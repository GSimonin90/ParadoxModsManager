import os
import sqlite3
import tkinter as tk
from tkinter import ttk, filedialog, messagebox, simpledialog
from collections import defaultdict
from dataclasses import dataclass, field
from typing import List, Dict, Optional, Set, Callable
import threading
import re
import json
import base64
import shutil
import datetime

# ==========================================
# ENGINE DATA STRUCTURES
# ==========================================
@dataclass
class ModInfo:
    name: str
    directory_path: str
    load_position: int
    dependencies: List[str] = field(default_factory=list)
    playset_id: str = ""
    mod_id: str = ""

# ==========================================
# CONFIGURATION MANAGER
# ==========================================
class AppConfig:
    """Handles saving and loading user preferences locally."""
    def __init__(self, config_file: str = "config.json"):
        self.config_file = config_file
        self.data = {
            "last_db_path": "",
            "last_game": ""
        }
        self.load()

    def load(self) -> None:
        if os.path.exists(self.config_file):
            try:
                with open(self.config_file, "r", encoding="utf-8") as f:
                    self.data.update(json.load(f))
            except Exception:
                pass

    def save(self) -> None:
        try:
            with open(self.config_file, "w", encoding="utf-8") as f:
                json.dump(self.data, f, indent=4)
        except Exception as e:
            print(f"[CONFIG ERROR] Failed to save settings: {e}")

# ==========================================
# CORE PARSERS AND SCANNERS
# ==========================================
class ParadoxGameDetector:
    def __init__(self):
        user_profile = os.environ.get("USERPROFILE", "")
        self.search_paths = [
            os.path.join(user_profile, "Documents", "Paradox Interactive"),
            os.path.join(user_profile, "Documents", "My Games")
        ]

    def find_installed_games(self) -> Dict[str, str]:
        installed_games: Dict[str, str] = {}
        for base_path in self.search_paths:
            if not os.path.exists(base_path):
                continue
            for item in os.listdir(base_path):
                game_folder_path = os.path.join(base_path, item)
                if os.path.isdir(game_folder_path):
                    expected_db_path = os.path.join(game_folder_path, "launcher-v2.sqlite")
                    if os.path.exists(expected_db_path):
                        if item not in installed_games:
                            installed_games[item] = expected_db_path
        return installed_games

class ParadoxLauncherParser:
    def __init__(self, db_path: str):
        self.db_path = db_path

    def create_backup(self) -> Optional[str]:
        if not os.path.exists(self.db_path):
            return None
        months = ["Jan", "Feb", "Mar", "Apr", "May", "Jun", "Jul", "Aug", "Sep", "Oct", "Nov", "Dec"]
        now = datetime.datetime.now()
        month_str = months[now.month - 1]
        
        timestamp = f"{now.day:02d}_{month_str}_{now.year}_{now.strftime('%H%M%S')}"
        backup_name = f"Backup_{timestamp}.sqlite"
        backup_path = os.path.join(os.path.dirname(self.db_path), backup_name)
        
        try:
            shutil.copy2(self.db_path, backup_path)
            return backup_path
        except Exception as e:
            print(f"[BACKUP ERROR] {e}")
            return None

    def restore_backup(self, backup_path: str) -> bool:
        if not os.path.exists(backup_path) or not os.path.exists(self.db_path):
            return False
        try:
            shutil.copy2(backup_path, self.db_path)
            return True
        except Exception:
            return False

    def _extract_dependencies(self, mod_dir: str) -> List[str]:
        descriptor_path = os.path.join(mod_dir, "descriptor.mod")
        deps = []
        if not os.path.exists(descriptor_path):
            return deps
        try:
            with open(descriptor_path, 'r', encoding='utf-8-sig', errors='ignore') as f:
                content = f.read()
                match = re.search(r'dependencies\s*=\s*\{\s*([^}]+)\}', content)
                if match:
                    inner_text = match.group(1)
                    deps = re.findall(r'"([^"]+)"', inner_text)
        except Exception:
            pass
        return deps

    def get_active_load_order(self) -> List[ModInfo]:
        if not os.path.exists(self.db_path):
            return []
        load_order: List[ModInfo] = []
        try:
            connection = sqlite3.connect(self.db_path)
            cursor = connection.cursor()
            query = """
                SELECT m.displayName, m.name, m.dirPath, pm.position, p.id, m.id
                FROM playsets p
                JOIN playsets_mods pm ON p.id = pm.playsetId
                JOIN mods m ON pm.modId = m.id
                WHERE p.isActive = 1 AND pm.enabled = 1
                ORDER BY pm.position ASC;
            """
            cursor.execute(query)
            for index, row in enumerate(cursor.fetchall(), start=1):
                display_name, internal_name, dir_path, _, playset_id, mod_id = row
                final_name = display_name if display_name else (internal_name if internal_name else f"Unknown_Mod_{index}")
                valid_path = dir_path if dir_path else ""
                dependencies = self._extract_dependencies(valid_path) if valid_path else []
                load_order.append(ModInfo(final_name, valid_path, index, dependencies, playset_id, mod_id))
            connection.close()
        except sqlite3.Error:
            return []
        return load_order

    def write_new_load_order(self, new_order: List[ModInfo]) -> bool:
        try:
            connection = sqlite3.connect(self.db_path)
            cursor = connection.cursor()
            for new_position, mod in enumerate(new_order, start=1):
                cursor.execute("""
                    UPDATE playsets_mods 
                    SET position = ? 
                    WHERE playsetId = ? AND modId = ?
                """, (str(new_position).zfill(10), mod.playset_id, mod.mod_id))
            connection.commit()
            connection.close()
            return True
        except sqlite3.Error:
            return False

    def disable_mods(self, mod_ids: List[str], playset_id: str) -> bool:
        if not mod_ids:
            return True
        try:
            connection = sqlite3.connect(self.db_path)
            cursor = connection.cursor()
            format_strings = ','.join(['?'] * len(mod_ids))
            cursor.execute(f"""
                UPDATE playsets_mods 
                SET enabled = 0 
                WHERE playsetId = ? AND modId IN ({format_strings})
            """, [playset_id] + mod_ids)
            connection.commit()
            connection.close()
            return True
        except sqlite3.Error:
            return False


class ModConflictDetector:
    def __init__(self, load_order: List[ModInfo], trusted_mods: Set[str]):
        self.load_order = load_order
        self.trusted_mods = trusted_mods
        self.file_registry: Dict[str, List[ModInfo]] = defaultdict(list)
        self.categorized_conflicts: Dict[str, List] = {"CRITICAL": [], "WARNING": [], "SAFE": []}
        self.dependency_errors: List[str] = []
        
        self.vram_impact_bytes: int = 0
        self.progress_callback: Optional[Callable[[int, int, str], None]] = None

    def _get_risk_level(self, rel_path: str) -> str:
        normalized_path = rel_path.replace('\\', '/').lower()
        if normalized_path.startswith('common/') or normalized_path.startswith('events/') or normalized_path.startswith('map/'):
            return "CRITICAL"
        elif normalized_path.startswith('gfx/') or normalized_path.startswith('music/') or normalized_path.startswith('sound/') or normalized_path.startswith('localization/'):
            return "SAFE"
        return "WARNING"

    def check_dependencies(self) -> None:
        loaded_mod_names = {mod.name: mod.load_position for mod in self.load_order}
        for mod in self.load_order:
            for dep in mod.dependencies:
                if dep in loaded_mod_names:
                    master_position = loaded_mod_names[dep]
                    if master_position > mod.load_position:
                        self.dependency_errors.append(f"[{mod.name}] Loaded BEFORE required master [{dep}]!")

    def scan_files(self) -> None:
        total_mods = len(self.load_order)
        for index, mod in enumerate(self.load_order, 1):
            if self.progress_callback:
                self.progress_callback(index, total_mods, f"Scanning Mod: {mod.name}")
            if not mod.directory_path or not os.path.exists(mod.directory_path):
                continue
            for root, _, files in os.walk(mod.directory_path):
                for file_name in files:
                    absolute_path = os.path.join(root, file_name)
                    relative_path = os.path.relpath(absolute_path, mod.directory_path)
                    normalized_path = relative_path.replace('\\', '/').lower()
                    
                    self.file_registry[relative_path].append(mod)
                    
                    if "gfx" in normalized_path or "models" in normalized_path or "textures" in normalized_path:
                        try:
                            self.vram_impact_bytes += os.path.getsize(absolute_path)
                        except OSError:
                            pass

    def detect_conflicts(self) -> None:
        if self.progress_callback:
            self.progress_callback(1, 1, "Categorizing Conflicts...")
        for file_path, mods in self.file_registry.items():
            if len(mods) > 1:
                risk = self._get_risk_level(file_path)
                
                if risk == "CRITICAL":
                    overriding_mods = mods[1:]
                    if all(m.name in self.trusted_mods for m in overriding_mods):
                        risk = "SAFE"
                        
                self.categorized_conflicts[risk].append((file_path, mods))

# ==========================================
# ADVANCED TOOLS ENGINE
# ==========================================
class AdvancedToolsEngine:
    @staticmethod
    def topological_sort_load_order(load_order: List[ModInfo]) -> List[ModInfo]:
        graph = defaultdict(list)
        in_degree = {mod.name: 0 for mod in load_order}
        mod_map = {mod.name: mod for mod in load_order}
        
        for mod in load_order:
            for dep in mod.dependencies:
                if dep in mod_map:
                    graph[dep].append(mod.name)
                    in_degree[mod.name] += 1
                    
        queue = [name for name in in_degree if in_degree[name] == 0]
        sorted_names = []
        
        while queue:
            current = queue.pop(0)
            sorted_names.append(current)
            for neighbor in graph[current]:
                in_degree[neighbor] -= 1
                if in_degree[neighbor] == 0:
                    queue.append(neighbor)
                    
        if len(sorted_names) != len(load_order):
            for name in mod_map:
                if name not in sorted_names:
                    sorted_names.append(name)
                    
        return [mod_map[name] for name in sorted_names]

    @staticmethod
    def generate_sync_code(load_order: List[ModInfo]) -> str:
        mod_names = [mod.name for mod in load_order]
        json_str = json.dumps({"order": mod_names})
        return base64.b64encode(json_str.encode('utf-8')).decode('utf-8')

    @staticmethod
    def parse_sync_code(code: str) -> List[str]:
        try:
            json_str = base64.b64decode(code.encode('utf-8')).decode('utf-8')
            data = json.loads(json_str)
            return data.get("order", [])
        except Exception:
            return []

    @staticmethod
    def generate_auto_patch(conflicts: Dict[str, List], base_game_db_path: str) -> str:
        mod_root_dir = os.path.join(os.path.dirname(base_game_db_path), "mod")
        patch_dir = os.path.join(mod_root_dir, "Z_Auto_Conflict_Patch")
        
        if not os.path.exists(patch_dir):
            os.makedirs(patch_dir)
            
        descriptor_path = os.path.join(patch_dir, "descriptor.mod")
        with open(descriptor_path, "w", encoding="utf-8") as f:
            f.write('version="1.0"\n')
            f.write('tags={\n\t"Utilities"\n}\n')
            f.write('name="Z Auto Conflict Patch"\n')
            f.write('supported_version="*"\n')

        merged_count = 0
        for file_path, mods in conflicts.get("CRITICAL", []):
            if not file_path.endswith('.txt'):
                continue
            target_file_path = os.path.join(patch_dir, file_path)
            os.makedirs(os.path.dirname(target_file_path), exist_ok=True)
            
            try:
                with open(target_file_path, "w", encoding="utf-8") as outfile:
                    for mod in mods:
                        source_file = os.path.join(mod.directory_path, file_path)
                        if os.path.exists(source_file):
                            outfile.write(f"\n# --- MERGED FROM: {mod.name} ---\n")
                            with open(source_file, "r", encoding="utf-8-sig", errors="ignore") as infile:
                                outfile.write(infile.read())
                            outfile.write("\n")
                merged_count += 1
            except Exception as e:
                pass
                
        return f"Successfully generated patch containing {merged_count} merged files at:\n{patch_dir}"

# ==========================================
# INTERACTIVE DIALOGS
# ==========================================
class SafeModeDialog(tk.Toplevel):
    def __init__(self, parent, overrider_mods: Dict[str, str], trusted_mods: Set[str], apply_callback):
        super().__init__(parent)
        self.title("Conflict Manager - Safe Mode")
        self.geometry("600x450")
        self.transient(parent)
        self.grab_set()

        self.apply_callback = apply_callback
        self.overrider_mods = overrider_mods
        self.trusted_mods = trusted_mods
        
        self.disable_vars: Dict[str, tk.BooleanVar] = {}
        self.trust_vars: Dict[str, tk.BooleanVar] = {}

        style = ttk.Style()
        self.theme_bg = style.lookup("TFrame", "background")
        self.configure(background=self.theme_bg)

        self._build_ui()

    def _build_ui(self) -> None:
        header = ttk.Label(self, text="The following sub-mods are overriding CRITICAL base files.\nChoose whether to disable them for safety or trust them permanently.", padding=10)
        header.pack(fill="x")

        canvas = tk.Canvas(self, borderwidth=0, highlightthickness=0, background=self.theme_bg)
        scrollbar = ttk.Scrollbar(self, orient="vertical", command=canvas.yview)
        scrollable_frame = ttk.Frame(canvas)

        scrollable_frame.bind("<Configure>", lambda e: canvas.configure(scrollregion=canvas.bbox("all")))
        canvas.create_window((0, 0), window=scrollable_frame, anchor="nw")
        canvas.configure(yscrollcommand=scrollbar.set)

        canvas.pack(side="top", fill="both", expand=True, padx=10)
        scrollbar.pack(side="right", fill="y")

        for mod_name in self.overrider_mods.keys():
            row_frame = ttk.Frame(scrollable_frame, padding=5)
            row_frame.pack(fill="x", expand=True)
            
            dis_var = tk.BooleanVar(value=False)
            trust_var = tk.BooleanVar(value=(mod_name in self.trusted_mods))
            
            self.disable_vars[mod_name] = dis_var
            self.trust_vars[mod_name] = trust_var
            
            def on_trust_toggle(d_var=dis_var, t_var=trust_var):
                if t_var.get(): d_var.set(False)
            
            def on_disable_toggle(d_var=dis_var, t_var=trust_var):
                if d_var.get(): t_var.set(False)

            cb_disable = ttk.Checkbutton(row_frame, text="Disable", variable=dis_var, command=on_disable_toggle)
            cb_disable.pack(side="left", padx=10)
            
            cb_trust = ttk.Checkbutton(row_frame, text="Trust (Whitelist)", variable=trust_var, command=on_trust_toggle)
            cb_trust.pack(side="left", padx=10)
            
            ttk.Label(row_frame, text=mod_name, font=("Helvetica", 9, "bold")).pack(side="left", padx=10)
            ttk.Separator(scrollable_frame, orient="horizontal").pack(fill="x")

        btn_frame = ttk.Frame(self, padding=10)
        btn_frame.pack(fill="x", side="bottom")
        
        apply_btn = ttk.Button(btn_frame, text="Apply Changes", command=self._on_apply)
        apply_btn.pack(side="right", padx=5)
        
        cancel_btn = ttk.Button(btn_frame, text="Cancel", command=self.destroy)
        cancel_btn.pack(side="right", padx=5)

    def _on_apply(self) -> None:
        mods_to_disable = []
        new_trusted_list = set(self.trusted_mods)

        for mod_name, mod_id in self.overrider_mods.items():
            if self.disable_vars[mod_name].get():
                mods_to_disable.append(mod_id)
                if mod_name in new_trusted_list:
                    new_trusted_list.remove(mod_name)
                    
            if self.trust_vars[mod_name].get():
                new_trusted_list.add(mod_name)
            elif not self.trust_vars[mod_name].get() and mod_name in new_trusted_list:
                new_trusted_list.remove(mod_name)

        self.apply_callback(mods_to_disable, new_trusted_list)
        self.destroy()

class WhitelistManagerDialog(tk.Toplevel):
    def __init__(self, parent, trusted_mods: Set[str], apply_callback):
        super().__init__(parent)
        self.title("Manage Whitelist")
        self.geometry("400x400")
        self.transient(parent)
        self.grab_set()

        self.trusted_mods = trusted_mods
        self.apply_callback = apply_callback
        self.remove_vars: Dict[str, tk.BooleanVar] = {}

        style = ttk.Style()
        self.theme_bg = style.lookup("TFrame", "background")
        self.configure(background=self.theme_bg)

        self._build_ui()

    def _build_ui(self) -> None:
        header = ttk.Label(self, text="Select mods to REMOVE from the Whitelist:", padding=10)
        header.pack(fill="x")

        canvas = tk.Canvas(self, borderwidth=0, highlightthickness=0, background=self.theme_bg)
        scrollbar = ttk.Scrollbar(self, orient="vertical", command=canvas.yview)
        scrollable_frame = ttk.Frame(canvas)

        scrollable_frame.bind("<Configure>", lambda e: canvas.configure(scrollregion=canvas.bbox("all")))
        canvas.create_window((0, 0), window=scrollable_frame, anchor="nw")
        canvas.configure(yscrollcommand=scrollbar.set)

        canvas.pack(side="top", fill="both", expand=True, padx=10)
        scrollbar.pack(side="right", fill="y")

        if not self.trusted_mods:
            ttk.Label(scrollable_frame, text="Your whitelist is currently empty.", padding=10).pack()
        else:
            for mod_name in sorted(self.trusted_mods):
                row_frame = ttk.Frame(scrollable_frame, padding=5)
                row_frame.pack(fill="x", expand=True)
                
                var = tk.BooleanVar(value=False)
                self.remove_vars[mod_name] = var
                
                cb = ttk.Checkbutton(row_frame, text="Remove", variable=var)
                cb.pack(side="left", padx=10)
                
                ttk.Label(row_frame, text=mod_name).pack(side="left", padx=10)
                ttk.Separator(scrollable_frame, orient="horizontal").pack(fill="x")

        btn_frame = ttk.Frame(self, padding=10)
        btn_frame.pack(fill="x", side="bottom")
        
        apply_btn = ttk.Button(btn_frame, text="Apply Changes", command=self._on_apply)
        apply_btn.pack(side="right", padx=5)
        
        cancel_btn = ttk.Button(btn_frame, text="Cancel", command=self.destroy)
        cancel_btn.pack(side="right", padx=5)

    def _on_apply(self) -> None:
        new_trusted_list = set(self.trusted_mods)
        for mod_name, var in self.remove_vars.items():
            if var.get() and mod_name in new_trusted_list:
                new_trusted_list.remove(mod_name)

        self.apply_callback(new_trusted_list)
        self.destroy()

# ==========================================
# DESKTOP GUI APPLICATION
# ==========================================
class ModManagerApp:
    def __init__(self, window: tk.Tk):
        self.window = window
        self.window.title("Paradox Mod Manager v6.0 - Master Edition")
        self.window.geometry("1050x850")
        self.window.minsize(950, 700)

        try:
            self.window.iconbitmap("icon.ico")
        except Exception:
            pass 

        self.config = AppConfig()
        self.whitelist_file = "whitelist.json"
        self.trusted_mods: Set[str] = self._load_whitelist()

        self.game_detector = ParadoxGameDetector()
        self.installed_games = self.game_detector.find_installed_games()
        self.latest_report_data = ""
        self.current_load_order: List[ModInfo] = []
        self.current_conflicts: Dict[str, List] = {}
        
        self._build_menu()
        self._build_ui()

    def _load_whitelist(self) -> Set[str]:
        if os.path.exists(self.whitelist_file):
            try:
                with open(self.whitelist_file, "r", encoding="utf-8") as f:
                    data = json.load(f)
                    return set(data.get("trusted_mods", []))
            except Exception:
                pass
        return set()

    def _save_whitelist(self) -> None:
        try:
            with open(self.whitelist_file, "w", encoding="utf-8") as f:
                json.dump({"trusted_mods": list(self.trusted_mods)}, f, indent=4)
        except Exception as e:
            print(f"Failed to save whitelist: {e}")

    def _build_menu(self) -> None:
        menubar = tk.Menu(self.window)
        
        help_menu = tk.Menu(menubar, tearoff=0)
        help_menu.add_command(label="How to use Advanced Tools", command=self._show_help)
        help_menu.add_separator()
        help_menu.add_command(label="About", command=self._show_about)
        
        menubar.add_cascade(label="Help", menu=help_menu)
        self.window.config(menu=menubar)

    def _show_help(self) -> None:
        help_text = (
            "--- ADVANCED TOOLS GUIDE ---\n\n"
            "✨ Auto-Sort: Automatically arranges your load order based on Master/Submod dependencies. "
            "It creates a backup before making any database changes.\n\n"
            "🛠️ Auto-Patch: Generates a new local mod folder called 'Z Auto Conflict Patch'. "
            "It attempts to safely merge colliding script files so you don't lose mod features.\n\n"
            "📤 Export / 📥 Import Sync: Copies your exact load order to the clipboard. "
            "Share this string with your friends to instantly sync your load orders for multiplayer.\n\n"
            "🛡️ Safe Mode: Lists all sub-mods currently overwriting critical game logic. "
            "You can disable them to stabilize your game, or 'Trust' them if the overwrite is intended (e.g. translation mods)."
        )
        messagebox.showinfo("Help & Instructions", help_text)

    def _show_about(self) -> None:
        about_text = "Paradox Mod Manager v6.0\nMaster Edition\n\nA powerful, lightweight utility designed to resolve complex modding conflicts without requiring heavy dependencies."
        messagebox.showinfo("About", about_text)

    def _build_ui(self) -> None:
        top_frame = ttk.LabelFrame(self.window, text=" Profile Target ", padding=10)
        top_frame.pack(fill="x", padx=15, pady=5)

        ttk.Label(top_frame, text="Detected Games:").pack(side="left", padx=5)
        self.game_combo = ttk.Combobox(top_frame, state="readonly", width=25)
        self.game_combo.pack(side="left", padx=5)
        
        if self.installed_games:
            self.game_combo['values'] = list(self.installed_games.keys())
            last_game = self.config.data.get("last_game")
            if last_game and last_game in self.installed_games:
                self.game_combo.set(last_game)
            else:
                self.game_combo.current(0)
        
        self.game_combo.bind("<<ComboboxSelected>>", self._on_game_select)

        ttk.Label(top_frame, text="DB Path:").pack(side="left", padx=(15, 5))
        self.db_path_entry = ttk.Entry(top_frame)
        self.db_path_entry.pack(side="left", fill="x", expand=True, padx=5)
        
        browse_btn = ttk.Button(top_frame, text="Browse...", command=self._browse_file)
        browse_btn.pack(side="left", padx=5)
        
        saved_db_path = self.config.data.get("last_db_path")
        if saved_db_path and os.path.exists(saved_db_path):
             self.db_path_entry.insert(0, saved_db_path)
        else:
            self._on_game_select(None)

        tools_frame = ttk.LabelFrame(self.window, text=" Advanced Actions & Safety ", padding=10)
        tools_frame.pack(fill="x", padx=15, pady=5)
        
        tools_top = ttk.Frame(tools_frame)
        tools_top.pack(fill="x", pady=2)
        sort_btn = ttk.Button(tools_top, text="✨ Auto-Sort", command=self._trigger_auto_sort)
        sort_btn.pack(side="left", padx=5)
        patch_btn = ttk.Button(tools_top, text="🛠️ Auto-Patch", command=self._trigger_auto_patch)
        patch_btn.pack(side="left", padx=5)
        sync_export_btn = ttk.Button(tools_top, text="📤 Export Sync", command=self._export_sync_code)
        sync_export_btn.pack(side="left", padx=5)
        sync_import_btn = ttk.Button(tools_top, text="📥 Import Sync", command=self._import_sync_code)
        sync_import_btn.pack(side="left", padx=5)
        
        tools_bot = ttk.Frame(tools_frame)
        tools_bot.pack(fill="x", pady=2)
        backup_btn = ttk.Button(tools_bot, text="💾 Backup DB", command=self._trigger_backup)
        backup_btn.pack(side="left", padx=5)
        restore_btn = ttk.Button(tools_bot, text="↩️ Restore DB", command=self._trigger_restore)
        restore_btn.pack(side="left", padx=5)
        ttk.Separator(tools_bot, orient='vertical').pack(side='left', fill='y', padx=10)
        isolate_btn = ttk.Button(tools_bot, text="🛡️ Interactive Safe Mode", command=self._open_safe_mode_dialog)
        isolate_btn.pack(side="left", padx=5)
        whitelist_btn = ttk.Button(tools_bot, text="📋 Manage Whitelist", command=self._open_whitelist_manager)
        whitelist_btn.pack(side="left", padx=5)

        control_frame = ttk.Frame(self.window, padding=5)
        control_frame.pack(fill="x", padx=15, pady=5)

        self.scan_btn = ttk.Button(control_frame, text="Run Full Analysis", command=self._start_scan_thread)
        self.scan_btn.pack(side="left", padx=5)
        self.export_btn = ttk.Button(control_frame, text="Export Log", command=self._export_log, state="disabled")
        self.export_btn.pack(side="left", padx=5)
        
        self.status_label = ttk.Label(control_frame, text="Idle", foreground="gray")
        self.status_label.pack(side="left", padx=15)
        self.progress_bar = ttk.Progressbar(control_frame, mode='determinate')
        self.progress_bar.pack(side="right", fill="x", expand=True, padx=5)

        notebook_frame = ttk.Frame(self.window, padding=10)
        notebook_frame.pack(fill="both", expand=True, padx=5, pady=5)
        self.notebook = ttk.Notebook(notebook_frame)
        self.notebook.pack(fill="both", expand=True)

        self.text_widgets: Dict[str, tk.Text] = {}
        tabs_setup = [
            ("Dashboard", "dashboard"),
            ("CRITICAL Overwrites", "critical"),
            ("WARNING Overwrites", "warning"),
            ("SAFE / Whitelisted", "safe")
        ]

        for title, key in tabs_setup:
            frame = ttk.Frame(self.notebook)
            self.notebook.add(frame, text=title)
            text_widget = tk.Text(frame, wrap="word", state="disabled", background="#1e1e1e", foreground="#ffffff", font=("Consolas", 10))
            scrollbar = ttk.Scrollbar(frame, command=text_widget.yview)
            text_widget.config(yscrollcommand=scrollbar.set)
            text_widget.pack(side="left", fill="both", expand=True)
            scrollbar.pack(side="right", fill="y")
            self.text_widgets[key] = text_widget

    def _on_game_select(self, event) -> None:
        selected_game = self.game_combo.get()
        if selected_game in self.installed_games:
            new_path = self.installed_games[selected_game]
            self.db_path_entry.delete(0, tk.END)
            self.db_path_entry.insert(0, new_path)
            
            self.config.data["last_game"] = selected_game
            self.config.data["last_db_path"] = new_path
            self.config.save()

    def _browse_file(self) -> None:
        selected_file = filedialog.askopenfilename(
            title="Select launcher-v2.sqlite",
            filetypes=[("SQLite Database", "*.sqlite"), ("All Files", "*.*")]
        )
        if selected_file:
            self.db_path_entry.delete(0, tk.END)
            self.db_path_entry.insert(0, selected_file)
            
            self.config.data["last_db_path"] = selected_file
            self.config.save()

    def _update_progress(self, current: int, total: int, message: str) -> None:
        def task():
            self.progress_bar['maximum'] = total
            self.progress_bar['value'] = current
            self.status_label.config(text=message)
        self.window.after(0, task)

    def _write_to_tab(self, tab_key: str, content: str) -> None:
        widget = self.text_widgets[tab_key]
        def task():
            widget.config(state="normal")
            widget.delete("1.0", tk.END)
            widget.insert(tk.END, content)
            widget.config(state="disabled")
        self.window.after(0, task)

    def _start_scan_thread(self) -> None:
        db_path = self.db_path_entry.get().strip()
        if not os.path.exists(db_path):
            messagebox.showerror("Error", f"Database not found at:\n{db_path}")
            return

        self.scan_btn.config(state="disabled", text="Scanning...")
        self.export_btn.config(state="disabled")
        self.progress_bar['value'] = 0
        for key in self.text_widgets:
            self._write_to_tab(key, "Running Analysis...\n")
            
        threading.Thread(target=self._run_engine_pipeline, args=(db_path,), daemon=True).start()

    def _run_engine_pipeline(self, db_path: str) -> None:
        self._update_progress(0, 100, "Extracting Load Order from DB...")
        parser = ParadoxLauncherParser(db_path)
        self.current_load_order = parser.get_active_load_order()

        if not self.current_load_order:
            self._update_progress(100, 100, "Error: No active mods found.")
            self._write_to_tab("dashboard", "ERROR: Database empty or locked.")
            self.window.after(0, self._finalize_scan)
            return

        detector = ModConflictDetector(self.current_load_order, self.trusted_mods)
        detector.progress_callback = self._update_progress
        detector.check_dependencies()
        detector.scan_files()
        detector.detect_conflicts()
        
        self.current_conflicts = detector.categorized_conflicts
        self._distribute_reports(detector)
        self._update_progress(100, 100, "Finalizing Reports...")
        self.window.after(0, self._finalize_scan)

    def _distribute_reports(self, detector: ModConflictDetector) -> None:
        dash_lines = ["====================================================="]
        dash_lines.append("                  ANALYSIS DASHBOARD                 ")
        dash_lines.append("=====================================================\n")
        dash_lines.append(f"Total Active Mods: {len(detector.load_order)}")
        
        vram_mb = detector.vram_impact_bytes / (1024 * 1024)
        dash_lines.append(f"Estimated Asset Impact (VRAM): {vram_mb:.2f} MB\n")
        
        crit_count = len(detector.categorized_conflicts["CRITICAL"])
        warn_count = len(detector.categorized_conflicts["WARNING"])
        safe_count = len(detector.categorized_conflicts["SAFE"])
        
        dash_lines.append(f"Critical Overwrites: {crit_count}")
        dash_lines.append(f"Warning Overwrites:  {warn_count}")
        dash_lines.append(f"Safe / Whitelisted:  {safe_count}\n")

        if detector.dependency_errors:
            dash_lines.append("[!!!] LOAD ORDER DEPENDENCY ERRORS DETECTED:")
            for err in detector.dependency_errors:
                dash_lines.append(f"  -> {err}")
        else:
            dash_lines.append("[SUCCESS] No Master/Submod dependency errors found.")
            
        dash_lines.append("\n\n--- CURRENT LOAD ORDER OVERVIEW ---")
        for mod in detector.load_order:
            deps_str = f" [Requires: {', '.join(mod.dependencies)}]" if mod.dependencies else ""
            dash_lines.append(f"[{str(mod.load_position).zfill(2)}] {mod.name}{deps_str}")
            
        self._write_to_tab("dashboard", "\n".join(dash_lines))

        for risk, tab_key in [("CRITICAL", "critical"), ("WARNING", "warning"), ("SAFE", "safe")]:
            conflicts = detector.categorized_conflicts[risk]
            lines = []
            for file_path, mods in conflicts:
                lines.append(f"FILE: {file_path}")
                for m in mods:
                    tag = " [TRUSTED]" if m.name in self.trusted_mods else ""
                    lines.append(f"  [{str(m.load_position).zfill(2)}] {m.name}{tag}")
                lines.append(f"  WINNER: {mods[-1].name}\n" + "-" * 65)
            self._write_to_tab(tab_key, "\n".join(lines) if lines else f"No {risk} level overwrites detected.")
            
        export_lines = dash_lines.copy()
        for risk in ["CRITICAL", "WARNING", "SAFE"]:
            export_lines.append(f"\n\n>>> {risk} OVERWRITES <<<\n")
            export_lines.append(self.text_widgets[risk.lower()].get("1.0", tk.END).strip())
        self.latest_report_data = "\n".join(export_lines)

    def _finalize_scan(self) -> None:
        self.scan_btn.config(state="normal", text="Run Full Analysis")
        self.export_btn.config(state="normal")
        self.status_label.config(text="Scan Complete.")

    def _export_log(self) -> None:
        if not self.latest_report_data: return
        file_path = filedialog.asksaveasfilename(
            defaultextension=".txt",
            filetypes=[("Text Document", "*.txt"), ("All Files", "*.*")]
        )
        if file_path:
            with open(file_path, "w", encoding="utf-8") as f:
                f.write(self.latest_report_data)
            messagebox.showinfo("Success", "Log exported successfully.")

    # --- Safety & Isolation Features ---
    def _trigger_backup(self) -> None:
        parser = ParadoxLauncherParser(self.db_path_entry.get().strip())
        backup_path = parser.create_backup()
        if backup_path:
            messagebox.showinfo("Backup Created", f"Safety backup successfully created:\n{backup_path}")
        else:
            messagebox.showerror("Error", "Failed to create database backup.")

    def _trigger_restore(self) -> None:
        db_dir = os.path.dirname(self.db_path_entry.get().strip())
        selected_file = filedialog.askopenfilename(
            initialdir=db_dir,
            title="Select Backup to Restore",
            filetypes=[("SQLite Backup", "Backup_*.sqlite"), ("All Files", "*.*")]
        )
        if not selected_file:
            return
        if messagebox.askyesno("Confirm Restore", "Are you sure you want to overwrite your current load order with this backup?"):
            parser = ParadoxLauncherParser(self.db_path_entry.get().strip())
            if parser.restore_backup(selected_file):
                messagebox.showinfo("Success", "Database restored successfully. Please restart the launcher.")
                self._start_scan_thread()
            else:
                messagebox.showerror("Error", "Failed to restore database.")

    def _open_safe_mode_dialog(self) -> None:
        if not self.current_conflicts or not self.current_load_order:
            messagebox.showwarning("Warning", "Please run a scan first to detect conflicts.")
            return

        criticals = self.current_conflicts.get("CRITICAL", [])
        overriders_map = {}
        for file_path, mods in criticals:
            for m in mods[1:]:
                overriders_map[m.name] = m.mod_id

        if not overriders_map:
            messagebox.showinfo("Safe Mode", "No sub-mods overriding critical files found.")
            return

        SafeModeDialog(self.window, overriders_map, self.trusted_mods, self._apply_safe_mode_changes)

    def _apply_safe_mode_changes(self, mods_to_disable: List[str], new_trusted_list: Set[str]) -> None:
        self.trusted_mods = new_trusted_list
        self._save_whitelist()
        
        if mods_to_disable:
            parser = ParadoxLauncherParser(self.db_path_entry.get().strip())
            parser.create_backup()
            playset_id = self.current_load_order[0].playset_id
            if parser.disable_mods(mods_to_disable, playset_id):
                messagebox.showinfo("Success", f"Disabled {len(mods_to_disable)} mods.\nWhitelist updated.\nRestart your Paradox Launcher.")
            else:
                messagebox.showerror("Error", "Failed to disable mods in database.")
                return

        self._start_scan_thread()

    def _open_whitelist_manager(self) -> None:
        WhitelistManagerDialog(self.window, self.trusted_mods, self._apply_whitelist_removal)

    def _apply_whitelist_removal(self, new_trusted_list: Set[str]) -> None:
        self.trusted_mods = new_trusted_list
        self._save_whitelist()
        messagebox.showinfo("Success", "Whitelist updated successfully.")
        self._start_scan_thread()

    # --- Advanced Features Triggers ---
    def _trigger_auto_sort(self) -> None:
        if not self.current_load_order: return
        parser = ParadoxLauncherParser(self.db_path_entry.get().strip())
        parser.create_backup()
        new_order = AdvancedToolsEngine.topological_sort_load_order(self.current_load_order)
        if parser.write_new_load_order(new_order):
            messagebox.showinfo("Success", "Load Order successfully auto-sorted.\nPlease restart the Paradox Launcher.")
            self._start_scan_thread()

    def _trigger_auto_patch(self) -> None:
        if not self.current_conflicts: return
        result_msg = AdvancedToolsEngine.generate_auto_patch(self.current_conflicts, self.db_path_entry.get().strip())
        messagebox.showinfo("Auto-Merger Complete", f"{result_msg}\n\nDon't forget to enable the new 'Z Auto Conflict Patch' mod in your launcher!")

    def _export_sync_code(self) -> None:
        if not self.current_load_order: return
        code = AdvancedToolsEngine.generate_sync_code(self.current_load_order)
        self.window.clipboard_clear()
        self.window.clipboard_append(code)
        messagebox.showinfo("Code Exported", "Sync Code has been copied to your clipboard!")

    def _import_sync_code(self) -> None:
        code = simpledialog.askstring("Import Sync Code", "Paste the Sync Code received from your friend:")
        if not code: return
            
        target_names = AdvancedToolsEngine.parse_sync_code(code)
        if not target_names:
            messagebox.showerror("Error", "Invalid or corrupted Sync Code.")
            return
            
        parser = ParadoxLauncherParser(self.db_path_entry.get().strip())
        parser.create_backup()
        current_mods = parser.get_active_load_order()
        mod_dict = {m.name: m for m in current_mods}
        new_order = []
        for name in target_names:
            if name in mod_dict:
                new_order.append(mod_dict[name])
        for m in current_mods:
            if m.name not in target_names:
                new_order.append(m)
                
        if parser.write_new_load_order(new_order):
            messagebox.showinfo("Success", "Load order synchronized successfully! Restart your launcher.")
            self._start_scan_thread()

# ==========================================
# MAIN ENTRY POINT
# ==========================================
if __name__ == "__main__":
    root = tk.Tk()
    style = ttk.Style()
    style.theme_use("clam")
    app = ModManagerApp(root)
    root.mainloop()