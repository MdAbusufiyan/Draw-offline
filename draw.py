"""A small, chemistry-aware 2D molecule editor built with Tkinter.

Optional chemistry backend:
    python -m pip install rdkit

Without RDKit, drawing and basic formula/MW estimates still work. Valence,
SMILES and aromaticity checks are deliberately marked as limited rather than
presented as authoritative chemistry.
"""

import math
import tkinter as tk
from tkinter import ttk, messagebox
from collections import defaultdict, deque

try:
    from rdkit import Chem
    from rdkit.Chem import Descriptors, rdMolDescriptors
    RDKIT_AVAILABLE = True
except ImportError:
    Chem = None
    Descriptors = None
    rdMolDescriptors = None
    RDKIT_AVAILABLE = False


ATOMIC_WEIGHTS = {
    "H": 1.008, "C": 12.011, "N": 14.007, "O": 15.999,
    "F": 18.998, "P": 30.974, "S": 32.06, "Cl": 35.45,
    "Br": 79.904, "I": 126.904,
}

# Simple fallback valences only. RDKit is used when available.
COMMON_VALENCES = {
    "C": (4,), "N": (3, 5), "O": (2,), "S": (2, 4, 6),
    "P": (3, 5), "F": (1,), "Cl": (1, 3, 5, 7),
    "Br": (1, 3, 5, 7), "I": (1, 3, 5, 7), "H": (1,),
}

HALOGENS = {"F", "Cl", "Br", "I"}
SUBSCRIPTS = str.maketrans("0123456789", "₀₁₂₃₄₅₆₇₈₉")


class Atom:
    def __init__(self, x, y, element="C", charge=0):
        self.x = float(x)
        self.y = float(y)
        self.element = element
        self.charge = int(charge)
        self.bonds = []
        self.canvas_id = None
        self.text_id = None
        self.implicit_h = 0
        self.is_valid = True
        self.smiles_index = -1

    def distance_to(self, x, y):
        return math.hypot(self.x - x, self.y - y)

    def get_bond_order_sum(self):
        return sum(b.order for b in self.bonds)

    def fallback_implicit_h(self):
        """Conservative estimate used only when RDKit cannot analyze the graph."""
        # A drawn hydrogen is an explicit atom; it never receives implicit H.
        if self.element == "H":
            self.implicit_h = 0
            return 0
        if self.element not in COMMON_VALENCES:
            self.implicit_h = 0
            return 0

        bond_sum = self.get_bond_order_sum()
        charge = self.charge

        # Common charge-dependent valence targets for the common organic atoms.
        if self.element == "N" and charge == 1:
            targets = (4,)
        elif self.element == "N" and charge == -1:
            targets = (2,)
        elif self.element == "O" and charge == 1:
            targets = (3,)
        elif self.element == "O" and charge == -1:
            targets = (1,)
        elif self.element == "C" and charge != 0:
            targets = (4,)
        else:
            targets = COMMON_VALENCES[self.element]

        possible = [v for v in targets if v >= bond_sum]
        target = min(possible) if possible else max(targets)
        self.implicit_h = max(0, int(round(target - bond_sum)))
        return self.implicit_h

    def fallback_validate_valence(self):
        if self.element not in COMMON_VALENCES:
            self.is_valid = True
            return True

        bond_sum = self.get_bond_order_sum()
        charge = self.charge
        if self.element == "N" and charge == 1:
            targets = (4,)
        elif self.element == "N" and charge == -1:
            targets = (2,)
        elif self.element == "O" and charge == 1:
            targets = (3,)
        elif self.element == "O" and charge == -1:
            targets = (1,)
        else:
            targets = COMMON_VALENCES[self.element]

        total = bond_sum + self.implicit_h
        # In fallback mode this is only a rough check, not a full electronic model.
        self.is_valid = any(total == target for target in targets)
        return self.is_valid


class Bond:
    def __init__(self, atom1, atom2, order=1):
        self.atom1 = atom1
        self.atom2 = atom2
        self.order = int(order)
        self.canvas_ids = []
        self.is_aromatic = False
        atom1.bonds.append(self)
        atom2.bonds.append(self)


class MoleculeEditor:
    def __init__(self, root):
        self.root = root
        self.root.title("Molecule Editor")
        self.root.minsize(900, 620)

        self.atoms = []
        self.bonds = []
        self.undo_stack = []
        self.redo_stack = []
        self.max_undo = 100

        self.selected_element = tk.StringVar(value="C")
        self.bond_order = tk.IntVar(value=1)
        self.tool = tk.StringVar(value="draw")
        self.charge_value = tk.IntVar(value=0)

        self.selected_atoms = set()
        self.selected_bond = None
        self.pending_bond_atom = None
        self.drag_start_atom = None
        self.temp_line = None
        self.drag_moved = False
        self.move_component = []
        self.move_last = None
        self.move_before_state = None
        self.move_undo_saved = False
        self.last_canvas_pos = (450, 340)

        self.ATOM_RADIUS = 15
        self.DEFAULT_BOND_LENGTH = 42
        self.SNAP_ANGLES = tuple(range(0, 360, 30))
        self._rdkit_mol = None
        self._rdkit_error = None
        self._rdkit_sanitized = False
        self._fallback_mode = not RDKIT_AVAILABLE

        self._setup_ui()
        self._bind_events()
        self._update_info_panel()

    # ------------------------------------------------------------------ UI
    def _setup_ui(self):
        toolbar = tk.Frame(self.root, relief=tk.RAISED, borderwidth=1, padx=4, pady=3)
        toolbar.pack(side=tk.TOP, fill=tk.X)

        tk.Label(toolbar, text="Element").pack(side=tk.LEFT, padx=(3, 2))
        elements = ["C", "N", "O", "S", "P", "F", "Cl", "Br", "I", "H"]
        ttk.Combobox(toolbar, textvariable=self.selected_element, values=elements,
                     width=4, state="readonly").pack(side=tk.LEFT, padx=3)

        tk.Label(toolbar, text="Bond").pack(side=tk.LEFT, padx=(8, 2))
        for order, label in ((1, "Single"), (2, "Double"), (3, "Triple")):
            tk.Radiobutton(toolbar, text=label, variable=self.bond_order,
                           value=order, takefocus=False).pack(side=tk.LEFT)

        ttk.Separator(toolbar, orient=tk.VERTICAL).pack(side=tk.LEFT, fill=tk.Y, padx=6)
        tk.Label(toolbar, text="Tool").pack(side=tk.LEFT, padx=(0, 2))
        for tool, label in (("draw", "Draw"), ("select", "Select"),
                            ("move", "Move fragment"), ("erase", "Erase")):
            tk.Radiobutton(toolbar, text=label, variable=self.tool, value=tool,
                           takefocus=False).pack(side=tk.LEFT, padx=1)

        tk.Button(toolbar, text="Undo", command=self.undo).pack(side=tk.LEFT, padx=(8, 2))
        tk.Button(toolbar, text="Redo", command=self.redo).pack(side=tk.LEFT, padx=2)
        tk.Button(toolbar, text="Clear", command=self.clear_all).pack(side=tk.LEFT, padx=(4, 2))

        templates = tk.Frame(self.root, relief=tk.RAISED, borderwidth=1, padx=4, pady=3)
        templates.pack(side=tk.TOP, fill=tk.X)
        tk.Label(templates, text="Rings").pack(side=tk.LEFT, padx=(3, 4))
        tk.Button(templates, text="Benzene", command=self.add_benzene).pack(side=tk.LEFT, padx=2)
        tk.Button(templates, text="Cyclohexane", command=self.add_cyclohexane).pack(side=tk.LEFT, padx=2)
        tk.Button(templates, text="Cyclopentane", command=self.add_cyclopentane).pack(side=tk.LEFT, padx=2)

        ttk.Separator(templates, orient=tk.VERTICAL).pack(side=tk.LEFT, fill=tk.Y, padx=7)
        tk.Label(templates, text="Groups").pack(side=tk.LEFT, padx=(0, 4))
        tk.Button(templates, text="CH₃", command=lambda: self.add_functional_group("CH3")).pack(side=tk.LEFT, padx=2)
        tk.Button(templates, text="OH", command=lambda: self.add_functional_group("OH")).pack(side=tk.LEFT, padx=2)
        tk.Button(templates, text="NH₂", command=lambda: self.add_functional_group("NH2")).pack(side=tk.LEFT, padx=2)
        tk.Button(templates, text="COOH", command=lambda: self.add_functional_group("COOH")).pack(side=tk.LEFT, padx=2)

        ttk.Separator(templates, orient=tk.VERTICAL).pack(side=tk.LEFT, fill=tk.Y, padx=7)
        tk.Label(templates, text="Charge").pack(side=tk.LEFT, padx=(0, 2))
        tk.Spinbox(templates, from_=-3, to=3, width=3, textvariable=self.charge_value).pack(side=tk.LEFT)
        tk.Button(templates, text="Apply to selection", command=self.apply_charge).pack(side=tk.LEFT, padx=3)

        main = tk.Frame(self.root)
        main.pack(expand=True, fill=tk.BOTH)
        self.canvas = tk.Canvas(main, bg="white", width=900, height=650,
                                cursor="crosshair", highlightthickness=0)
        self.canvas.pack(side=tk.LEFT, expand=True, fill=tk.BOTH)

        panel = tk.Frame(main, width=235, relief=tk.SUNKEN, borderwidth=1, padx=9, pady=8)
        panel.pack(side=tk.RIGHT, fill=tk.Y)
        panel.pack_propagate(False)
        tk.Label(panel, text="MOLECULE", font=("Arial", 11, "bold")).pack(anchor="w", pady=(2, 9))

        self.formula_label = tk.Label(panel, text="Formula: —", anchor="w", justify=tk.LEFT)
        self.formula_label.pack(fill=tk.X, pady=3)
        self.weight_label = tk.Label(panel, text="MW: —", anchor="w", justify=tk.LEFT)
        self.weight_label.pack(fill=tk.X, pady=3)
        self.atom_count_label = tk.Label(panel, text="Atoms: 0", anchor="w")
        self.atom_count_label.pack(fill=tk.X, pady=3)
        self.bond_count_label = tk.Label(panel, text="Bonds: 0", anchor="w")
        self.bond_count_label.pack(fill=tk.X, pady=3)
        self.smiles_label = tk.Label(panel, text="SMILES: —", anchor="w", justify=tk.LEFT,
                                     wraplength=210)
        self.smiles_label.pack(fill=tk.X, pady=(8, 5))
        self.validation_label = tk.Label(panel, text="Empty molecule", anchor="w",
                                         justify=tk.LEFT, wraplength=210, fg="#555555")
        self.validation_label.pack(fill=tk.X, pady=5)

        ttk.Separator(panel, orient=tk.HORIZONTAL).pack(fill=tk.X, pady=9)
        tk.Label(panel, text="SHORTCUTS", font=("Arial", 9, "bold")).pack(anchor="w")
        shortcut_text = (
            "Click an atom, then click another atom or empty space to extend.\n"
            "Drag atom → atom/space also creates a bond.\n"
            "Esc: cancel pending bond / selection\n"
            "Ctrl+Z / Ctrl+Y: undo / redo\n"
            "Ctrl+C / Ctrl+V: copy / paste fragment\n"
            "Delete: delete selected atom(s) or bond\n"
            "1 / 2 / 3: choose bond order"
        )
        tk.Label(panel, text=shortcut_text, anchor="w", justify=tk.LEFT,
                 wraplength=210, font=("Arial", 8)).pack(anchor="w", pady=(5, 8))

        self.status_label = tk.Label(self.root, text=self._backend_status(), anchor="w",
                                     relief=tk.SUNKEN, padx=6, pady=3, fg="#555555")
        self.status_label.pack(side=tk.BOTTOM, fill=tk.X)

    def _backend_status(self):
        if RDKIT_AVAILABLE:
            return "Chemistry engine: RDKit enabled. Select an atom to attach rings/groups; Esc clears the pending anchor."
        return "Chemistry engine: basic fallback only. Install RDKit for robust valence, aromaticity and canonical SMILES."

    def _bind_events(self):
        self.canvas.bind("<Button-1>", self.on_click)
        self.canvas.bind("<B1-Motion>", self.on_drag)
        self.canvas.bind("<ButtonRelease-1>", self.on_release)
        self.canvas.bind("<Button-3>", self.on_right_click)
        self.canvas.bind("<Motion>", self.on_mouse_motion)

        self.root.bind("<Control-z>", lambda _e: self.undo())
        self.root.bind("<Control-y>", lambda _e: self.redo())
        self.root.bind("<Control-c>", lambda _e: self.copy_selection())
        self.root.bind("<Control-v>", lambda _e: self.paste_selection())
        self.root.bind("<Delete>", lambda _e: self.delete_selected())
        self.root.bind("<Escape>", lambda _e: self.cancel_pending())
        for key, element in (("c", "C"), ("n", "N"), ("o", "O"), ("h", "H"),
                             ("s", "S"), ("p", "P"), ("f", "F")):
            self.root.bind(key, lambda _e, value=element: self.selected_element.set(value))
        for order in (1, 2, 3):
            self.root.bind(str(order), lambda _e, value=order: self.bond_order.set(value))

    # ----------------------------------------------------------- state/history
    def _capture_state(self):
        index = {atom: i for i, atom in enumerate(self.atoms)}
        return {
            "atoms": [(a.x, a.y, a.element, a.charge) for a in self.atoms],
            "bonds": [(index[b.atom1], index[b.atom2], b.order, b.is_aromatic)
                      for b in self.bonds],
        }

    def _push_undo_snapshot(self, snapshot):
        self.undo_stack.append(snapshot)
        if len(self.undo_stack) > self.max_undo:
            self.undo_stack.pop(0)
        self.redo_stack.clear()

    def save_state(self):
        """Save state before a mutation."""
        self._push_undo_snapshot(self._capture_state())

    def undo(self):
        if not self.undo_stack:
            return
        self.redo_stack.append(self._capture_state())
        self._restore_state(self.undo_stack.pop())

    def redo(self):
        if not self.redo_stack:
            return
        self.undo_stack.append(self._capture_state())
        self._restore_state(self.redo_stack.pop())

    def _restore_state(self, state):
        self.canvas.delete("all")
        self.atoms = []
        self.bonds = []
        self.selected_atoms.clear()
        self.selected_bond = None
        self.pending_bond_atom = None
        self.drag_start_atom = None

        for x, y, element, charge in state["atoms"]:
            self.atoms.append(Atom(x, y, element, charge))
        for item in state["bonds"]:
            idx1, idx2, order = item[:3]
            aromatic = item[3] if len(item) > 3 else False
            bond = Bond(self.atoms[idx1], self.atoms[idx2], order)
            bond.is_aromatic = aromatic
            self.bonds.append(bond)
        self.redraw_all()

    # ----------------------------------------------------------- chemistry core
    def _build_rdkit_molecule(self):
        if not RDKIT_AVAILABLE or not self.atoms:
            self._rdkit_mol = None
            self._rdkit_error = None
            self._rdkit_sanitized = False
            return None

        rw = Chem.RWMol()
        atom_to_idx = {}
        try:
            for atom in self.atoms:
                rd_atom = Chem.Atom(atom.element)
                rd_atom.SetFormalCharge(int(atom.charge))
                idx = rw.AddAtom(rd_atom)
                atom_to_idx[atom] = idx

            for bond in self.bonds:
                if bond.order == 1:
                    kind = Chem.BondType.SINGLE
                elif bond.order == 2:
                    kind = Chem.BondType.DOUBLE
                elif bond.order == 3:
                    kind = Chem.BondType.TRIPLE
                else:
                    raise ValueError("Only single, double and triple bonds are supported.")
                # Aromaticity is recalculated from the bond graph by RDKit during
                # sanitization. Do not trust the cached display flag as input.
                rw.AddBond(atom_to_idx[bond.atom1], atom_to_idx[bond.atom2], kind)

            mol = rw.GetMol()
            Chem.SanitizeMol(mol)
            self._rdkit_mol = mol
            self._rdkit_error = None
            self._rdkit_sanitized = True

            for atom in self.atoms:
                rd_atom = mol.GetAtomWithIdx(atom_to_idx[atom])
                atom.implicit_h = int(rd_atom.GetNumImplicitHs())
                atom.is_valid = True
            for bond in self.bonds:
                rd_bond = mol.GetBondBetweenAtoms(atom_to_idx[bond.atom1], atom_to_idx[bond.atom2])
                bond.is_aromatic = bool(rd_bond.GetIsAromatic())
            return mol
        except Exception as exc:
            self._rdkit_mol = None
            self._rdkit_error = str(exc).splitlines()[0][:180]
            self._rdkit_sanitized = False
            return None

    def refresh_chemistry(self):
        """Recompute implicit H and validity, using RDKit whenever available."""
        mol = self._build_rdkit_molecule()
        if mol is not None:
            return
        for atom in self.atoms:
            atom.fallback_implicit_h()
            atom.fallback_validate_valence()

    def calculate_molecular_formula(self):
        if not self.atoms:
            return "—"
        if RDKIT_AVAILABLE and self._rdkit_mol is not None:
            try:
                return rdMolDescriptors.CalcMolFormula(self._rdkit_mol)
            except Exception:
                pass
        counts = defaultdict(int)
        for atom in self.atoms:
            counts[atom.element] += 1
            counts["H"] += atom.implicit_h
        result = ""
        for element in ("C", "H"):
            if counts.get(element, 0):
                result += element + (str(counts[element]) if counts[element] != 1 else "")
                counts.pop(element, None)
        for element in sorted(counts):
            if counts[element]:
                result += element + (str(counts[element]) if counts[element] != 1 else "")
        if any(a.charge for a in self.atoms):
            net_charge = sum(a.charge for a in self.atoms)
            if net_charge:
                result += ("+" if net_charge > 0 else "-") + (str(abs(net_charge)) if abs(net_charge) > 1 else "")
        return result or "—"

    def calculate_molecular_weight(self):
        if not self.atoms:
            return 0.0
        if RDKIT_AVAILABLE and self._rdkit_mol is not None:
            try:
                return round(float(Descriptors.MolWt(self._rdkit_mol)), 2)
            except Exception:
                pass
        total = 0.0
        for atom in self.atoms:
            total += ATOMIC_WEIGHTS.get(atom.element, 0.0)
            total += atom.implicit_h * ATOMIC_WEIGHTS["H"]
        return round(total, 2)

    def generate_smiles(self):
        if not self.atoms:
            return "—"
        if not RDKIT_AVAILABLE:
            return "Install RDKit for SMILES"
        if self._rdkit_mol is None:
            return "Unavailable (invalid structure)"
        try:
            return Chem.MolToSmiles(self._rdkit_mol, canonical=True)
        except Exception:
            return "Unavailable"

    def validate_structure(self):
        if not self.atoms:
            return False, "Empty molecule"

        issues = []
        invalid = [a for a in self.atoms if not a.is_valid]
        if invalid:
            indices = [str(self.atoms.index(a) + 1) for a in invalid[:6]]
            suffix = "…" if len(invalid) > 6 else ""
            issues.append("Check valence at atom(s) " + ", ".join(indices) + suffix)

        components = self.get_connected_components()
        if len(components) > 1:
            issues.append("Disconnected fragments: %d" % len(components))

        if self.has_invalid_bonds():
            issues.append("Unsupported or unusual bond combination")

        if RDKIT_AVAILABLE and self._rdkit_error:
            issues.append("RDKit: " + self._rdkit_error)
        elif not RDKIT_AVAILABLE:
            issues.append("Basic checks only — install RDKit for chemistry validation")

        return len(issues) == 0, "; ".join(issues)

    def has_invalid_bonds(self):
        for bond in self.bonds:
            a, b = bond.atom1.element, bond.atom2.element
            if "H" in (a, b) and bond.order > 1:
                return True
            if a in HALOGENS and b in HALOGENS and bond.order > 1:
                return True
        return False

    def _update_info_panel(self):
        self.refresh_chemistry()
        formula = self.calculate_molecular_formula()
        weight = self.calculate_molecular_weight()
        smiles = self.generate_smiles()
        valid, issues = self.validate_structure()

        self.formula_label.config(text="Formula: %s" % formula)
        self.weight_label.config(text="MW: %s g/mol" % ("—" if not self.atoms else weight))
        self.atom_count_label.config(text="Atoms: %d" % len(self.atoms))
        self.bond_count_label.config(text="Bonds: %d" % len(self.bonds))
        self.smiles_label.config(text="SMILES: %s" % smiles)

        if not self.atoms:
            self.validation_label.config(text="Empty molecule", fg="#555555")
        elif valid:
            self.validation_label.config(text="✓ Structure checks passed", fg="#187344")
        else:
            self.validation_label.config(text="⚠ " + issues, fg="#B42318")

    # --------------------------------------------------------------- geometry
    def find_atom_at(self, x, y, radius=None):
        radius = self.ATOM_RADIUS if radius is None else radius
        for atom in reversed(self.atoms):
            if atom.distance_to(x, y) <= radius:
                return atom
        return None

    def find_bond_at(self, x, y, threshold=7):
        for bond in reversed(self.bonds):
            if self.point_near_line(x, y, bond.atom1.x, bond.atom1.y,
                                    bond.atom2.x, bond.atom2.y, threshold):
                return bond
        return None

    def point_near_line(self, px, py, x1, y1, x2, y2, threshold=5):
        dx, dy = x2 - x1, y2 - y1
        length_sq = dx * dx + dy * dy
        if length_sq == 0:
            return math.hypot(px - x1, py - y1) < threshold
        t = max(0.0, min(1.0, ((px - x1) * dx + (py - y1) * dy) / length_sq))
        return math.hypot(px - (x1 + t * dx), py - (y1 + t * dy)) < threshold

    def snap_angle(self, x1, y1, x2, y2):
        dx, dy = x2 - x1, y2 - y1
        distance = math.hypot(dx, dy)
        if distance < 0.001:
            return x2, y2
        angle = math.degrees(math.atan2(dy, dx)) % 360
        nearest = min(self.SNAP_ANGLES, key=lambda a: abs((angle - a + 180) % 360 - 180))
        rad = math.radians(nearest)
        return x1 + distance * math.cos(rad), y1 + distance * math.sin(rad)

    def _direction_from_anchor(self, atom):
        x, y = self.last_canvas_pos
        dx, dy = x - atom.x, y - atom.y
        if math.hypot(dx, dy) < 5:
            return 1.0, 0.0
        snapped_x, snapped_y = self.snap_angle(atom.x, atom.y, x, y)
        dx, dy = snapped_x - atom.x, snapped_y - atom.y
        length = math.hypot(dx, dy) or 1.0
        return dx / length, dy / length

    def _anchor_atom(self):
        if self.selected_atoms:
            for atom in self.atoms:
                if atom in self.selected_atoms:
                    return atom
        if self.pending_bond_atom in self.atoms:
            return self.pending_bond_atom
        return None

    def on_mouse_motion(self, event):
        self.last_canvas_pos = (event.x, event.y)

    # ----------------------------------------------------------- drawing events
    def on_click(self, event):
        self.last_canvas_pos = (event.x, event.y)
        mode = self.tool.get()
        atom = self.find_atom_at(event.x, event.y)

        if mode == "draw":
            if atom is not None:
                # Click-to-connect: a second atom click completes the bond.
                if self.pending_bond_atom in self.atoms and self.pending_bond_atom is not atom:
                    self._create_or_update_bond(self.pending_bond_atom, atom)
                    self.pending_bond_atom = None
                    self.drag_start_atom = None
                    self.selected_atoms = {atom}
                    self.selected_bond = None
                    self.redraw_all()
                    return
                self.pending_bond_atom = atom
                self.drag_start_atom = atom
                self.drag_moved = False
                self.selected_atoms = {atom}
                self.selected_bond = None
                self.redraw_all(refresh=False)
            else:
                # With an active anchor, a click on empty space extends the chain.
                anchor = self.pending_bond_atom
                if anchor in self.atoms:
                    self._add_atom_and_bond(anchor, event.x, event.y, save=True)
                    self.pending_bond_atom = None
                else:
                    self.save_state()
                    new_atom = Atom(event.x, event.y, self.selected_element.get())
                    self.atoms.append(new_atom)
                    self.selected_atoms = {new_atom}
                    self.selected_bond = None
                    self.pending_bond_atom = None
                    self.redraw_all()

        elif mode == "select":
            self.pending_bond_atom = None
            self.drag_start_atom = None
            if atom is not None:
                if event.state & 0x0001:  # Shift-click adds/removes from selection.
                    if atom in self.selected_atoms:
                        self.selected_atoms.remove(atom)
                    else:
                        self.selected_atoms.add(atom)
                else:
                    self.selected_atoms = {atom}
                self.selected_bond = None
            else:
                bond = self.find_bond_at(event.x, event.y)
                self.selected_atoms = set()
                self.selected_bond = bond
            self.redraw_all(refresh=False)

        elif mode == "erase":
            if atom is not None or self.find_bond_at(event.x, event.y) is not None:
                self.save_state()
                self.delete_at(event.x, event.y)
                self.selected_atoms.clear()
                self.selected_bond = None
                self.pending_bond_atom = None
                self.redraw_all()

        elif mode == "move":
            if atom is not None:
                self.selected_atoms = {atom}
                self.selected_bond = None
                self.pending_bond_atom = None
                self.drag_start_atom = atom
                self.move_component = self.get_connected_component(atom)
                self.move_last = (event.x, event.y)
                self.move_before_state = self._capture_state()
                self.move_undo_saved = False
                self.drag_moved = False
                self.redraw_all(refresh=False)

    def on_drag(self, event):
        self.last_canvas_pos = (event.x, event.y)
        if self.tool.get() == "draw" and self.drag_start_atom is not None:
            if math.hypot(event.x - self.drag_start_atom.x,
                          event.y - self.drag_start_atom.y) > 3:
                self.drag_moved = True
            if self.temp_line:
                self.canvas.delete(self.temp_line)
            x2, y2 = self.snap_angle(self.drag_start_atom.x, self.drag_start_atom.y,
                                    event.x, event.y)
            self.temp_line = self.canvas.create_line(
                self.drag_start_atom.x, self.drag_start_atom.y, x2, y2,
                fill="#7A8699", dash=(4, 3), width=2
            )

        elif self.tool.get() == "move" and self.drag_start_atom is not None and self.move_last:
            dx, dy = event.x - self.move_last[0], event.y - self.move_last[1]
            if abs(dx) + abs(dy) > 0:
                self.drag_moved = True
                if not self.move_undo_saved:
                    self._push_undo_snapshot(self.move_before_state)
                    self.move_undo_saved = True
                for atom in self.move_component:
                    atom.x += dx
                    atom.y += dy
                self.move_last = (event.x, event.y)
                self.redraw_all(refresh=False)

    def on_release(self, event):
        self.last_canvas_pos = (event.x, event.y)
        if self.temp_line:
            self.canvas.delete(self.temp_line)
            self.temp_line = None

        if self.tool.get() == "draw" and self.drag_start_atom is not None:
            source = self.drag_start_atom
            target = self.find_atom_at(event.x, event.y)
            moved = self.drag_moved
            if moved and target is not source:
                if target is not None:
                    self._create_or_update_bond(source, target)
                    self.selected_atoms = {target}
                    self.pending_bond_atom = None
                else:
                    self._add_atom_and_bond(source, event.x, event.y, save=True)
                    self.pending_bond_atom = None
                self.redraw_all()
            # A simple click leaves the source as the pending click-to-connect anchor.
            self.drag_start_atom = None
            self.drag_moved = False

        elif self.tool.get() == "move":
            self.drag_start_atom = None
            self.move_component = []
            self.move_last = None
            self.move_before_state = None
            self.move_undo_saved = False
            self.drag_moved = False

    def on_right_click(self, event):
        if self.find_atom_at(event.x, event.y) is not None or self.find_bond_at(event.x, event.y) is not None:
            self.save_state()
            self.delete_at(event.x, event.y)
            self.selected_atoms.clear()
            self.selected_bond = None
            self.pending_bond_atom = None
            self.redraw_all()

    def cancel_pending(self):
        self.pending_bond_atom = None
        self.drag_start_atom = None
        self.selected_atoms.clear()
        self.selected_bond = None
        if self.temp_line:
            self.canvas.delete(self.temp_line)
            self.temp_line = None
        self.redraw_all(refresh=False)

    def _add_atom_and_bond(self, anchor, x, y, save=False):
        if save:
            self.save_state()
        sx, sy = self.snap_angle(anchor.x, anchor.y, x, y)
        dx, dy = sx - anchor.x, sy - anchor.y
        length = math.hypot(dx, dy)
        if length < 1:
            dx, dy, length = 1.0, 0.0, 1.0
        new_x = anchor.x + dx / length * self.DEFAULT_BOND_LENGTH
        new_y = anchor.y + dy / length * self.DEFAULT_BOND_LENGTH
        new_atom = Atom(new_x, new_y, self.selected_element.get())
        self.atoms.append(new_atom)
        bond = Bond(anchor, new_atom, self.bond_order.get())
        self.bonds.append(bond)
        self.selected_atoms = {new_atom}
        self.selected_bond = None
        self.redraw_all()

    def _create_or_update_bond(self, atom1, atom2):
        if atom1 is atom2:
            return
        for bond in atom1.bonds:
            if bond.atom1 is atom2 or bond.atom2 is atom2:
                self.save_state()
                bond.order = self.bond_order.get()
                bond.is_aromatic = False
                self.redraw_all()
                return
        self.save_state()
        self.bonds.append(Bond(atom1, atom2, self.bond_order.get()))
        self.selected_bond = None
        self.redraw_all()

    # --------------------------------------------------------------- rendering
    def redraw_all(self, refresh=True):
        if refresh:
            self.refresh_chemistry()
        self.canvas.delete("all")
        for atom in self.atoms:
            atom.canvas_id = None
            atom.text_id = None
        for bond in self.bonds:
            bond.canvas_ids = []
            self.draw_bond(bond)
        for atom in self.atoms:
            self.draw_atom(atom)
        self._update_info_panel()

    def _atom_has_visible_label(self, atom):
        return (atom.element != "C" or len(atom.bonds) == 0 or atom.charge != 0)

    def _display_atom_text(self, atom):
        label = atom.element
        if atom.implicit_h > 0 and atom.element != "H":
            label += "H"
            if atom.implicit_h > 1:
                label += str(atom.implicit_h).translate(SUBSCRIPTS)
        if atom.charge:
            magnitude = abs(atom.charge)
            sign = "+" if atom.charge > 0 else "−"
            label += (str(magnitude).translate(SUBSCRIPTS) if magnitude > 1 else "") + sign
        return label

    def draw_atom(self, atom):
        selected = atom in self.selected_atoms
        if selected:
            r = 10 if self._atom_has_visible_label(atom) else 8
            atom.canvas_id = self.canvas.create_oval(
                atom.x-r, atom.y-r, atom.x+r, atom.y+r,
                outline="#2674D9", width=2, fill=""
            )

        if self._atom_has_visible_label(atom):
            label = self._display_atom_text(atom)
            # Opaque white backing keeps bond strokes from crossing atom labels.
            width = max(13, 4.5 * len(label) + 5)
            atom.canvas_id = self.canvas.create_oval(
                atom.x-width/2, atom.y-11, atom.x+width/2, atom.y+11,
                fill="white", outline="white"
            )
            colour = "#222222" if atom.is_valid else "#B42318"
            atom.text_id = self.canvas.create_text(
                atom.x, atom.y, text=label, font=("Arial", 11, "bold"), fill=colour
            )
        # Carbon vertices in skeletal notation are intentionally not drawn as dots.

    def _bond_endpoints(self, bond):
        a, b = bond.atom1, bond.atom2
        dx, dy = b.x - a.x, b.y - a.y
        length = math.hypot(dx, dy)
        if length < 0.001:
            return a.x, a.y, b.x, b.y, 0.0, 0.0, 0.0
        ux, uy = dx / length, dy / length
        offset_a = 10 if self._atom_has_visible_label(a) else 0
        offset_b = 10 if self._atom_has_visible_label(b) else 0
        return (a.x + ux*offset_a, a.y + uy*offset_a,
                b.x - ux*offset_b, b.y - uy*offset_b, ux, uy, length)

    def draw_bond(self, bond):
        x1, y1, x2, y2, ux, uy, length = self._bond_endpoints(bond)
        colour = "#2674D9" if bond is self.selected_bond else "#202124"
        width = 3 if bond is self.selected_bond else 2
        if length < 0.001:
            return
        px, py = -uy, ux

        if bond.order == 1:
            bond.canvas_ids.append(self.canvas.create_line(x1, y1, x2, y2,
                                                           fill=colour, width=width,
                                                           capstyle=tk.ROUND))
        elif bond.order == 2:
            offset = 3.0
            bond.canvas_ids.append(self.canvas.create_line(x1+px*offset, y1+py*offset,
                                                           x2+px*offset, y2+py*offset,
                                                           fill=colour, width=width))
            bond.canvas_ids.append(self.canvas.create_line(x1-px*offset, y1-py*offset,
                                                           x2-px*offset, y2-py*offset,
                                                           fill=colour, width=width))
        elif bond.order == 3:
            offset = 4.2
            bond.canvas_ids.append(self.canvas.create_line(x1, y1, x2, y2,
                                                           fill=colour, width=width))
            bond.canvas_ids.append(self.canvas.create_line(x1+px*offset, y1+py*offset,
                                                           x2+px*offset, y2+py*offset,
                                                           fill=colour, width=width))
            bond.canvas_ids.append(self.canvas.create_line(x1-px*offset, y1-py*offset,
                                                           x2-px*offset, y2-py*offset,
                                                           fill=colour, width=width))

    # -------------------------------------------------------------- deletion
    def delete_at(self, x, y):
        atom = self.find_atom_at(x, y)
        if atom is not None:
            self.delete_atom(atom)
            return True
        bond = self.find_bond_at(x, y)
        if bond is not None:
            self.delete_bond(bond)
            return True
        return False

    def delete_atom(self, atom):
        for bond in list(atom.bonds):
            self.delete_bond(bond)
        if atom in self.atoms:
            self.atoms.remove(atom)
        self.selected_atoms.discard(atom)
        if self.pending_bond_atom is atom:
            self.pending_bond_atom = None

    def delete_bond(self, bond):
        if bond in bond.atom1.bonds:
            bond.atom1.bonds.remove(bond)
        if bond in bond.atom2.bonds:
            bond.atom2.bonds.remove(bond)
        if bond in self.bonds:
            self.bonds.remove(bond)
        if self.selected_bond is bond:
            self.selected_bond = None

    def delete_selected(self):
        if self.selected_atoms:
            self.save_state()
            for atom in list(self.selected_atoms):
                if atom in self.atoms:
                    self.delete_atom(atom)
            self.selected_atoms.clear()
            self.selected_bond = None
            self.pending_bond_atom = None
            self.redraw_all()
        elif self.selected_bond is not None:
            self.save_state()
            self.delete_bond(self.selected_bond)
            self.selected_bond = None
            self.redraw_all()

    def clear_all(self):
        if not self.atoms:
            return
        if messagebox.askyesno("Clear molecule", "Delete the entire drawing?"):
            self.save_state()
            self.atoms.clear()
            self.bonds.clear()
            self.selected_atoms.clear()
            self.selected_bond = None
            self.pending_bond_atom = None
            self.redraw_all()

    # ------------------------------------------------------------ connectivity
    def get_connected_component(self, start):
        if start not in self.atoms:
            return []
        result = []
        visited = {start}
        stack = [start]
        while stack:
            atom = stack.pop()
            result.append(atom)
            for bond in atom.bonds:
                other = bond.atom2 if bond.atom1 is atom else bond.atom1
                if other not in visited:
                    visited.add(other)
                    stack.append(other)
        return result

    def get_connected_components(self):
        components = []
        visited = set()
        for atom in self.atoms:
            if atom not in visited:
                component = self.get_connected_component(atom)
                components.append(component)
                visited.update(component)
        return components

    # --------------------------------------------------------------- templates
    def _new_ring(self, size, aromatic=False):
        anchor = self._anchor_atom()
        length = self.DEFAULT_BOND_LENGTH
        radius = length / (2.0 * math.sin(math.pi / size))
        ring_atoms = []

        if anchor is not None:
            ux, uy = self._direction_from_anchor(anchor)
            cx = anchor.x + (length + radius) * ux
            cy = anchor.y + (length + radius) * uy
            # Vertex zero faces the anchor; the external bond has standard length.
            start = math.atan2(uy, ux) + math.pi
            points = [(cx + radius*math.cos(start + i*2*math.pi/size),
                       cy + radius*math.sin(start + i*2*math.pi/size))
                      for i in range(size)]
        else:
            cx, cy = self.last_canvas_pos
            if cx < 80 and cy < 80:
                cx, cy = 450, 330
            start = -math.pi/2
            points = [(cx + radius*math.cos(start + i*2*math.pi/size),
                       cy + radius*math.sin(start + i*2*math.pi/size))
                      for i in range(size)]

        self.save_state()
        for x, y in points:
            atom = Atom(x, y, "C")
            self.atoms.append(atom)
            ring_atoms.append(atom)
        for i in range(size):
            order = 2 if aromatic and i % 2 == 0 else 1
            self.bonds.append(Bond(ring_atoms[i], ring_atoms[(i+1) % size], order))
        if anchor is not None:
            self.bonds.append(Bond(anchor, ring_atoms[0], 1))
        self.selected_atoms = {ring_atoms[0]}
        self.selected_bond = None
        self.pending_bond_atom = ring_atoms[0]
        self.redraw_all()

    def add_benzene(self):
        self._new_ring(6, aromatic=True)

    def add_cyclohexane(self):
        self._new_ring(6, aromatic=False)

    def add_cyclopentane(self):
        self._new_ring(5, aromatic=False)

    def add_functional_group(self, group_type):
        anchor = self._anchor_atom()
        length = self.DEFAULT_BOND_LENGTH
        self.save_state()

        if anchor is not None:
            ux, uy = self._direction_from_anchor(anchor)
            cx, cy = anchor.x + ux*length, anchor.y + uy*length
            if group_type == "CH3":
                group_atom = Atom(cx, cy, "C")
                self.atoms.append(group_atom)
                self.bonds.append(Bond(anchor, group_atom, 1))
                self.selected_atoms = {group_atom}
            elif group_type in ("OH", "NH2"):
                element = "O" if group_type == "OH" else "N"
                group_atom = Atom(cx, cy, element)
                self.atoms.append(group_atom)
                self.bonds.append(Bond(anchor, group_atom, 1))
                self.selected_atoms = {group_atom}
            elif group_type == "COOH":
                carboxyl_c = Atom(cx, cy, "C")
                angle = math.atan2(uy, ux)
                o1 = Atom(cx + length*math.cos(angle + math.pi/3),
                          cy + length*math.sin(angle + math.pi/3), "O")
                o2 = Atom(cx + length*math.cos(angle - math.pi/3),
                          cy + length*math.sin(angle - math.pi/3), "O")
                self.atoms.extend((carboxyl_c, o1, o2))
                self.bonds.extend((Bond(anchor, carboxyl_c, 1),
                                   Bond(carboxyl_c, o1, 2),
                                   Bond(carboxyl_c, o2, 1)))
                self.selected_atoms = {carboxyl_c}
            self.selected_bond = None
            self.pending_bond_atom = None
        else:
            x, y = self.last_canvas_pos
            if x < 80 and y < 80:
                x, y = 450, 330
            if group_type == "CH3":
                atom = Atom(x, y, "C")
                self.atoms.append(atom)
                self.selected_atoms = {atom}
            elif group_type == "OH":
                # Standalone OH template is represented as water, a closed-shell molecule.
                o, h = Atom(x, y, "O"), Atom(x + 30, y, "H")
                self.atoms.extend((o, h))
                self.bonds.append(Bond(o, h, 1))
                self.selected_atoms = {o}
            elif group_type == "NH2":
                # Standalone nitrogen defaults to ammonia; attach it to an atom for NH2.
                atom = Atom(x, y, "N")
                self.atoms.append(atom)
                self.selected_atoms = {atom}
            elif group_type == "COOH":
                c = Atom(x, y, "C")
                o1 = Atom(x + length*math.cos(-math.pi/3), y + length*math.sin(-math.pi/3), "O")
                o2 = Atom(x + length*math.cos(math.pi/3), y + length*math.sin(math.pi/3), "O")
                self.atoms.extend((c, o1, o2))
                self.bonds.extend((Bond(c, o1, 2), Bond(c, o2, 1)))
                self.selected_atoms = {c}
            self.selected_bond = None
            self.pending_bond_atom = None

        self.redraw_all()

    def apply_charge(self):
        if not self.selected_atoms:
            messagebox.showinfo("Formal charge", "Choose Select and click an atom first.")
            return
        try:
            charge = int(self.charge_value.get())
        except (ValueError, tk.TclError):
            messagebox.showerror("Formal charge", "Charge must be an integer from -3 to +3.")
            return
        if charge < -3 or charge > 3:
            messagebox.showerror("Formal charge", "Charge must be between -3 and +3.")
            return
        self.save_state()
        for atom in self.selected_atoms:
            atom.charge = charge
        self.redraw_all()

    # ------------------------------------------------------------- copy/paste
    def _atoms_for_copy(self):
        if not self.selected_atoms:
            return []
        # A single selected atom copies its complete connected fragment.
        if len(self.selected_atoms) == 1:
            selected = next(iter(self.selected_atoms))
            return self.get_connected_component(selected)
        return [a for a in self.atoms if a in self.selected_atoms]

    def copy_selection(self):
        selected = self._atoms_for_copy()
        if not selected:
            self.status_label.config(text="Select an atom or fragment before copying.")
            return
        index = {atom: i for i, atom in enumerate(selected)}
        self.clipboard = {
            "atoms": [(a.x, a.y, a.element, a.charge) for a in selected],
            "bonds": [(index[b.atom1], index[b.atom2], b.order, b.is_aromatic)
                      for b in self.bonds if b.atom1 in index and b.atom2 in index],
        }
        self.paste_count = 0
        self.status_label.config(text="Copied %d atom(s)." % len(selected))

    def paste_selection(self):
        if not getattr(self, "clipboard", None):
            return
        self.save_state()
        self.paste_count += 1
        dx = dy = 35 * self.paste_count
        pasted = []
        for x, y, element, charge in self.clipboard["atoms"]:
            atom = Atom(x + dx, y + dy, element, charge)
            self.atoms.append(atom)
            pasted.append(atom)
        for item in self.clipboard["bonds"]:
            i, j, order = item[:3]
            aromatic = item[3] if len(item) > 3 else False
            bond = Bond(pasted[i], pasted[j], order)
            bond.is_aromatic = aromatic
            self.bonds.append(bond)
        self.selected_atoms = set(pasted)
        self.selected_bond = None
        self.pending_bond_atom = None
        self.redraw_all()
        self.status_label.config(text="Pasted %d atom(s)." % len(pasted))


def main():
    root = tk.Tk()
    MoleculeEditor(root)
    root.mainloop()


if __name__ == "__main__":
    main()
