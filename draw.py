"""ChemDraw-style 2D structure and reaction editor (Tkinter + optional RDKit).

Interaction model (ChemDraw-like)
- Draw tool, click blank canvas ........ creates a bond (two atoms) at a standard length.
- Draw tool, click an atom ............. adds a bond at the best free angle (zigzag for chains).
- Draw tool, drag ...................... fixed bond length, 30-degree snapping; releasing on an
                                         existing atom bonds to it (ring closing).
- Draw tool, click a bond .............. cycles single -> double -> triple.
- Hover atom + letter (c n o s p f h) .. changes that atom's element. Hover bond + 1/2/3 sets order.
- Ring buttons ......................... attach to the selected atom, FUSE onto the selected bond,
                                         or float at the cursor.
- Select tool .......................... click, shift-click, or rubber-band box select.
- Clean Up ............................. RDKit 2D layout (only when you press the button).
- Import SMILES / Export .mol .......... through RDKit.

Install the chemistry backend with:  python -m pip install rdkit
"""

from __future__ import annotations

import math
import re
import tkinter as tk
from tkinter import ttk, messagebox, simpledialog, filedialog
from collections import defaultdict

try:
    from rdkit import Chem, rdBase
    from rdkit.Chem import AllChem, Descriptors, rdMolDescriptors
    RDKIT_AVAILABLE = True
except ImportError:
    Chem = rdBase = AllChem = Descriptors = rdMolDescriptors = None
    RDKIT_AVAILABLE = False


ELEMENTS = ["C", "N", "O", "S", "P", "F", "Cl", "Br", "I", "H"]
ATOMIC_WEIGHTS = {
    "H": 1.008, "C": 12.011, "N": 14.007, "O": 15.999,
    "F": 18.998, "P": 30.974, "S": 32.06, "Cl": 35.45,
    "Br": 79.904, "I": 126.904,
}
COMMON_VALENCES = {
    "C": (4,), "N": (3, 5), "O": (2,), "S": (2, 4, 6),
    "P": (3, 5), "F": (1,), "Cl": (1, 3, 5, 7),
    "Br": (1, 3, 5, 7), "I": (1, 3, 5, 7), "H": (1,),
}
HALOGENS = {"F", "Cl", "Br", "I"}
SUBSCRIPTS = str.maketrans("0123456789", "₀₁₂₃₄₅₆₇₈₉")


class Atom:
    """One chemical atom. Coordinates are display-only; bonds define chemistry."""

    def __init__(self, x, y, element="C", charge=0):
        self.x = float(x)
        self.y = float(y)
        self.element = element
        self.charge = int(charge)
        self.bonds = []
        self.implicit_h = 0

    def distance_to(self, x, y):
        return math.hypot(self.x - x, self.y - y)

    def bond_order_sum(self):
        return sum(bond.order for bond in self.bonds)

    def neighbors(self):
        return [b.atom2 if b.atom1 is self else b.atom1 for b in self.bonds]


class Bond:
    """A chemical bond between two Atom objects."""

    def __init__(self, atom1, atom2, order=1):
        self.atom1 = atom1
        self.atom2 = atom2
        self.order = int(order)
        atom1.bonds.append(self)
        atom2.bonds.append(self)

    def other(self, atom):
        return self.atom2 if self.atom1 is atom else self.atom1


class Annotation:
    """Reaction-scheme drawing object; separate from the molecule graph."""

    def __init__(self, kind, x1, y1, x2=None, y2=None, text=""):
        self.kind = kind
        self.x1 = float(x1)
        self.y1 = float(y1)
        self.x2 = float(x1 if x2 is None else x2)
        self.y2 = float(y1 if y2 is None else y2)
        self.text = str(text)

    def move_by(self, dx, dy):
        self.x1 += dx
        self.y1 += dy
        self.x2 += dx
        self.y2 += dy


class MoleculeEditor:
    ATOM_HIT_RADIUS = 14
    BOND_LENGTH = 42.0
    SNAP_ANGLES = tuple(range(0, 360, 30))

    TOOL_HELP = {
        "draw": "Draw: click blank = bond, click atom = add bond, drag = fixed-length bond, "
                "click bond = cycle order. Hover atom + letter changes element.",
        "select": "Select: click, shift-click, or drag a box. Ring buttons fuse onto a selected bond.",
        "move": "Move: drag a molecule fragment or a reaction annotation.",
        "erase": "Erase: click an atom, bond or annotation. Right-click also erases.",
        "arrow": "Reaction arrow: drag from the tail to the arrowhead.",
        "equilibrium": "Equilibrium arrow: drag from left to right.",
        "plus": "Plus sign: click the canvas to place +.",
        "equals": "Equals sign: click the canvas to place =.",
        "text": "Text label: click the canvas, then enter a label or reaction condition.",
    }

    def __init__(self, root):
        self.root = root
        self.root.title("Molecule & Reaction Editor")
        self.root.geometry("1280x800")
        self.root.minsize(1100, 660)

        self.atoms = []
        self.bonds = []
        self.annotations = []

        self.undo_stack = []
        self.redo_stack = []
        self.max_undo = 100
        self.clipboard = None
        self.paste_count = 0

        self.selected_element = tk.StringVar(value="C")
        self.bond_order = tk.IntVar(value=1)
        self.tool = tk.StringVar(value="draw")
        self.charge_value = tk.IntVar(value=0)
        self.selected_atoms = set()
        self.selected_bond = None
        self.selected_annotation = None

        self.last_canvas_pos = (440.0, 330.0)
        self.temp_ids = []

        # draw-tool state
        self.draw_start = None
        self.draw_atom = None
        self.draw_bond = None
        self.draw_moved = False
        # annotation drag
        self.annotation_start = None
        # move-tool state
        self.move_component = []
        self.move_last = None
        self.move_before_state = None
        self.move_undo_saved = False
        self.moving_annotation = None
        # rubber-band state
        self.rubber_start = None
        self.rubber_shift = False

        self.chem_mol = None
        self.chem_error = None
        self.invalid_atom_indices = set()
        self.validation_state = "unchecked"
        self.validation_notes = []

        self._setup_ui()
        self._bind_events()
        self._redraw_canvas()
        self._update_tool_status()

    # ------------------------------------------------------------------ UI
    def _setup_ui(self):
        top = tk.Frame(self.root, padx=5, pady=4, relief=tk.GROOVE, borderwidth=1)
        top.pack(side=tk.TOP, fill=tk.X)

        tk.Label(top, text="Element").pack(side=tk.LEFT, padx=(2, 3))
        ttk.Combobox(top, textvariable=self.selected_element, values=ELEMENTS,
                     state="readonly", width=4).pack(side=tk.LEFT, padx=(0, 8))

        tk.Label(top, text="Bond").pack(side=tk.LEFT, padx=(0, 3))
        for order, label in ((1, "—"), (2, "="), (3, "≡")):
            tk.Radiobutton(top, text=label, variable=self.bond_order, value=order,
                           indicatoron=False, width=3, padx=2, pady=1,
                           takefocus=False).pack(side=tk.LEFT, padx=1)

        ttk.Separator(top, orient=tk.VERTICAL).pack(side=tk.LEFT, fill=tk.Y, padx=7)
        tk.Label(top, text="Tool").pack(side=tk.LEFT, padx=(0, 3))
        for value, label in (("draw", "Draw"), ("select", "Select"),
                             ("move", "Move"), ("erase", "Erase")):
            tk.Radiobutton(top, text=label, variable=self.tool, value=value,
                           command=self._tool_changed, takefocus=False).pack(side=tk.LEFT, padx=1)

        ttk.Separator(top, orient=tk.VERTICAL).pack(side=tk.LEFT, fill=tk.Y, padx=7)
        tk.Button(top, text="Check structure", command=self.check_structure,
                  padx=7).pack(side=tk.LEFT, padx=2)
        tk.Button(top, text="Clean up", command=self.clean_up).pack(side=tk.LEFT, padx=2)
        tk.Button(top, text="Undo", command=self.undo).pack(side=tk.LEFT, padx=(6, 2))
        tk.Button(top, text="Redo", command=self.redo).pack(side=tk.LEFT, padx=2)
        tk.Button(top, text="Clear", command=self.clear_all).pack(side=tk.LEFT, padx=(6, 2))

        ttk.Separator(top, orient=tk.VERTICAL).pack(side=tk.LEFT, fill=tk.Y, padx=7)
        tk.Button(top, text="Import SMILES", command=self.import_smiles).pack(side=tk.LEFT, padx=2)
        tk.Button(top, text="Export .mol", command=self.export_molfile).pack(side=tk.LEFT, padx=2)

        second = tk.Frame(self.root, padx=5, pady=4, relief=tk.GROOVE, borderwidth=1)
        second.pack(side=tk.TOP, fill=tk.X)

        tk.Label(second, text="Rings").pack(side=tk.LEFT, padx=(2, 4))
        for label, size, arom in (("Benzene", 6, True), ("Cyclohexane", 6, False),
                                  ("Cyclopentane", 5, False), ("Cyclopropane", 3, False),
                                  ("Cyclobutane", 4, False), ("Cycloheptane", 7, False)):
            tk.Button(second, text=label,
                      command=lambda s=size, a=arom: self.add_ring(s, a)).pack(side=tk.LEFT, padx=2)

        ttk.Separator(second, orient=tk.VERTICAL).pack(side=tk.LEFT, fill=tk.Y, padx=7)
        tk.Label(second, text="Groups").pack(side=tk.LEFT, padx=(0, 4))
        for label, group in (("CH₃", "CH3"), ("OH", "OH"), ("NH₂", "NH2"), ("COOH", "COOH")):
            tk.Button(second, text=label,
                      command=lambda g=group: self.add_functional_group(g)).pack(side=tk.LEFT, padx=2)

        ttk.Separator(second, orient=tk.VERTICAL).pack(side=tk.LEFT, fill=tk.Y, padx=7)
        tk.Label(second, text="Reaction").pack(side=tk.LEFT, padx=(0, 3))
        for value, label in (("arrow", "→ Arrow"), ("equilibrium", "⇌ Equilibrium"),
                             ("plus", "+ Plus"), ("equals", "= Equals"), ("text", "Text")):
            tk.Radiobutton(second, text=label, variable=self.tool, value=value,
                           command=self._tool_changed, takefocus=False).pack(side=tk.LEFT, padx=1)

        third = tk.Frame(self.root, padx=5, pady=3)
        third.pack(side=tk.TOP, fill=tk.X)
        tk.Label(third, text="Formal charge").pack(side=tk.LEFT, padx=(2, 4))
        tk.Spinbox(third, from_=-3, to=3, width=4, textvariable=self.charge_value).pack(side=tk.LEFT)
        tk.Button(third, text="Apply to selected atom(s)", command=self.apply_charge).pack(
            side=tk.LEFT, padx=5)
        tk.Label(third, text="Check structure never changes your drawing. Clean up only when you press it.",
                 fg="#5B6573").pack(side=tk.LEFT, padx=8)

        main = tk.Frame(self.root)
        main.pack(expand=True, fill=tk.BOTH)
        self.canvas = tk.Canvas(main, bg="white", width=940, height=650,
                                cursor="crosshair", highlightthickness=0, takefocus=True)
        self.canvas.pack(side=tk.LEFT, expand=True, fill=tk.BOTH)

        panel = tk.Frame(main, width=285, relief=tk.SUNKEN, borderwidth=1, padx=10, pady=8)
        panel.pack(side=tk.RIGHT, fill=tk.Y)
        panel.pack_propagate(False)

        tk.Label(panel, text="STRUCTURE", font=("Arial", 11, "bold")).pack(anchor="w", pady=(2, 7))
        self.formula_label = tk.Label(panel, text="", anchor="w", justify=tk.LEFT, wraplength=255)
        self.formula_label.pack(fill=tk.X, pady=2)
        self.weight_label = tk.Label(panel, text="", anchor="w", justify=tk.LEFT)
        self.weight_label.pack(fill=tk.X, pady=2)
        self.smiles_label = tk.Label(panel, text="", anchor="w", justify=tk.LEFT, wraplength=255)
        self.smiles_label.pack(fill=tk.X, pady=(3, 2))
        self.atom_count_label = tk.Label(panel, text="", anchor="w")
        self.atom_count_label.pack(fill=tk.X, pady=2)
        self.bond_count_label = tk.Label(panel, text="", anchor="w")
        self.bond_count_label.pack(fill=tk.X, pady=2)
        self.fragment_count_label = tk.Label(panel, text="", anchor="w")
        self.fragment_count_label.pack(fill=tk.X, pady=2)

        ttk.Separator(panel, orient=tk.HORIZONTAL).pack(fill=tk.X, pady=8)
        tk.Label(panel, text="CHECK RESULT", font=("Arial", 10, "bold")).pack(anchor="w")
        self.validation_label = tk.Label(panel, text="Not checked", anchor="w", justify=tk.LEFT,
                                         wraplength=255, fg="#5B6573", font=("Arial", 9, "bold"))
        self.validation_label.pack(fill=tk.X, pady=(4, 4))

        self.diagnostics_text = tk.Text(panel, height=11, wrap=tk.WORD, relief=tk.FLAT,
                                        bg="#F7F8FA", fg="#24292F", font=("Arial", 9),
                                        padx=6, pady=6, state=tk.DISABLED)
        self.diagnostics_text.pack(fill=tk.BOTH, expand=True)

        tk.Label(panel,
                 text=("Chemistry engine: RDKit" if RDKIT_AVAILABLE else
                       "Chemistry engine: basic checks only\nInstall RDKit for stronger validation."),
                 anchor="w", justify=tk.LEFT, fg="#5B6573", font=("Arial", 8),
                 wraplength=255).pack(fill=tk.X, pady=(8, 2))

        self.status_label = tk.Label(self.root, text="", anchor="w", relief=tk.SUNKEN,
                                     padx=7, pady=3, fg="#4B5563")
        self.status_label.pack(side=tk.BOTTOM, fill=tk.X)
        self._set_diagnostics(["Draw the structure, then click Check structure.",
                               "Suggestions are shown here. The editor never repairs a structure automatically."])

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
        self.root.bind("<Control-a>", lambda _e: self.select_all())
        self.root.bind("<Delete>", lambda _e: self.delete_selected())
        self.root.bind("<BackSpace>", lambda _e: self.delete_selected())
        self.root.bind("<Escape>", lambda _e: self.cancel_pending())
        for key, element in (("c", "C"), ("n", "N"), ("o", "O"), ("h", "H"),
                             ("s", "S"), ("p", "P"), ("f", "F"), ("l", "Cl"), ("b", "Br"), ("i", "I")):
            self.root.bind(key, lambda _e, value=element: self._element_key(value))
        for order in (1, 2, 3):
            self.root.bind(str(order), lambda _e, value=order: self._bond_key(value))

    # ------------------------------------------------------ state and history
    def _capture_state(self):
        idx = {atom: i for i, atom in enumerate(self.atoms)}
        return {
            "atoms": [(a.x, a.y, a.element, a.charge) for a in self.atoms],
            "bonds": [(idx[b.atom1], idx[b.atom2], b.order) for b in self.bonds],
            "annotations": [(a.kind, a.x1, a.y1, a.x2, a.y2, a.text) for a in self.annotations],
        }

    def _push_snapshot(self, snapshot):
        self.undo_stack.append(snapshot)
        if len(self.undo_stack) > self.max_undo:
            self.undo_stack.pop(0)
        self.redo_stack.clear()

    def save_state(self):
        self._push_snapshot(self._capture_state())

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
        self.atoms, self.bonds, self.annotations = [], [], []
        self.selected_atoms.clear()
        self.selected_bond = None
        self.selected_annotation = None
        self.draw_start = self.draw_atom = self.draw_bond = None
        self.annotation_start = None
        for x, y, element, charge in state["atoms"]:
            self.atoms.append(Atom(x, y, element, charge))
        for i, j, order in state["bonds"]:
            self.bonds.append(Bond(self.atoms[i], self.atoms[j], order))
        for kind, x1, y1, x2, y2, text in state.get("annotations", []):
            self.annotations.append(Annotation(kind, x1, y1, x2, y2, text))
        self._invalidate_validation()
        self._redraw_canvas()
        self._set_status("Restored drawing. Run Check structure to review it again.")

    def _invalidate_validation(self):
        self.validation_state = "unchecked"
        self.validation_notes = []
        self.invalid_atom_indices.clear()

    # -------------------------------------------------------- chemistry engine
    def _build_sanitized_molecule(self):
        """Separate RDKit molecule. Never rewrites the editor's own graph."""
        if not RDKIT_AVAILABLE:
            return None, "RDKit is not installed"
        if not self.atoms:
            return None, "Empty drawing"
        rw = Chem.RWMol()
        index = {}
        try:
            for atom in self.atoms:
                rd = Chem.Atom(atom.element)
                rd.SetFormalCharge(int(atom.charge))
                index[atom] = rw.AddAtom(rd)
            types = {1: Chem.BondType.SINGLE, 2: Chem.BondType.DOUBLE, 3: Chem.BondType.TRIPLE}
            for bond in self.bonds:
                rw.AddBond(index[bond.atom1], index[bond.atom2], types[bond.order])
            mol = rw.GetMol()
            with rdBase.BlockLogs():
                Chem.SanitizeMol(mol)
            return mol, None
        except Exception as exc:
            return None, (str(exc).splitlines() or [exc.__class__.__name__])[0][:240]

    def _fallback_targets(self, atom):
        c = atom.charge
        if atom.element == "N" and c == 1:
            return (4,)
        if atom.element == "N" and c == -1:
            return (2,)
        if atom.element == "O" and c == 1:
            return (3,)
        if atom.element == "O" and c == -1:
            return (1,)
        return COMMON_VALENCES.get(atom.element, ())

    def _fallback_implicit_h(self, atom):
        if atom.element == "H":
            return 0
        targets = self._fallback_targets(atom)
        s = atom.bond_order_sum()
        possible = [t for t in targets if t >= s]
        return max(0, min(possible) - s) if possible else 0

    def _refresh_chemistry_cache(self):
        self.chem_mol, self.chem_error = self._build_sanitized_molecule()
        for i, atom in enumerate(self.atoms):
            if self.chem_mol is not None:
                try:
                    atom.implicit_h = int(self.chem_mol.GetAtomWithIdx(i).GetNumImplicitHs())
                    continue
                except Exception:
                    pass
            atom.implicit_h = self._fallback_implicit_h(atom)

    def _heuristic_suspects(self):
        out = set()
        for i, atom in enumerate(self.atoms):
            targets = self._fallback_targets(atom)
            if targets and atom.bond_order_sum() > max(targets):
                out.add(i)
            if atom.element == "H" and atom.bond_order_sum() != 1:
                out.add(i)
        return out

    def _friendly_rdkit_issue(self, raw):
        m = re.search(r"atom\s*#\s*(\d+)\s+([A-Za-z]+),\s*(-?\d+)", raw or "")
        if m:
            idx = int(m.group(1))
            if 0 <= idx < len(self.atoms):
                self.invalid_atom_indices.add(idx)
                return (f"Atom {idx + 1} ({m.group(2)}) has an explicit valence of {m.group(3)} "
                        "that RDKit does not accept for this structure.")
        k = re.search(r"Unkekulized atoms:\s*([0-9 ]+)", raw or "")
        if k:
            ids = [int(v) for v in k.group(1).split() if v.isdigit()]
            self.invalid_atom_indices.update(i for i in ids if 0 <= i < len(self.atoms))
            if ids:
                return ("The ring bond pattern could not be given a valid Kekulé form. Review bond orders "
                        "around atoms " + ", ".join(str(i + 1) for i in ids[:8]) + ".")
        return "The chemistry engine could not sanitize this graph: " + (raw or "unknown error")

    def has_unusual_bonds(self):
        for b in self.bonds:
            a, c = b.atom1.element, b.atom2.element
            if "H" in (a, c) and b.order != 1:
                return True
            if a in HALOGENS and c in HALOGENS and b.order != 1:
                return True
        return False

    def check_structure(self):
        """Report validation results. Never repairs the drawing."""
        self._refresh_chemistry_cache()
        self.invalid_atom_indices.clear()
        notes = []
        if not self.atoms:
            self.validation_state = "unchecked"
            self._set_diagnostics(["Nothing to check yet. Draw a structure first."])
            self.validation_label.config(text="Nothing to validate", fg="#5B6573")
            return

        comps = self.get_connected_components()
        if len(comps) > 1:
            notes.append(f"{len(comps)} separate fragments found. This is allowed for reaction schemes.")
        overlaps = self._overlapping_atom_pairs()
        unusual = self.has_unusual_bonds()

        if RDKIT_AVAILABLE:
            if self.chem_mol is not None and not unusual:
                self.validation_state = "valid"
                notes.insert(0, "No valence or sanitization errors detected by RDKit.")
            else:
                self.validation_state = "invalid"
                if self.chem_error:
                    self.invalid_atom_indices.update(self._heuristic_suspects())
                    notes.insert(0, self._friendly_rdkit_issue(self.chem_error))
                    notes.append("Suggestion (not applied): review bond order and formal charge at the flagged atom.")
                if unusual:
                    notes.insert(0, "An unusual bond was drawn (multiple bond to H, or between halogens).")
                if not self.invalid_atom_indices:
                    self.invalid_atom_indices.update(self._heuristic_suspects())
        else:
            suspects = self._heuristic_suspects()
            if unusual or suspects:
                self.validation_state = "invalid"
                notes.insert(0, "Basic valence heuristics flagged atom(s): " +
                             (", ".join(str(i + 1) for i in sorted(suspects)) or "unusual bond") + ".")
                self.invalid_atom_indices.update(suspects)
            else:
                self.validation_state = "limited"
                notes.insert(0, "No obvious valence issue found; this is not a full validation.")
            notes.append("Install RDKit for full validation, aromaticity handling and canonical SMILES.")

        if overlaps:
            notes.append(f"Drawing note: {len(overlaps)} atom pair(s) overlap. Consider moving a fragment.")
        notes.append("No atoms, bonds, positions or charges were changed by this check.")
        self.validation_notes = notes
        self._redraw_canvas(refresh_chemistry=False)
        self._set_diagnostics(notes)
        self._set_status({"valid": "Check complete: chemistry checks passed.",
                          "limited": "Basic checks complete. Install RDKit for full validation.",
                          "invalid": "Check complete: review the suggestions in the right panel."}
                         [self.validation_state])

    def calculate_molecular_formula(self):
        if not self.atoms:
            return "—"
        if RDKIT_AVAILABLE:
            if self.chem_mol is None:
                return "Unavailable until structure passes checks"
            return rdMolDescriptors.CalcMolFormula(self.chem_mol)
        counts = defaultdict(int)
        for a in self.atoms:
            counts[a.element] += 1
            counts["H"] += a.implicit_h
        parts = []
        for el in ("C", "H"):
            if counts.get(el):
                parts.append(el + (str(counts[el]) if counts[el] > 1 else ""))
                counts.pop(el)
        for el in sorted(counts):
            if counts[el]:
                parts.append(el + (str(counts[el]) if counts[el] > 1 else ""))
        return "~" + "".join(parts)

    def calculate_molecular_weight(self):
        if not self.atoms:
            return None
        if RDKIT_AVAILABLE:
            return round(float(Descriptors.MolWt(self.chem_mol)), 2) if self.chem_mol is not None else None
        total = sum(ATOMIC_WEIGHTS.get(a.element, 0.0) + a.implicit_h * ATOMIC_WEIGHTS["H"]
                    for a in self.atoms)
        return round(total, 2)

    def generate_smiles(self):
        if not self.atoms:
            return "—"
        if not RDKIT_AVAILABLE:
            return "Install RDKit for SMILES"
        if self.chem_mol is None:
            return "Unavailable — check structure"
        return Chem.MolToSmiles(self.chem_mol, canonical=True)

    # ---------------------------------------------- clean up / import / export
    def _molecule_with_coords(self):
        """RDKit mol carrying the drawn 2D coordinates (screen y flipped)."""
        if self.chem_mol is None:
            return None
        mol = Chem.Mol(self.chem_mol)
        mol.RemoveAllConformers()
        conf = Chem.Conformer(mol.GetNumAtoms())
        s = 1.5 / self.BOND_LENGTH
        for i, a in enumerate(self.atoms):
            conf.SetAtomPosition(i, (a.x * s, -a.y * s, 0.0))
        mol.AddConformer(conf)
        return mol

    def clean_up(self):
        """ChemDraw-style 'Clean Up Structure' using RDKit 2D coordinates (user-triggered)."""
        if not RDKIT_AVAILABLE:
            messagebox.showinfo("Clean up", "Install RDKit to use Clean up.", parent=self.root)
            return
        self._refresh_chemistry_cache()
        if self.chem_mol is None:
            messagebox.showwarning("Clean up", "Fix the structure first (Check structure).", parent=self.root)
            return
        mol = Chem.Mol(self.chem_mol)
        AllChem.Compute2DCoords(mol)
        conf = mol.GetConformer()
        pts = [conf.GetAtomPosition(i) for i in range(mol.GetNumAtoms())]
        s = self.BOND_LENGTH / 1.5
        ox = sum(a.x for a in self.atoms) / len(self.atoms)
        oy = sum(a.y for a in self.atoms) / len(self.atoms)
        mx = sum(p.x for p in pts) / len(pts)
        my = sum(p.y for p in pts) / len(pts)
        self.save_state()
        for a, p in zip(self.atoms, pts):
            a.x = ox + (p.x - mx) * s
            a.y = oy - (p.y - my) * s
        self._invalidate_validation()
        self._redraw_canvas()
        self._set_status("Structure cleaned up with RDKit 2D layout. Use Undo to revert.")

    def import_smiles(self):
        if not RDKIT_AVAILABLE:
            messagebox.showinfo("Import SMILES", "Install RDKit to import SMILES.", parent=self.root)
            return
        text = simpledialog.askstring("Import SMILES", "SMILES:", parent=self.root)
        if not text:
            return
        mol = Chem.MolFromSmiles(text.strip())
        if mol is None:
            messagebox.showerror("Import SMILES", "Could not parse that SMILES.", parent=self.root)
            return
        AllChem.Compute2DCoords(mol)
        Chem.Kekulize(mol, clearAromaticFlags=True)
        conf = mol.GetConformer()
        w, h = self._canvas_size()
        pts = [conf.GetAtomPosition(i) for i in range(mol.GetNumAtoms())]
        mx = sum(p.x for p in pts) / len(pts)
        my = sum(p.y for p in pts) / len(pts)
        s = self.BOND_LENGTH / 1.5
        self.save_state()
        new = []
        for rd, p in zip(mol.GetAtoms(), pts):
            a = Atom(w / 2 + (p.x - mx) * s, h / 2 - (p.y - my) * s,
                     rd.GetSymbol(), rd.GetFormalCharge())
            self.atoms.append(a)
            new.append(a)
        for b in mol.GetBonds():
            order = {Chem.BondType.SINGLE: 1, Chem.BondType.DOUBLE: 2,
                     Chem.BondType.TRIPLE: 3}.get(b.GetBondType(), 1)
            self.bonds.append(Bond(new[b.GetBeginAtomIdx()], new[b.GetEndAtomIdx()], order))
        self.selected_atoms = set(new)
        self._invalidate_validation()
        self._redraw_canvas()
        self._set_status("SMILES imported.")

    def export_molfile(self):
        if not RDKIT_AVAILABLE:
            messagebox.showinfo("Export", "Install RDKit to export .mol files.", parent=self.root)
            return
        self._refresh_chemistry_cache()
        mol = self._molecule_with_coords()
        if mol is None:
            messagebox.showwarning("Export", "Nothing valid to export. Run Check structure.", parent=self.root)
            return
        path = filedialog.asksaveasfilename(defaultextension=".mol",
                                            filetypes=[("MDL Molfile", "*.mol"), ("All files", "*.*")],
                                            parent=self.root)
        if path:
            with open(path, "w", encoding="utf-8") as fh:
                fh.write(Chem.MolToMolBlock(mol))
            self._set_status(f"Exported {path}")

    # ---------------------------------------------------------------- geometry
    def _canvas_size(self):
        return max(self.canvas.winfo_width(), 400), max(self.canvas.winfo_height(), 300)

    def find_atom_at(self, x, y, radius=None):
        radius = self.ATOM_HIT_RADIUS if radius is None else radius
        for atom in reversed(self.atoms):
            if atom.distance_to(x, y) <= radius:
                return atom
        return None

    @staticmethod
    def point_near_line(px, py, x1, y1, x2, y2, threshold=6):
        dx, dy = x2 - x1, y2 - y1
        l2 = dx * dx + dy * dy
        if l2 < 1e-9:
            return math.hypot(px - x1, py - y1) < threshold
        t = max(0.0, min(1.0, ((px - x1) * dx + (py - y1) * dy) / l2))
        return math.hypot(px - (x1 + t * dx), py - (y1 + t * dy)) < threshold

    def find_bond_at(self, x, y, threshold=7):
        for bond in reversed(self.bonds):
            if self.point_near_line(x, y, bond.atom1.x, bond.atom1.y,
                                    bond.atom2.x, bond.atom2.y, threshold):
                return bond
        return None

    def find_annotation_at(self, x, y):
        for an in reversed(self.annotations):
            if an.kind in ("plus", "equals", "text"):
                w = max(18, len(an.text or an.kind) * 8)
                if abs(x - an.x1) <= w / 2 + 5 and abs(y - an.y1) <= 17:
                    return an
            elif an.kind == "equilibrium":
                if (self.point_near_line(x, y, an.x1, an.y1 - 3, an.x2, an.y2 - 3, 9) or
                        self.point_near_line(x, y, an.x2, an.y2 + 3, an.x1, an.y1 + 3, 9)):
                    return an
            elif self.point_near_line(x, y, an.x1, an.y1, an.x2, an.y2, 9):
                return an
        return None

    def snap_angle(self, x1, y1, x2, y2):
        dx, dy = x2 - x1, y2 - y1
        length = math.hypot(dx, dy)
        if length < 0.001:
            return x2, y2
        angle = math.degrees(math.atan2(dy, dx)) % 360
        nearest = min(self.SNAP_ANGLES, key=lambda c: abs((angle - c + 180) % 360 - 180))
        r = math.radians(nearest)
        return x1 + length * math.cos(r), y1 + length * math.sin(r)

    def _fixed_end(self, sx, sy, x, y, ignore=None):
        """Fixed-length, 30-degree-snapped endpoint; snaps onto an existing atom if released on one."""
        target = self.find_atom_at(x, y)
        if target is not None and target is not ignore:
            return target.x, target.y
        px, py = self.snap_angle(sx, sy, x, y)
        d = math.hypot(px - sx, py - sy) or 1.0
        return sx + self.BOND_LENGTH * (px - sx) / d, sy + self.BOND_LENGTH * (py - sy) / d

    def _clearance(self, x, y, exclude=()):
        return min((math.hypot(x - o.x, y - o.y) for o in self.atoms if o not in exclude),
                   default=1e9)

    def _auto_direction(self, atom):
        """Best free direction for a new bond: zigzag for 1 neighbour, widest-gap bisector otherwise."""
        L = self.BOND_LENGTH
        nbrs = atom.neighbors()
        if not nbrs:
            r = math.radians(-30)
            return math.cos(r), math.sin(r)
        angs = sorted(math.degrees(math.atan2(n.y - atom.y, n.x - atom.x)) % 360 for n in nbrs)
        if len(angs) == 1:
            cands = [angs[0] + 120, angs[0] - 120]
        else:
            gaps = [(((angs[(i + 1) % len(angs)] - angs[i]) % 360) or 360, angs[i])
                    for i in range(len(angs))]
            gap, start = max(gaps)
            cands = [start + gap / 2]
            if len(angs) >= 3:
                cands.append(start + gap / 2 + 0.01)

        def score(a):
            r = math.radians(a)
            return self._clearance(atom.x + L * math.cos(r), atom.y + L * math.sin(r), (atom,))
        best = math.radians(max(cands, key=score))
        return math.cos(best), math.sin(best)

    def on_mouse_motion(self, event):
        self.last_canvas_pos = (event.x, event.y)

    # ----------------------------------------------------------- tool / keys
    def _tool_changed(self):
        self.draw_start = self.draw_atom = self.draw_bond = None
        cursor = {"select": "arrow", "move": "fleur", "erase": "X_cursor"}.get(self.tool.get(), "crosshair")
        self.canvas.configure(cursor=cursor)
        self._update_tool_status()

    def _canvas_has_focus(self):
        try:
            return self.root.focus_get() in (self.canvas, self.root)
        except (tk.TclError, KeyError):
            return True

    def _element_key(self, element):
        if not self._canvas_has_focus():
            return
        x, y = self.last_canvas_pos
        atom = self.find_atom_at(x, y)
        if atom is not None:
            if atom.element != element:
                self.save_state()
                atom.element = element
                self._invalidate_validation()
                self._redraw_canvas()
                self._set_status(f"Atom changed to {element}.")
        else:
            self.selected_element.set(element)

    def _bond_key(self, order):
        if not self._canvas_has_focus():
            return
        x, y = self.last_canvas_pos
        bond = self.find_bond_at(x, y) if self.find_atom_at(x, y) is None else None
        if bond is not None and bond.order != order:
            self.save_state()
            bond.order = order
            self._invalidate_validation()
            self._redraw_canvas()
        else:
            self.bond_order.set(order)

    def _update_tool_status(self):
        self._set_status(self.TOOL_HELP.get(self.tool.get(), ""))

    def _set_status(self, text):
        self.status_label.config(text=text)

    # ------------------------------------------------------------ mouse events
    def on_click(self, event):
        self.canvas.focus_set()
        self.last_canvas_pos = (event.x, event.y)
        mode = self.tool.get()

        if mode in ("arrow", "equilibrium"):
            self.annotation_start = (event.x, event.y)
            self._draw_annotation_preview(event.x, event.y)
            return
        if mode in ("plus", "equals"):
            self.save_state()
            self.annotations.append(Annotation(mode, event.x, event.y,
                                               text="+" if mode == "plus" else "="))
            self._redraw_canvas(refresh_chemistry=False)
            return
        if mode == "text":
            label = simpledialog.askstring("Reaction label", "Text or condition to place:",
                                           parent=self.root)
            if label and label.strip():
                self.save_state()
                self.annotations.append(Annotation("text", event.x, event.y, text=label.strip()))
                self._redraw_canvas(refresh_chemistry=False)
            return

        atom = self.find_atom_at(event.x, event.y)
        bond = None if atom else self.find_bond_at(event.x, event.y)
        annotation = None if (atom or bond) else self.find_annotation_at(event.x, event.y)

        if mode == "draw":
            self.draw_start = (event.x, event.y)
            self.draw_atom, self.draw_bond, self.draw_moved = atom, bond, False
            self.selected_atoms = {atom} if atom else set()
            self.selected_bond = None
            self.selected_annotation = None
            self._redraw_canvas(refresh_chemistry=False)

        elif mode == "select":
            shift = bool(event.state & 0x0001)
            if atom is not None:
                if shift:
                    self.selected_atoms ^= {atom}
                else:
                    self.selected_atoms = {atom}
                self.selected_bond = self.selected_annotation = None
            elif bond is not None:
                self.selected_atoms.clear()
                self.selected_bond, self.selected_annotation = bond, None
            elif annotation is not None:
                self.selected_atoms.clear()
                self.selected_bond, self.selected_annotation = None, annotation
            else:
                if not shift:
                    self.selected_atoms.clear()
                self.selected_bond = self.selected_annotation = None
                self.rubber_start = (event.x, event.y)
                self.rubber_shift = shift
            self._redraw_canvas(refresh_chemistry=False)

        elif mode == "erase":
            if atom or bond or annotation:
                self.save_state()
                self._delete_object(atom=atom, bond=bond, annotation=annotation)
                self._invalidate_validation()
                self._redraw_canvas()

        elif mode == "move":
            self.move_last = (event.x, event.y)
            self.move_undo_saved = False
            self.move_before_state = self._capture_state()
            self.moving_annotation = None
            self.move_component = []
            anchor = atom or (bond.atom1 if bond else None)
            if anchor is not None:
                if anchor in self.selected_atoms and len(self.selected_atoms) > 1:
                    self.move_component = list(self.selected_atoms)
                else:
                    self.selected_atoms = {anchor}
                    self.move_component = self.get_connected_component(anchor)
                self.selected_bond = self.selected_annotation = None
            elif annotation is not None:
                self.selected_atoms.clear()
                self.selected_bond = None
                self.selected_annotation = self.moving_annotation = annotation
            else:
                self.selected_atoms.clear()
                self.selected_bond = self.selected_annotation = None
            self._redraw_canvas(refresh_chemistry=False)

    def on_drag(self, event):
        self.last_canvas_pos = (event.x, event.y)
        mode = self.tool.get()

        if self.annotation_start is not None and mode in ("arrow", "equilibrium"):
            self._draw_annotation_preview(event.x, event.y)
            return

        if mode == "draw" and self.draw_start is not None:
            if math.hypot(event.x - self.draw_start[0], event.y - self.draw_start[1]) > 5:
                self.draw_moved = True
            if self.draw_moved:
                sx, sy = ((self.draw_atom.x, self.draw_atom.y) if self.draw_atom
                          else self.draw_start)
                ex, ey = self._fixed_end(sx, sy, event.x, event.y, self.draw_atom)
                self._clear_temp_preview()
                self.temp_ids.append(self.canvas.create_line(
                    sx, sy, ex, ey, fill="#7A8699", dash=(4, 3), width=2))

        elif mode == "select" and self.rubber_start is not None:
            self._clear_temp_preview()
            x0, y0 = self.rubber_start
            self.temp_ids.append(self.canvas.create_rectangle(
                x0, y0, event.x, event.y, outline="#2674D9", dash=(3, 3)))

        elif mode == "move" and self.move_last is not None:
            dx, dy = event.x - self.move_last[0], event.y - self.move_last[1]
            if dx or dy:
                if not self.move_undo_saved:
                    self._push_snapshot(self.move_before_state)
                    self.move_undo_saved = True
                if self.moving_annotation is not None:
                    self.moving_annotation.move_by(dx, dy)
                else:
                    for a in self.move_component:
                        a.x += dx
                        a.y += dy
                self.move_last = (event.x, event.y)
                self._redraw_canvas(refresh_chemistry=False)

    def on_release(self, event):
        self.last_canvas_pos = (event.x, event.y)
        mode = self.tool.get()

        if self.annotation_start is not None and mode in ("arrow", "equilibrium"):
            x1, y1 = self.annotation_start
            self._clear_temp_preview()
            self.annotation_start = None
            if math.hypot(event.x - x1, event.y - y1) >= 20:
                self.save_state()
                self.annotations.append(Annotation(mode, x1, y1, event.x, event.y))
                self._redraw_canvas(refresh_chemistry=False)
            return

        self._clear_temp_preview()

        if mode == "draw" and self.draw_start is not None:
            self._finish_draw(event)
        elif mode == "select" and self.rubber_start is not None:
            x0, y0 = self.rubber_start
            lo_x, hi_x = sorted((x0, event.x))
            lo_y, hi_y = sorted((y0, event.y))
            if hi_x - lo_x > 4 or hi_y - lo_y > 4:
                inside = {a for a in self.atoms if lo_x <= a.x <= hi_x and lo_y <= a.y <= hi_y}
                self.selected_atoms = (self.selected_atoms | inside) if self.rubber_shift else inside
            self.rubber_start = None
            self._redraw_canvas(refresh_chemistry=False)
        elif mode == "move":
            if self.move_undo_saved:
                self._invalidate_validation()
                self._redraw_canvas(refresh_chemistry=False)
                self._set_status("Moved. Run Check structure to refresh the review.")
            self.move_component = []
            self.move_last = self.move_before_state = self.moving_annotation = None
            self.move_undo_saved = False

    # ---------------------------------------------------- ChemDraw draw logic
    def _link(self, a1, a2):
        if a1 is a2:
            return
        old = next((b for b in a1.bonds if b.other(a1) is a2), None)
        if old is not None:
            old.order = self.bond_order.get()
        else:
            self.bonds.append(Bond(a1, a2, self.bond_order.get()))

    def _new_atom(self, x, y, element=None):
        atom = Atom(x, y, element or self.selected_element.get())
        self.atoms.append(atom)
        return atom

    def _finish_draw(self, event):
        atom, bond, moved = self.draw_atom, self.draw_bond, self.draw_moved
        x0, y0 = self.draw_start
        self.draw_start = self.draw_atom = self.draw_bond = None
        L = self.BOND_LENGTH
        self.save_state()
        focus = None

        if moved:
            a1 = atom or self._new_atom(x0, y0)
            ex, ey = self._fixed_end(a1.x, a1.y, event.x, event.y, a1)
            a2 = self.find_atom_at(ex, ey, 10) or self._new_atom(ex, ey)
            self._link(a1, a2)
            focus = a2
        elif atom is not None:
            ux, uy = self._auto_direction(atom)
            tx, ty = atom.x + L * ux, atom.y + L * uy
            focus = self.find_atom_at(tx, ty, 10) or self._new_atom(tx, ty)
            self._link(atom, focus)
        elif bond is not None:
            bond.order = bond.order % 3 + 1
            self.selected_bond = bond
        else:
            r = math.radians(-30)
            a1 = self._new_atom(x0, y0)
            focus = self._new_atom(x0 + L * math.cos(r), y0 + L * math.sin(r))
            self._link(a1, focus)

        self.selected_atoms = {focus} if focus else set()
        self._invalidate_validation()
        self._redraw_canvas()

    def _draw_annotation_preview(self, x2, y2):
        self._clear_temp_preview()
        if self.annotation_start is None:
            return
        x1, y1 = self.annotation_start
        if self.tool.get() == "equilibrium":
            self.temp_ids.append(self.canvas.create_line(x1, y1 - 3, x2, y2 - 3, arrow=tk.LAST,
                                                         width=2, fill="#7A8699", dash=(4, 3)))
            self.temp_ids.append(self.canvas.create_line(x2, y2 + 3, x1, y1 + 3, arrow=tk.LAST,
                                                         width=2, fill="#7A8699", dash=(4, 3)))
        else:
            self.temp_ids.append(self.canvas.create_line(x1, y1, x2, y2, arrow=tk.LAST,
                                                         width=2, fill="#7A8699", dash=(4, 3)))

    def _clear_temp_preview(self):
        for i in self.temp_ids:
            self.canvas.delete(i)
        self.temp_ids = []

    def on_right_click(self, event):
        atom = self.find_atom_at(event.x, event.y)
        bond = None if atom else self.find_bond_at(event.x, event.y)
        annotation = None if (atom or bond) else self.find_annotation_at(event.x, event.y)
        if atom or bond or annotation:
            self.save_state()
            self._delete_object(atom=atom, bond=bond, annotation=annotation)
            self._invalidate_validation()
            self._redraw_canvas()

    def cancel_pending(self):
        self.draw_start = self.draw_atom = self.draw_bond = None
        self.annotation_start = None
        self.rubber_start = None
        self.move_component = []
        self.move_last = self.moving_annotation = None
        self.selected_atoms.clear()
        self.selected_bond = self.selected_annotation = None
        self._clear_temp_preview()
        self._redraw_canvas(refresh_chemistry=False)
        self._set_status("Cancelled pending action and cleared selection.")

    def select_all(self):
        if self._canvas_has_focus():
            self.selected_atoms = set(self.atoms)
            self.selected_bond = self.selected_annotation = None
            self._redraw_canvas(refresh_chemistry=False)

    # ---------------------------------------------------------- rings & groups
    def _anchor_atom(self):
        if len(self.selected_atoms) == 1:
            atom = next(iter(self.selected_atoms))
            if atom in self.atoms:
                return atom
        return None

    def _free_origin(self, x, y, radius_needed):
        """Spiral outward from (x, y) until a ring/group fits without overlapping atoms."""
        for r in (0, 40, 80, 120, 160):
            steps = 1 if r == 0 else 12
            for i in range(steps):
                a = math.radians(i * 360 / steps)
                px, py = x + r * math.cos(a), y + r * math.sin(a)
                if self._clearance(px, py) > radius_needed:
                    return px, py
        return x, y

    def add_ring(self, size, aromatic=False):
        bond = self.selected_bond if self.selected_bond in self.bonds else None
        if bond is not None:
            self._fuse_ring(bond, size, aromatic)
            return
        L = self.BOND_LENGTH
        R = L / (2 * math.sin(math.pi / size))
        anchor = self._anchor_atom()
        if anchor is not None:
            ux, uy = self._auto_direction(anchor)
            cx = anchor.x + (L + R) * ux
            cy = anchor.y + (L + R) * uy
            start = math.atan2(uy, ux) + math.pi
        else:
            x, y = self.last_canvas_pos
            w, h = self._canvas_size()
            if x < 5 or y < 5:
                x, y = w / 2, h / 2
            cx, cy = self._free_origin(x, y, R + 15)
            start = -math.pi / 2

        self.save_state()
        ring = []
        for i in range(size):
            ang = start + i * 2 * math.pi / size
            px, py = cx + R * math.cos(ang), cy + R * math.sin(ang)
            existing = self.find_atom_at(px, py, 8)
            ring.append(existing or self._new_atom(px, py, "C"))
        self._close_ring(ring, aromatic)
        if anchor is not None and ring[0] is not anchor:
            if not any(b.other(anchor) is ring[0] for b in anchor.bonds):
                self.bonds.append(Bond(anchor, ring[0], 1))
        self.selected_atoms = {ring[0]}
        self.selected_bond = self.selected_annotation = None
        self.tool.set("draw")
        self._tool_changed()
        self._invalidate_validation()
        self._redraw_canvas()
        self._set_status("Ring placed. No existing atoms were moved.")

    def _close_ring(self, ring, aromatic):
        n = len(ring)
        for i in range(n):
            a, b = ring[i], ring[(i + 1) % n]
            if a is b or any(bd.other(a) is b for bd in a.bonds):
                continue
            self.bonds.append(Bond(a, b, 2 if aromatic and i % 2 == 0 else 1))

    def _fuse_ring(self, bond, size, aromatic):
        """Fuse a new ring onto the selected bond, on the less crowded side."""
        a, b = bond.atom1, bond.atom2
        L = self.BOND_LENGTH
        mx, my = (a.x + b.x) / 2, (a.y + b.y) / 2
        dx, dy = (b.x - a.x) / L, (b.y - a.y) / L
        nx, ny = -dy, dx
        apo = L / (2 * math.tan(math.pi / size))
        R = L / (2 * math.sin(math.pi / size))

        def centre(s):
            return mx + s * nx * apo, my + s * ny * apo

        def crowd(s):
            cx, cy = centre(s)
            return sum(math.hypot(o.x - cx, o.y - cy) < R * 0.9 for o in self.atoms if o not in (a, b))

        side = min((1, -1), key=crowd)
        cx, cy = centre(side)
        a0 = math.atan2(a.y - cy, a.x - cx)
        cross = (b.x - cx) * (a.y - cy) - (b.y - cy) * (a.x - cx)
        step = 2 * math.pi / size * (1 if cross < 0 else -1)
        self.save_state()
        ring = [a]
        for i in range(1, size):
            ang = a0 + i * step
            px, py = cx + R * math.cos(ang), cy + R * math.sin(ang)
            if math.hypot(px - b.x, py - b.y) < 4:
                ring.append(b)
            else:
                ring.append(self.find_atom_at(px, py, 8) or self._new_atom(px, py, "C"))
        self._close_ring(ring, aromatic and False)
        if aromatic:
            self._apply_kekule(ring)
        self.selected_bond = None
        self.selected_atoms = {ring[-1]}
        self._invalidate_validation()
        self._redraw_canvas()
        self._set_status("Ring fused onto the selected bond.")

    def _apply_kekule(self, ring):
        """Alternate double bonds around a ring, skipping bonds that already exist as double."""
        n = len(ring)
        bonds = []
        for i in range(n):
            a, b = ring[i], ring[(i + 1) % n]
            bd = next((x for x in a.bonds if x.other(a) is b), None)
            if bd is not None:
                bonds.append(bd)
        free = [bd for bd in bonds if bd.atom1.bond_order_sum() <= 3 and bd.atom2.bond_order_sum() <= 3]
        for i, bd in enumerate(bonds):
            if i % 2 == 0 and bd in free and all(
                    x.order == 1 for x in bd.atom1.bonds + bd.atom2.bonds):
                bd.order = 2

    GROUPS = {"CH3": [("C", 0)], "OH": [("O", 0)], "NH2": [("N", 0)]}

    def add_functional_group(self, group_type):
        L = self.BOND_LENGTH
        anchor = self._anchor_atom()
        if anchor is not None:
            ux, uy = self._auto_direction(anchor)
            gx, gy = anchor.x + L * ux, anchor.y + L * uy
        else:
            x, y = self.last_canvas_pos
            w, h = self._canvas_size()
            if x < 5 or y < 5:
                x, y = w / 2, h / 2
            gx, gy = self._free_origin(x, y, L)
            ux, uy = 1.0, 0.0
        ang = math.atan2(uy, ux)

        self.save_state()
        if group_type in self.GROUPS:
            focus = self._new_atom(gx, gy, self.GROUPS[group_type][0][0])
        elif group_type == "COOH":
            focus = self._new_atom(gx, gy, "C")
            o1 = self._new_atom(gx + L * math.cos(ang + math.pi / 3),
                                gy + L * math.sin(ang + math.pi / 3), "O")
            o2 = self._new_atom(gx + L * math.cos(ang - math.pi / 3),
                                gy + L * math.sin(ang - math.pi / 3), "O")
            self.bonds.append(Bond(focus, o1, 2))
            self.bonds.append(Bond(focus, o2, 1))
        else:
            return
        if anchor is not None:
            self.bonds.append(Bond(anchor, focus, 1))
        self.selected_atoms = {focus}
        self.selected_bond = self.selected_annotation = None
        self.tool.set("draw")
        self._tool_changed()
        self._invalidate_validation()
        self._redraw_canvas()
        self._set_status("Functional group placed. Bonds and charges were not auto-corrected.")

    def apply_charge(self):
        selected = [a for a in self.atoms if a in self.selected_atoms]
        if not selected:
            messagebox.showinfo("Formal charge", "Select one or more atoms first.", parent=self.root)
            return
        try:
            charge = int(self.charge_value.get())
        except (ValueError, tk.TclError):
            messagebox.showerror("Formal charge", "Enter an integer from -3 to +3.", parent=self.root)
            return
        if not -3 <= charge <= 3:
            messagebox.showerror("Formal charge", "Charge must be between -3 and +3.", parent=self.root)
            return
        self.save_state()
        for a in selected:
            a.charge = charge
        self._invalidate_validation()
        self._redraw_canvas()
        self._set_status("Formal charge changed. Run Check structure to review it.")

    # ------------------------------------------------------------- rendering
    def _redraw_canvas(self, refresh_chemistry=True):
        if refresh_chemistry:
            self._refresh_chemistry_cache()
        self.canvas.delete("all")
        for an in self.annotations:
            self._draw_annotation(an)
        for bond in self.bonds:
            self._draw_bond(bond)
        index = {a: i for i, a in enumerate(self.atoms)}
        for atom in self.atoms:
            self._draw_atom(atom, index[atom])
        self._update_panel()

    def _atom_has_label(self, atom):
        return atom.element != "C" or not atom.bonds or atom.charge != 0

    def _atom_label(self, atom):
        text = atom.element
        if atom.element != "H" and atom.implicit_h > 0:
            text += "H" + (str(atom.implicit_h).translate(SUBSCRIPTS) if atom.implicit_h > 1 else "")
        if atom.charge:
            mag = abs(atom.charge)
            text += (str(mag).translate(SUBSCRIPTS) if mag > 1 else "") + ("+" if atom.charge > 0 else "−")
        return text

    def _draw_atom(self, atom, idx):
        selected = atom in self.selected_atoms
        suspect = idx in self.invalid_atom_indices and self.validation_state == "invalid"
        if self._atom_has_label(atom):
            label = self._atom_label(atom)
            width = max(15, 4.7 * len(label) + 7)
            self.canvas.create_oval(atom.x - width / 2, atom.y - 11, atom.x + width / 2,
                                    atom.y + 11, fill="white", outline="white")
            self.canvas.create_text(atom.x, atom.y, text=label, font=("Arial", 11, "bold"),
                                    fill="#B42318" if suspect else "#202124")
        elif suspect:
            self.canvas.create_oval(atom.x - 6, atom.y - 6, atom.x + 6, atom.y + 6,
                                    outline="#B42318", width=2)
        if selected:
            r = 13 if self._atom_has_label(atom) else 8
            self.canvas.create_oval(atom.x - r, atom.y - r, atom.x + r, atom.y + r,
                                    outline="#2674D9", width=2)

    def _bond_endpoints(self, bond):
        a, b = bond.atom1, bond.atom2
        dx, dy = b.x - a.x, b.y - a.y
        length = math.hypot(dx, dy)
        if length < 1e-6:
            return a.x, a.y, b.x, b.y, 0.0, 0.0, 0.0
        ux, uy = dx / length, dy / length
        oa = 10 if self._atom_has_label(a) else 0
        ob = 10 if self._atom_has_label(b) else 0
        return a.x + ux * oa, a.y + uy * oa, b.x - ux * ob, b.y - uy * ob, ux, uy, length

    def _ring_path(self, bond):
        """Shortest ring (list of atoms) containing this bond, or None if it is acyclic."""
        a, b = bond.atom1, bond.atom2
        parent = {a: None}
        queue = [a]
        while queue:
            cur = queue.pop(0)
            for bd in cur.bonds:
                if bd is bond:
                    continue
                nxt = bd.other(cur)
                if nxt in parent:
                    continue
                parent[nxt] = cur
                if nxt is b:
                    path, node = [], b
                    while node is not None:
                        path.append(node)
                        node = parent[node]
                    return path if len(path) <= 8 else None
                queue.append(nxt)
        return None

    def _double_bond_side(self, bond):
        """+1/-1 puts the second line on the ring-inner side; 0 keeps it centred."""
        path = self._ring_path(bond)
        if not path:
            return 0
        cx = sum(p.x for p in path) / len(path)
        cy = sum(p.y for p in path) / len(path)
        _, _, _, _, ux, uy, _ = self._bond_endpoints(bond)
        px, py = -uy, ux
        a = bond.atom1
        return 1 if ((cx - a.x) * px + (cy - a.y) * py) > 0 else -1

    def _draw_bond(self, bond):
        x1, y1, x2, y2, ux, uy, length = self._bond_endpoints(bond)
        if length < 1e-6:
            return
        selected = bond is self.selected_bond
        colour = "#2674D9" if selected else "#202124"
        width = 3 if selected else 2
        px, py = -uy, ux
        line = lambda ax, ay, bx, by: self.canvas.create_line(
            ax, ay, bx, by, fill=colour, width=width, capstyle=tk.ROUND)
        if bond.order == 1:
            line(x1, y1, x2, y2)
        elif bond.order == 2:
            side = self._double_bond_side(bond)
            if side == 0:
                o = 3.0
                line(x1 + px * o, y1 + py * o, x2 + px * o, y2 + py * o)
                line(x1 - px * o, y1 - py * o, x2 - px * o, y2 - py * o)
            else:
                o, trim = 6.0 * side, min(6.0, length * 0.15)
                line(x1, y1, x2, y2)
                line(x1 + px * o + ux * trim, y1 + py * o + uy * trim,
                     x2 + px * o - ux * trim, y2 + py * o - uy * trim)
        elif bond.order == 3:
            o = 4.2
            line(x1, y1, x2, y2)
            line(x1 + px * o, y1 + py * o, x2 + px * o, y2 + py * o)
            line(x1 - px * o, y1 - py * o, x2 - px * o, y2 - py * o)

    def _draw_annotation(self, an):
        selected = an is self.selected_annotation
        colour = "#2674D9" if selected else "#202124"
        width = 2.5 if selected else 2
        if an.kind == "arrow":
            self.canvas.create_line(an.x1, an.y1, an.x2, an.y2, arrow=tk.LAST, width=width,
                                    fill=colour, capstyle=tk.ROUND)
        elif an.kind == "equilibrium":
            self.canvas.create_line(an.x1, an.y1 - 3, an.x2, an.y2 - 3, arrow=tk.LAST,
                                    width=width, fill=colour)
            self.canvas.create_line(an.x2, an.y2 + 3, an.x1, an.y1 + 3, arrow=tk.LAST,
                                    width=width, fill=colour)
        else:
            content = an.text or ("+" if an.kind == "plus" else "=")
            size = 24 if an.kind in ("plus", "equals") else 12
            self.canvas.create_text(an.x1, an.y1, text=content, fill=colour,
                                    font=("Arial", size, "bold" if an.kind != "text" else "normal"),
                                    justify=tk.CENTER)

    # --------------------------------------------------------------- deletion
    def _delete_object(self, atom=None, bond=None, annotation=None):
        if atom is not None and atom in self.atoms:
            for attached in list(atom.bonds):
                self._delete_bond(attached)
            self.atoms.remove(atom)
            self.selected_atoms.discard(atom)
        elif bond is not None:
            self._delete_bond(bond)
        elif annotation is not None and annotation in self.annotations:
            self.annotations.remove(annotation)
            if self.selected_annotation is annotation:
                self.selected_annotation = None

    def _delete_bond(self, bond):
        for a in (bond.atom1, bond.atom2):
            if bond in a.bonds:
                a.bonds.remove(bond)
        if bond in self.bonds:
            self.bonds.remove(bond)
        if self.selected_bond is bond:
            self.selected_bond = None

    def delete_selected(self):
        if not self._canvas_has_focus():
            return
        if self.selected_atoms:
            self.save_state()
            for atom in list(self.selected_atoms):
                self._delete_object(atom=atom)
            self.selected_atoms.clear()
        elif self.selected_bond is not None:
            self.save_state()
            self._delete_bond(self.selected_bond)
        elif self.selected_annotation is not None:
            self.save_state()
            self._delete_object(annotation=self.selected_annotation)
        else:
            return
        self._invalidate_validation()
        self._redraw_canvas()

    def clear_all(self):
        if not self.atoms and not self.annotations:
            return
        if not messagebox.askyesno("Clear drawing", "Clear all atoms, bonds and reaction annotations?",
                                   parent=self.root):
            return
        self.save_state()
        self.atoms.clear()
        self.bonds.clear()
        self.annotations.clear()
        self.selected_atoms.clear()
        self.selected_bond = self.selected_annotation = None
        self._invalidate_validation()
        self._redraw_canvas()

    # ------------------------------------------------------------ connectivity
    def get_connected_component(self, start):
        if start not in self.atoms:
            return []
        seen, stack, out = {start}, [start], []
        while stack:
            cur = stack.pop()
            out.append(cur)
            for n in cur.neighbors():
                if n not in seen:
                    seen.add(n)
                    stack.append(n)
        return out

    def get_connected_components(self):
        comps, seen = [], set()
        for atom in self.atoms:
            if atom not in seen:
                comp = self.get_connected_component(atom)
                comps.append(comp)
                seen.update(comp)
        return comps

    def _overlapping_atom_pairs(self):
        return [(i, j) for i, a in enumerate(self.atoms)
                for j in range(i + 1, len(self.atoms))
                if a.distance_to(self.atoms[j].x, self.atoms[j].y) < 12]

    # -------------------------------------------------------------- copy/paste
    def _atoms_for_copy(self):
        if not self.selected_atoms:
            return []
        if len(self.selected_atoms) == 1:
            return self.get_connected_component(next(iter(self.selected_atoms)))
        return [a for a in self.atoms if a in self.selected_atoms]

    def copy_selection(self):
        if not self._canvas_has_focus():
            return
        if self.selected_annotation is not None:
            a = self.selected_annotation
            self.clipboard = {"type": "annotation", "annotation": (a.kind, a.x1, a.y1, a.x2, a.y2, a.text)}
            self.paste_count = 0
            self._set_status("Copied reaction annotation.")
            return
        selected = self._atoms_for_copy()
        if not selected:
            self._set_status("Select an atom/fragment or an annotation before copying.")
            return
        idx = {a: i for i, a in enumerate(selected)}
        self.clipboard = {
            "type": "molecule",
            "atoms": [(a.x, a.y, a.element, a.charge) for a in selected],
            "bonds": [(idx[b.atom1], idx[b.atom2], b.order) for b in self.bonds
                      if b.atom1 in idx and b.atom2 in idx],
        }
        self.paste_count = 0
        self._set_status(f"Copied {len(selected)} atom(s).")

    def paste_selection(self):
        if not self._canvas_has_focus() or not self.clipboard:
            return
        self.save_state()
        self.paste_count += 1
        off = 32 * self.paste_count
        if self.clipboard["type"] == "annotation":
            kind, x1, y1, x2, y2, text = self.clipboard["annotation"]
            pasted = Annotation(kind, x1 + off, y1 + off, x2 + off, y2 + off, text)
            self.annotations.append(pasted)
            self.selected_annotation = pasted
            self.selected_atoms.clear()
            self.selected_bond = None
            self._redraw_canvas(refresh_chemistry=False)
            return
        first = len(self.atoms)
        new = []
        for x, y, el, ch in self.clipboard["atoms"]:
            a = Atom(x + off, y + off, el, ch)
            self.atoms.append(a)
            new.append(a)
        for i, j, order in self.clipboard["bonds"]:
            self.bonds.append(Bond(self.atoms[first + i], self.atoms[first + j], order))
        self.selected_atoms = set(new)
        self.selected_bond = self.selected_annotation = None
        self._invalidate_validation()
        self._redraw_canvas()
        self._set_status(f"Pasted {len(new)} atom(s).")

    # ------------------------------------------------------------------ panel
    def _update_panel(self):
        formula = self.calculate_molecular_formula()
        weight = self.calculate_molecular_weight()
        if weight is None:
            wtxt = "—"
        elif not RDKIT_AVAILABLE:
            wtxt = f"~{weight} g/mol (estimate)"
        else:
            wtxt = f"{weight} g/mol"
        self.formula_label.config(text=f"Formula (all fragments): {formula}")
        self.weight_label.config(text=f"Average MW: {wtxt}")
        self.smiles_label.config(text=f"SMILES: {self.generate_smiles()}")
        self.atom_count_label.config(text=f"Atoms: {len(self.atoms)}")
        self.bond_count_label.config(text=f"Bonds: {len(self.bonds)}")
        self.fragment_count_label.config(text=f"Fragments: {len(self.get_connected_components())}")
        text, colour = {
            "unchecked": ("Not checked — click Check structure", "#5B6573"),
            "valid": ("✓ Chemistry checks passed", "#187344"),
            "limited": ("Limited checks only", "#9A6700"),
            "invalid": ("⚠ Needs review", "#B42318"),
        }[self.validation_state]
        self.validation_label.config(text=text, fg=colour)

    def _set_diagnostics(self, lines):
        self.diagnostics_text.config(state=tk.NORMAL)
        self.diagnostics_text.delete("1.0", tk.END)
        self.diagnostics_text.insert(tk.END, "\n\n".join(lines))
        self.diagnostics_text.config(state=tk.DISABLED)


def main():
    root = tk.Tk()
    MoleculeEditor(root)
    root.mainloop()


if __name__ == "__main__":
    main()
