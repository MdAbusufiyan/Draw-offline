"""A compact 2D chemical structure and reaction editor.

Core design:
- Drawn atoms/bonds are the chemistry graph.
- Reaction arrows, plus/equal signs and labels are annotations, not atoms.
- Check Structure reports problems and suggestions; it never edits the drawing.
- RDKit is optional for robust chemistry validation and molecular descriptors.

Install the chemistry backend with:
    python -m pip install rdkit
"""

from __future__ import annotations

import math
import re
import tkinter as tk
from tkinter import ttk, messagebox, simpledialog
from collections import defaultdict

try:
    from rdkit import Chem, rdBase
    from rdkit.Chem import Descriptors, rdMolDescriptors
    RDKIT_AVAILABLE = True
except ImportError:
    Chem = None
    rdBase = None
    Descriptors = None
    rdMolDescriptors = None
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

# Common, readable element colours used in skeletal drawing. Carbon and hydrogen
# remain black; a suspected-invalid atom is still highlighted separately.
ELEMENT_COLOURS = {
    "C": "#202124", "H": "#202124", "N": "#1D4ED8",
    "O": "#C62828", "S": "#9A6700", "P": "#C2410C",
    "F": "#238636", "Cl": "#238636", "Br": "#8B4513", "I": "#7E22CE",
}


class Atom:
    """One chemical atom. Coordinates are display-only; bonds define chemistry."""

    def __init__(self, x, y, element="C", charge=0):
        self.x = float(x)
        self.y = float(y)
        self.element = element
        self.charge = int(charge)
        self.bonds = []
        self.implicit_h = 0
        self.canvas_id = None
        self.text_id = None

    def distance_to(self, x, y):
        return math.hypot(self.x - x, self.y - y)

    def bond_order_sum(self):
        return sum(bond.order for bond in self.bonds)


class Bond:
    """A chemical bond between two Atom objects."""

    def __init__(self, atom1, atom2, order=1):
        self.atom1 = atom1
        self.atom2 = atom2
        self.order = int(order)
        self.canvas_ids = []
        atom1.bonds.append(self)
        atom2.bonds.append(self)


class Annotation:
    """Reaction-scheme drawing object; deliberately separate from the molecule."""

    def __init__(self, kind, x1, y1, x2=None, y2=None, text=""):
        self.kind = kind
        self.x1 = float(x1)
        self.y1 = float(y1)
        self.x2 = float(x1 if x2 is None else x2)
        self.y2 = float(y1 if y2 is None else y2)
        self.text = str(text)
        self.canvas_ids = []

    def move_by(self, dx, dy):
        self.x1 += dx
        self.y1 += dy
        self.x2 += dx
        self.y2 += dy


class MoleculeEditor:
    """Tkinter chemical structure editor with a separate reaction-annotation layer."""

    ATOM_HIT_RADIUS = 15
    BOND_LENGTH = 42.0
    SNAP_ANGLES = tuple(range(0, 360, 30))
    MIN_ATOM_GAP = 25.0

    TOOL_HELP = {
        "draw": "Draw: click blank for an atom; click an atom then a target to connect. Clicking a bond with — cycles its order; = or ≡ applies that order.",
        "atom": "Atom: choose an element, then click empty canvas to place it or an existing atom to change its element. Existing bonds are preserved.",
        "select": "Select: click an atom/bond, or drag a box around atoms. Shift-click or Shift-drag adds to selection.",
        "move": "Move: drag any selected atom to move its whole connected molecule; box-select can move several fragments.",
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
        self.root.geometry("1240x790")
        self.root.minsize(1050, 650)

        # Chemical graph
        self.atoms = []
        self.bonds = []

        # Reaction scheme objects are not part of the chemical graph.
        self.annotations = []

        # Undo/redo snapshots include both layers.
        self.undo_stack = []
        self.redo_stack = []
        self.max_undo = 100
        self.clipboard = None
        self.paste_count = 0

        # UI state
        self.selected_element = tk.StringVar(value="C")
        self.bond_order = tk.IntVar(value=1)
        self.tool = tk.StringVar(value="draw")
        self.charge_value = tk.IntVar(value=0)
        # Aromatic-circle mode changes only how eligible rings are displayed;
        # the underlying single/double bond graph is never changed.
        self.aromatic_circle = tk.BooleanVar(value=True)
        self._drawing_cycles = []
        self._aromatic_display_bonds = set()
        self.selected_atoms = set()
        self.selected_bond = None
        self.selected_annotation = None
        self.pending_bond_atom = None

        # Template placement follows the familiar sketcher pattern: choose a
        # template, then click the canvas to place it. Clicking an atom fuses a
        # ring at that vertex; dragging from an atom places a linked ring.
        self.pending_placement = None
        self.placement_start = None
        self.placement_start_atom = None
        self.placement_start_bond = None
        self.placement_dragged = False
        self.placement_preview_ids = []

        # Pointer/drag state
        self.last_canvas_pos = (440.0, 330.0)
        self.drag_start_atom = None
        self.drag_moved = False
        self.temp_ids = []
        self.annotation_start = None
        self.move_component = []
        self.move_last = None
        self.move_before_state = None
        self.move_undo_saved = False
        self.moving_annotation = None
        self.selection_start = None
        self.selection_additive = False
        self.selection_base_atoms = set()

        # Chemistry analysis cache. It never writes changes back into the graph.
        self.chem_mol = None
        self.chem_error = None
        self.invalid_atom_indices = set()
        self.validation_state = "unchecked"  # unchecked, valid, invalid, limited
        self.validation_notes = []

        self._setup_ui()
        self._bind_events()
        self._refresh_chemistry_cache()
        self._redraw_canvas(refresh_chemistry=False)
        self._update_panel()
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
                           command=self._bond_order_changed,
                           takefocus=False).pack(side=tk.LEFT, padx=1)

        ttk.Separator(top, orient=tk.VERTICAL).pack(side=tk.LEFT, fill=tk.Y, padx=7)
        tk.Label(top, text="Tool").pack(side=tk.LEFT, padx=(0, 3))
        for value, label in (("draw", "Draw"), ("atom", "Atom"),
                             ("select", "Select"), ("move", "Move"), ("erase", "Erase")):
            tk.Radiobutton(top, text=label, variable=self.tool, value=value,
                           command=self._tool_changed, takefocus=False).pack(side=tk.LEFT, padx=1)

        ttk.Separator(top, orient=tk.VERTICAL).pack(side=tk.LEFT, fill=tk.Y, padx=7)
        tk.Button(top, text="Check structure", command=self.check_structure,
                  padx=7).pack(side=tk.LEFT, padx=2)
        tk.Button(top, text="Undo", command=self.undo).pack(side=tk.LEFT, padx=(6, 2))
        tk.Button(top, text="Redo", command=self.redo).pack(side=tk.LEFT, padx=2)
        tk.Button(top, text="Clear", command=self.clear_all).pack(side=tk.LEFT, padx=(6, 2))

        second = tk.Frame(self.root, padx=5, pady=4, relief=tk.GROOVE, borderwidth=1)
        second.pack(side=tk.TOP, fill=tk.X)

        tk.Label(second, text="Rings").pack(side=tk.LEFT, padx=(2, 4))
        tk.Button(second, text="Benzene", command=lambda: self.arm_placement("benzene")).pack(side=tk.LEFT, padx=2)
        tk.Button(second, text="Cyclohexane", command=lambda: self.arm_placement("cyclohexane")).pack(side=tk.LEFT, padx=2)
        tk.Button(second, text="Cyclopentane", command=lambda: self.arm_placement("cyclopentane")).pack(side=tk.LEFT, padx=2)

        ttk.Separator(second, orient=tk.VERTICAL).pack(side=tk.LEFT, fill=tk.Y, padx=7)
        tk.Label(second, text="Groups").pack(side=tk.LEFT, padx=(0, 4))
        for label, group in (("CH₃", "CH3"), ("OH", "OH"),
                             ("NH₂", "NH2"), ("COOH", "COOH")):
            tk.Button(second, text=label,
                      command=lambda group_name=group: self.arm_placement(group_name)).pack(
                          side=tk.LEFT, padx=2)

        ttk.Separator(second, orient=tk.VERTICAL).pack(side=tk.LEFT, fill=tk.Y, padx=7)
        tk.Label(second, text="Reaction").pack(side=tk.LEFT, padx=(0, 3))
        for value, label in (("arrow", "→ Arrow"), ("equilibrium", "⇌ Equilibrium"),
                             ("plus", "+ Plus"), ("equals", "= Equals"),
                             ("text", "Text")):
            tk.Radiobutton(second, text=label, variable=self.tool, value=value,
                           command=self._tool_changed, takefocus=False).pack(side=tk.LEFT, padx=1)

        third = tk.Frame(self.root, padx=5, pady=3)
        third.pack(side=tk.TOP, fill=tk.X)
        tk.Label(third, text="Formal charge").pack(side=tk.LEFT, padx=(2, 4))
        tk.Spinbox(third, from_=-3, to=3, width=4, textvariable=self.charge_value).pack(side=tk.LEFT)
        tk.Button(third, text="Apply to selected atom(s)", command=self.apply_charge).pack(
            side=tk.LEFT, padx=5)
        ttk.Separator(third, orient=tk.VERTICAL).pack(side=tk.LEFT, fill=tk.Y, padx=7)
        ttk.Checkbutton(third, text="Aromatic rings as circle",
                        variable=self.aromatic_circle,
                        command=self._redraw_canvas).pack(side=tk.LEFT, padx=(0, 8))
        tk.Label(third, text="Visual style only; checking never edits your drawing.",
                 fg="#5B6573").pack(side=tk.LEFT, padx=4)

        main = tk.Frame(self.root)
        main.pack(expand=True, fill=tk.BOTH)
        self.canvas = tk.Canvas(main, bg="white", width=920, height=650,
                                cursor="crosshair", highlightthickness=0, takefocus=True)
        self.canvas.pack(side=tk.LEFT, expand=True, fill=tk.BOTH)

        panel = tk.Frame(main, width=285, relief=tk.SUNKEN, borderwidth=1, padx=10, pady=8)
        panel.pack(side=tk.RIGHT, fill=tk.Y)
        panel.pack_propagate(False)

        tk.Label(panel, text="STRUCTURE", font=("Arial", 11, "bold")).pack(anchor="w", pady=(2, 7))
        self.formula_label = tk.Label(panel, text="Formula (all fragments): —", anchor="w", justify=tk.LEFT)
        self.formula_label.pack(fill=tk.X, pady=2)
        self.weight_label = tk.Label(panel, text="Average MW: —", anchor="w", justify=tk.LEFT)
        self.weight_label.pack(fill=tk.X, pady=2)
        self.smiles_label = tk.Label(panel, text="SMILES: —", anchor="w", justify=tk.LEFT,
                                     wraplength=255)
        self.smiles_label.pack(fill=tk.X, pady=(3, 2))
        self.atom_count_label = tk.Label(panel, text="Atoms: 0", anchor="w")
        self.atom_count_label.pack(fill=tk.X, pady=2)
        self.bond_count_label = tk.Label(panel, text="Bonds: 0", anchor="w")
        self.bond_count_label.pack(fill=tk.X, pady=2)
        self.fragment_count_label = tk.Label(panel, text="Fragments: 0", anchor="w")
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

        # Contextual, user-confirmed edit: never mutate chemistry just because a
        # suggestion was detected. This button appears only for an unambiguous
        # six-carbon ring with exocyclic C=C and ring double bonds.
        self.suggestion_action_button = tk.Button(
            panel, text="Apply suggested ring edit", command=self.apply_saturated_ring_suggestion,
            padx=4, pady=3, takefocus=False)

        self.engine_label = tk.Label(
            panel,
            text=("Chemistry engine: RDKit" if RDKIT_AVAILABLE else
                  "Chemistry engine: basic checks only\nInstall RDKit for stronger validation."),
            anchor="w", justify=tk.LEFT, fg="#5B6573", font=("Arial", 8), wraplength=255)
        self.engine_label.pack(fill=tk.X, pady=(8, 2))

        self.status_label = tk.Label(self.root, text="", anchor="w", relief=tk.SUNKEN,
                                     padx=7, pady=3, fg="#4B5563")
        self.status_label.pack(side=tk.BOTTOM, fill=tk.X)

        self._set_diagnostics([
            "Draw the structure, then click Check structure.",
            "Suggestions are shown here. The editor never repairs or changes a structure automatically.",
        ])

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
            self.root.bind(key, lambda _e, value=element: self._set_element_from_key(value))
        for order in (1, 2, 3):
            self.root.bind(str(order), lambda _e, value=order: self._set_bond_order_from_key(value))

    # ------------------------------------------------------ state and history
    def _capture_state(self):
        atom_index = {atom: i for i, atom in enumerate(self.atoms)}
        return {
            "atoms": [(a.x, a.y, a.element, a.charge) for a in self.atoms],
            "bonds": [(atom_index[b.atom1], atom_index[b.atom2], b.order) for b in self.bonds],
            "annotations": [(a.kind, a.x1, a.y1, a.x2, a.y2, a.text)
                            for a in self.annotations],
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
        # Do not use _push_snapshot here: it clears the redo stack.
        self.undo_stack.append(self._capture_state())
        if len(self.undo_stack) > self.max_undo:
            self.undo_stack.pop(0)
        self._restore_state(self.redo_stack.pop())

    def _restore_state(self, state):
        current = self._capture_state()
        # Annotation-only undo/redo keeps the existing chemistry result: annotations
        # are not atoms, do not affect valence, and are excluded from validation.
        same_chemical_drawing = (current["atoms"] == state["atoms"] and
                                 current["bonds"] == state["bonds"])
        previous_validation = (self.validation_state, list(self.validation_notes),
                               set(self.invalid_atom_indices))

        self.atoms = []
        self.bonds = []
        self.annotations = []
        self.selected_atoms.clear()
        self.selected_bond = None
        self.selected_annotation = None
        self.pending_bond_atom = None
        self.pending_placement = None
        self.placement_start = None
        self.placement_start_atom = None
        self.placement_start_bond = None
        self.placement_dragged = False
        self._clear_placement_preview()
        self.drag_start_atom = None
        self.annotation_start = None

        for x, y, element, charge in state["atoms"]:
            self.atoms.append(Atom(x, y, element, charge))
        for i, j, order in state["bonds"]:
            self.bonds.append(Bond(self.atoms[i], self.atoms[j], order))
        for kind, x1, y1, x2, y2, text in state.get("annotations", []):
            self.annotations.append(Annotation(kind, x1, y1, x2, y2, text))

        if same_chemical_drawing:
            self.validation_state, self.validation_notes, self.invalid_atom_indices = previous_validation
        else:
            self._invalidate_validation()
        self._redraw_canvas()
        self._set_status("Restored drawing. Run Check structure to review it again." if not same_chemical_drawing
                         else "Restored reaction annotation; chemistry result unchanged.")

    def _invalidate_validation(self):
        """Mark chemistry as unchecked and show any immediate, non-destructive hint."""
        self.validation_state = "unchecked"
        self.validation_notes = []
        self.invalid_atom_indices.clear()

        # Give feedback as soon as the drawing changes. This is only a suggestion:
        # it never changes bond orders, atom positions, elements or charges.
        hint = self._exocyclic_multiple_bond_suggestion()
        if hint:
            self._set_diagnostics([
                "Drawing updated — full validation has not been run yet.",
                hint,
                "Suggestion only: select the indicated bond and choose — to change it yourself. "
                "Click Check structure for the complete chemistry review. No changes were made automatically.",
            ])
        else:
            self._set_diagnostics([
                "Draw the structure, then click Check structure.",
                "Suggestions are shown here. The editor never repairs or changes a structure automatically.",
            ])

    # -------------------------------------------------------- chemistry engine
    def _build_sanitized_molecule(self):
        """Build a separate RDKit molecule. Never rewrites the editor's Atom/Bond graph."""
        if not RDKIT_AVAILABLE:
            return None, "RDKit is not installed"
        if not self.atoms:
            return None, "Empty drawing"

        rw = Chem.RWMol()
        atom_to_index = {}
        try:
            for atom in self.atoms:
                rd_atom = Chem.Atom(atom.element)
                rd_atom.SetFormalCharge(int(atom.charge))
                rd_atom.SetNoImplicit(False)
                atom_to_index[atom] = rw.AddAtom(rd_atom)

            bond_types = {1: Chem.BondType.SINGLE,
                          2: Chem.BondType.DOUBLE,
                          3: Chem.BondType.TRIPLE}
            for bond in self.bonds:
                if bond.order not in bond_types:
                    raise ValueError("Only single, double and triple bonds are supported.")
                rw.AddBond(atom_to_index[bond.atom1], atom_to_index[bond.atom2],
                           bond_types[bond.order])

            mol = rw.GetMol()
            # RDKit's diagnostic is shown in the editor panel instead of cluttering the terminal.
            with rdBase.BlockLogs():
                Chem.SanitizeMol(mol)
            return mol, None
        except Exception as exc:
            return None, str(exc).splitlines()[0][:240] or exc.__class__.__name__

    def _fallback_targets(self, atom):
        charge = atom.charge
        if atom.element == "N" and charge == 1:
            return (4,)
        if atom.element == "N" and charge == -1:
            return (2,)
        if atom.element == "O" and charge == 1:
            return (3,)
        if atom.element == "O" and charge == -1:
            return (1,)
        return COMMON_VALENCES.get(atom.element, ())

    def _fallback_implicit_h(self, atom):
        if atom.element == "H":
            return 0
        targets = self._fallback_targets(atom)
        if not targets:
            return 0
        bond_sum = atom.bond_order_sum()
        possible = [target for target in targets if target >= bond_sum]
        if not possible:
            return 0
        return max(0, min(possible) - bond_sum)

    def _refresh_chemistry_cache(self):
        """Refresh descriptor/display data, not the drawn bonds, positions or charges."""
        self.chem_mol, self.chem_error = self._build_sanitized_molecule()
        if self.chem_mol is not None:
            for i, atom in enumerate(self.atoms):
                try:
                    atom.implicit_h = int(self.chem_mol.GetAtomWithIdx(i).GetNumImplicitHs())
                except Exception:
                    atom.implicit_h = 0
        else:
            for atom in self.atoms:
                atom.implicit_h = self._fallback_implicit_h(atom)

    def _fallback_atom_is_valid(self, atom):
        targets = self._fallback_targets(atom)
        if not targets:
            return True
        total = atom.bond_order_sum() + atom.implicit_h
        return total in targets

    def _heuristic_suspects(self):
        suspects = set()
        for i, atom in enumerate(self.atoms):
            targets = self._fallback_targets(atom)
            if targets and atom.bond_order_sum() > max(targets):
                suspects.add(i)
            if atom.element == "H" and atom.bond_order_sum() != 1:
                suspects.add(i)
        return suspects

    def _friendly_rdkit_issue(self, raw_error):
        match = re.search(r"atom\s*#\s*(\d+)\s+([A-Za-z]+),\s*(-?\d+)", raw_error or "")
        if match:
            index = int(match.group(1))
            symbol = match.group(2)
            value = match.group(3)
            if 0 <= index < len(self.atoms):
                self.invalid_atom_indices.add(index)
                return (f"Atom {index + 1} ({symbol}) has an explicit valence of {value} that RDKit "
                        "does not accept for this structure.")
        unkek = re.search(r"Unkekulized atoms:\s*([0-9 ]+)", raw_error or "")
        if unkek:
            indices = [int(v) for v in unkek.group(1).split() if v.isdigit()]
            self.invalid_atom_indices.update(i for i in indices if 0 <= i < len(self.atoms))
            if indices:
                return "The ring bond pattern could not be assigned a valid Kekulé form. Review the drawn bond orders around atoms " + ", ".join(str(i + 1) for i in indices[:8]) + "."
        return "The chemistry engine could not sanitize this graph: " + (raw_error or "unknown chemistry error")

    def has_unusual_bonds(self):
        for bond in self.bonds:
            a, b = bond.atom1.element, bond.atom2.element
            if "H" in (a, b) and bond.order != 1:
                return True
            if a in HALOGENS and b in HALOGENS and bond.order != 1:
                return True
        return False

    def check_structure(self):
        """Report validation results and suggestions. This method never repairs the drawing."""
        self._refresh_chemistry_cache()
        self.invalid_atom_indices.clear()
        notes = []

        if not self.atoms:
            self.validation_state = "invalid"
            self.validation_notes = ["Nothing to check yet. Draw a structure first."]
            self._update_panel()
            self._set_diagnostics(self.validation_notes + ["No changes were made to the canvas."])
            self.validation_label.config(text="Nothing to validate", fg="#5B6573")
            return

        components = self.get_connected_components()
        if len(components) > 1:
            notes.append(f"{len(components)} separate fragments found. This is allowed for reaction schemes.")

        overlaps = self._overlapping_atom_pairs()
        geometry_note = None
        if overlaps:
            geometry_note = f"Drawing note: {len(overlaps)} atom pair(s) overlap or sit very close together. Consider moving a fragment."

        unusual_bonds = self.has_unusual_bonds()
        if RDKIT_AVAILABLE:
            if self.chem_mol is not None and not unusual_bonds:
                self.validation_state = "valid"
                notes.insert(0, "No valence or sanitization errors detected by RDKit.")
            else:
                self.validation_state = "invalid"
                if self.chem_error:
                    self.invalid_atom_indices.update(self._heuristic_suspects())
                    issue = self._friendly_rdkit_issue(self.chem_error)
                    notes.insert(0, issue)
                    notes.append("Suggestions (not applied): review the bond order and formal charge around the flagged atom; confirm explicit hydrogens and neighboring atoms.")
                    if "Kekul" in self.chem_error or "kekul" in self.chem_error.lower():
                        notes.append("For a ring, review conjugation and alternating bond placement. Ring size alone does not establish aromaticity.")
                if unusual_bonds:
                    notes.insert(0, "An unusual bond was drawn (for example, a multiple bond to hydrogen or between halogens).")
                    notes.append("Suggestion (not applied): inspect the bond type and the intended atom identities.")
                if not self.invalid_atom_indices:
                    self.invalid_atom_indices.update(self._heuristic_suspects())

        else:
            suspect = self._heuristic_suspects()
            if unusual_bonds:
                self.validation_state = "invalid"
                notes.insert(0, "An unusual bond was detected by the basic checks.")
                notes.append("Suggestion (not applied): inspect bond order and atom types.")
                self.invalid_atom_indices.update(suspect)
            elif suspect:
                self.validation_state = "invalid"
                notes.insert(0, "Basic valence heuristics flagged atom(s): " + ", ".join(str(i + 1) for i in sorted(suspect)) + ".")
                notes.append("Suggestion (not applied): review the bonds and formal charges at those atoms.")
                self.invalid_atom_indices.update(suspect)
            else:
                self.validation_state = "limited"
                notes.insert(0, "No obvious valence issue found by the basic checks; this is not a full validation.")
            notes.append("Install RDKit for stronger chemistry validation, aromaticity handling and canonical SMILES.")

        # Give a drawing-specific suggestion for a common sketching mistake:
        # adding an exocyclic multiple bond to a ring carbon while leaving the
        # adjacent Kekule double bond in place. This is advice only. In keeping
        # with the editor's non-destructive contract, never alter a bond here.
        ring_bond_hint = self._exocyclic_multiple_bond_suggestion(
            self.invalid_atom_indices)
        if ring_bond_hint:
            notes.append(ring_bond_hint)

        if geometry_note:
            notes.append(geometry_note)
        notes.append("No atoms, bonds, positions or charges were changed by this check.")
        self.validation_notes = notes
        self._redraw_canvas(refresh_chemistry=False)
        self._update_panel()
        self._set_diagnostics(notes)
        if self.validation_state == "valid":
            self.validation_label.config(text="✓ Chemistry checks passed", fg="#187344")
            self._set_status("Check complete: chemistry checks passed. The drawing was not changed.")
        elif self.validation_state == "limited":
            self.validation_label.config(text="Limited checks only", fg="#9A6700")
            self._set_status("Basic checks complete. Install RDKit for full structure validation.")
        else:
            self.validation_label.config(text="⚠ Needs review", fg="#B42318")
            self._set_status("Check complete: review the suggestions in the right panel. Nothing was corrected automatically.")

    def calculate_molecular_formula(self):
        if not self.atoms:
            return "—"
        if RDKIT_AVAILABLE:
            if self.chem_mol is None:
                return "Unavailable until the structure passes chemistry checks"
            try:
                return rdMolDescriptors.CalcMolFormula(self.chem_mol)
            except Exception:
                return "Unavailable"
        counts = defaultdict(int)
        for atom in self.atoms:
            counts[atom.element] += 1
            counts["H"] += atom.implicit_h
        pieces = []
        for element in ("C", "H"):
            if counts.get(element):
                pieces.append(element + (str(counts[element]) if counts[element] != 1 else ""))
                counts.pop(element, None)
        for element in sorted(counts):
            if counts[element]:
                pieces.append(element + (str(counts[element]) if counts[element] != 1 else ""))
        return "~" + ("".join(pieces) or "—")

    def calculate_molecular_weight(self):
        if not self.atoms:
            return None
        if RDKIT_AVAILABLE:
            if self.chem_mol is None:
                return None
            try:
                return round(float(Descriptors.MolWt(self.chem_mol)), 2)
            except Exception:
                return None
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
        if self.chem_mol is None:
            return "Unavailable — check structure"
        try:
            return Chem.MolToSmiles(self.chem_mol, canonical=True)
        except Exception:
            return "Unavailable"

    # ---------------------------------------------------------------- geometry
    def _canvas_size(self):
        width = max(self.canvas.winfo_width(), 400)
        height = max(self.canvas.winfo_height(), 300)
        return width, height

    def find_atom_at(self, x, y, radius=None):
        radius = self.ATOM_HIT_RADIUS if radius is None else radius
        for atom in reversed(self.atoms):
            if atom.distance_to(x, y) <= radius:
                return atom
        return None

    @staticmethod
    def point_near_line(px, py, x1, y1, x2, y2, threshold=6):
        dx, dy = x2 - x1, y2 - y1
        length_sq = dx * dx + dy * dy
        if length_sq < 1e-9:
            return math.hypot(px - x1, py - y1) < threshold
        t = max(0.0, min(1.0, ((px - x1) * dx + (py - y1) * dy) / length_sq))
        qx, qy = x1 + t * dx, y1 + t * dy
        return math.hypot(px - qx, py - qy) < threshold

    def find_bond_at(self, x, y, threshold=7):
        for bond in reversed(self.bonds):
            if self.point_near_line(x, y, bond.atom1.x, bond.atom1.y,
                                    bond.atom2.x, bond.atom2.y, threshold):
                return bond
        return None

    def find_annotation_at(self, x, y):
        for annotation in reversed(self.annotations):
            if annotation.kind in ("plus", "equals", "text"):
                approximate_width = max(18, len(annotation.text or annotation.kind) * 8)
                if (abs(x - annotation.x1) <= approximate_width / 2 + 5 and
                        abs(y - annotation.y1) <= 17):
                    return annotation
            elif annotation.kind == "equilibrium":
                if (self.point_near_line(x, y, annotation.x1, annotation.y1 - 3,
                                         annotation.x2, annotation.y2 - 3, 9) or
                    self.point_near_line(x, y, annotation.x2, annotation.y2 + 3,
                                         annotation.x1, annotation.y1 + 3, 9)):
                    return annotation
            elif self.point_near_line(x, y, annotation.x1, annotation.y1,
                                      annotation.x2, annotation.y2, 9):
                return annotation
        return None

    def snap_angle(self, x1, y1, x2, y2):
        dx, dy = x2 - x1, y2 - y1
        length = math.hypot(dx, dy)
        if length < 0.001:
            return x2, y2
        angle = math.degrees(math.atan2(dy, dx)) % 360
        nearest = min(self.SNAP_ANGLES,
                      key=lambda candidate: abs((angle - candidate + 180) % 360 - 180))
        rad = math.radians(nearest)
        return x1 + length * math.cos(rad), y1 + length * math.sin(rad)

    @staticmethod
    def _angular_difference(a, b):
        return abs((a - b + 180) % 360 - 180)

    def _candidate_directions(self, anchor, target_x=None, target_y=None):
        if target_x is None or target_y is None:
            target_x, target_y = self.last_canvas_pos
        requested = math.degrees(math.atan2(target_y - anchor.y, target_x - anchor.x)) % 360
        angles = sorted(self.SNAP_ANGLES,
                        key=lambda angle: self._angular_difference(angle, requested))
        return [(math.cos(math.radians(angle)), math.sin(math.radians(angle)),
                 self._angular_difference(angle, requested)) for angle in angles]

    def _geometry_score(self, points, excluded=(), angle_difference=0.0, cursor_distance=0.0):
        """Lower score is better: avoid overlaps/bounds first, then respect the cursor."""
        excluded = set(excluded)
        width, height = self._canvas_size()
        bad_bounds = 0
        for x, y, _element in points:
            if x < 12 or y < 12 or x > width - 12 or y > height - 12:
                bad_bounds += 1

        overlap_pairs = 0
        min_clearance = 1e6
        for x, y, _element in points:
            for atom in self.atoms:
                if atom in excluded:
                    continue
                distance = math.hypot(x - atom.x, y - atom.y)
                min_clearance = min(min_clearance, distance)
                if distance < self.MIN_ATOM_GAP:
                    overlap_pairs += 1
        if min_clearance == 1e6:
            min_clearance = 500.0
        return (bad_bounds + overlap_pairs, cursor_distance, angle_difference, -min_clearance)

    def _best_attached_direction(self, anchor, geometry):
        candidates = self._candidate_directions(anchor)
        scored = []
        for ux, uy, angle_difference in candidates:
            points = geometry(ux, uy)
            score = self._geometry_score(points, excluded={anchor},
                                         angle_difference=angle_difference)
            scored.append((score, ux, uy, points))
        score, ux, uy, points = min(scored, key=lambda item: item[0])
        return ux, uy, points, score[0] > 0

    def _spiral_origins(self, x, y):
        yield x, y, 0.0
        for radius in (30.0, 54.0, 78.0, 104.0):
            for i in range(16):
                angle = math.radians(i * 22.5)
                yield x + radius * math.cos(angle), y + radius * math.sin(angle), radius

    def _best_unattached_origin(self, x, y, geometry):
        scored = []
        for ox, oy, offset in self._spiral_origins(x, y):
            points = geometry(ox, oy)
            score = self._geometry_score(points, cursor_distance=offset)
            scored.append((score, ox, oy, points))
            if score[0] == 0 and offset == 0:
                return ox, oy, points, False
        score, ox, oy, points = min(scored, key=lambda item: item[0])
        return ox, oy, points, score[0] > 0

    def _anchor_atom(self):
        if self.pending_bond_atom in self.atoms:
            return self.pending_bond_atom
        if len(self.selected_atoms) == 1:
            atom = next(iter(self.selected_atoms))
            if atom in self.atoms:
                return atom
        return None

    def on_mouse_motion(self, event):
        self.last_canvas_pos = (event.x, event.y)
        if self.pending_placement and self.placement_start is None:
            anchor = self.find_atom_at(event.x, event.y)
            hovered_bond = None if anchor else self.find_bond_at(event.x, event.y)
            if hovered_bond is not None and self.pending_placement not in (
                    "benzene", "cyclohexane", "cyclopentane"):
                anchor = min((hovered_bond.atom1, hovered_bond.atom2),
                             key=lambda a: a.distance_to(event.x, event.y))
                hovered_bond = None
            self._placement_preview_geometry(event.x, event.y, anchor=anchor,
                                             dragged=False, bond=hovered_bond)

    # ------------------------------------------------------ template placement
    def arm_placement(self, kind):
        """Arm a one-shot ring/group tool; the next canvas click places it."""
        valid = {"benzene", "cyclohexane", "cyclopentane", "CH3", "OH", "NH2", "COOH"}
        if kind not in valid:
            return
        self.pending_placement = kind
        self.placement_start = None
        self.placement_start_atom = None
        self.placement_start_bond = None
        self.placement_dragged = False
        self.pending_bond_atom = None
        self.drag_start_atom = None
        self._clear_placement_preview()
        if self.tool.get() != "draw":
            self.tool.set("draw")
            self._tool_changed()
        self._set_status(
            f"{kind} selected: click empty canvas to place; click an atom to attach a group/ring. "
            "For rings, click an existing bond to fuse along that bond. Drag from an atom to set the attachment direction. Esc cancels."
        )

    def _clear_placement_preview(self):
        for item_id in self.placement_preview_ids:
            self.canvas.delete(item_id)
        self.placement_preview_ids = []

    def _preview_line(self, x1, y1, x2, y2, width=2, arrow=None):
        kwargs = {"fill": "#82A9E6", "width": width, "dash": (3, 3),
                  "capstyle": tk.ROUND}
        if arrow is not None:
            kwargs["arrow"] = arrow
        self.placement_preview_ids.append(
            self.canvas.create_line(x1, y1, x2, y2, **kwargs))

    def _placement_direction(self, anchor, x, y):
        dx, dy = x - anchor.x, y - anchor.y
        if math.hypot(dx, dy) < 2:
            _ux, _uy, _pts, _crowded = self._best_attached_direction(
                anchor, lambda ux, uy: [(anchor.x + self.BOND_LENGTH * ux,
                                         anchor.y + self.BOND_LENGTH * uy, "C")])
            return _ux, _uy
        sx, sy = self.snap_angle(anchor.x, anchor.y, x, y)
        length = math.hypot(sx - anchor.x, sy - anchor.y)
        if length < 1e-6:
            return 1.0, 0.0
        return (sx - anchor.x) / length, (sy - anchor.y) / length

    def _placement_preview_geometry(self, x, y, anchor=None, dragged=False, bond=None):
        """Draw a non-mutating preview using the same placement geometry as commit."""
        kind = self.pending_placement
        if not kind:
            return
        self._clear_placement_preview()
        ring_sizes = {"benzene": (6, True), "cyclohexane": (6, False),
                      "cyclopentane": (5, False)}
        if kind in ring_sizes:
            size, aromatic = ring_sizes[kind]
            if bond is not None:
                ring_points = self._fused_bond_ring_points(bond, size, x, y)
                pts = [(px, py) for px, py, _ in ring_points]
                # The shared bond is already in the drawing; the dashed preview
                # makes the intended fused-ring side visible before placement.
                for i in range(size):
                    self._preview_line(*pts[i], *pts[(i + 1) % size])
            elif anchor is not None:
                ux, uy = self._placement_direction(anchor, x, y)
                ring_points = self._ring_points_attached(anchor, ux, uy, size)
                pts = [(px, py) for px, py, _ in ring_points]
                self._preview_line(anchor.x, anchor.y, pts[0][0], pts[0][1])
                for i in range(size):
                    self._preview_line(*pts[i], *pts[(i + 1) % size])
            else:
                ring_points = self._ring_points_unattached(x, y, size)
                pts = [(px, py) for px, py, _ in ring_points]
                for i in range(size):
                    self._preview_line(*pts[i], *pts[(i + 1) % size])
            if aromatic:
                cx = sum(px for px, py in pts) / size
                cy = sum(py for px, py in pts) / size
                rad = sum(math.hypot(px - cx, py - cy) for px, py in pts) / size * 0.5
                self.placement_preview_ids.append(self.canvas.create_oval(
                    cx-rad, cy-rad, cx+rad, cy+rad, outline="#82A9E6",
                    width=1.5, dash=(3, 3), fill=""))
            return

        # Functional groups: preview only, never add temporary Atom/Bond objects.
        if anchor is not None:
            ux, uy = self._placement_direction(anchor, x, y)
            points = self._group_geometry_attached(anchor, kind, ux, uy)
            if kind == "COOH":
                c = points[0]; o1, o2 = points[1], points[2]
                self._preview_line(anchor.x, anchor.y, c[0], c[1])
                self._preview_line(c[0], c[1], o1[0], o1[1], width=2)
                self._preview_line(c[0], c[1], o2[0], o2[1])
                # Parallel short stroke on the nominal C=O side.
                dx, dy = o1[0]-c[0], o1[1]-c[1]
                length = max(math.hypot(dx, dy), 1)
                px, py = -dy/length*3, dx/length*3
                self._preview_line(c[0]+px, c[1]+py, o1[0]+px, o1[1]+py, width=1)
                labels = [(c[0], c[1], "C"), (o1[0], o1[1], "O"), (o2[0], o2[1], "OH")]
            else:
                gx, gy, element = points[0]
                self._preview_line(anchor.x, anchor.y, gx, gy)
                label = {"CH3": "CH₃", "OH": "OH", "NH2": "NH₂"}[kind]
                labels = [(gx, gy, label)]
        else:
            points = self._group_geometry_unattached(kind, x, y)
            labels = []
            if kind == "CH3":
                labels = [(points[0][0], points[0][1], "CH₃")]
            elif kind == "OH":
                self._preview_line(points[0][0], points[0][1], points[1][0], points[1][1])
                labels = [(points[0][0], points[0][1], "OH")]
            elif kind == "NH2":
                labels = [(points[0][0], points[0][1], "NH₂")]
            elif kind == "COOH":
                c, o1, o2 = points
                self._preview_line(c[0], c[1], o1[0], o1[1])
                self._preview_line(c[0], c[1], o2[0], o2[1])
                labels = [(c[0], c[1], "C"), (o1[0], o1[1], "O"), (o2[0], o2[1], "OH")]
        for lx, ly, label in labels:
            self.placement_preview_ids.append(self.canvas.create_text(
                lx, ly, text=label, fill="#497DBF", font=("Arial", 11, "bold")))

    def _fused_bond_ring_points(self, bond, size, hint_x=None, hint_y=None):
        """Return a regular ring sharing an existing bond, on the less crowded side."""
        a, b = bond.atom1, bond.atom2
        dx, dy = b.x - a.x, b.y - a.y
        length = math.hypot(dx, dy)
        if length < 1e-6:
            return self._ring_points_unattached(a.x, a.y, size)
        radius = length / (2.0 * math.sin(math.pi / size))
        apothem = radius * math.cos(math.pi / size)
        nx, ny = -dy / length, dx / length
        mx, my = (a.x + b.x) / 2.0, (a.y + b.y) / 2.0
        if hint_x is None or hint_y is None:
            hint_x, hint_y = mx, my
        side_distance = ((dx * (hint_y - my) - dy * (hint_x - mx)) / length)
        preferred_side = 1 if side_distance >= 0 else -1
        sides = (preferred_side, -preferred_side) if abs(side_distance) > 3 else (1, -1)
        scored = []
        for side in sides:
            cx, cy = mx + side * apothem * nx, my + side * apothem * ny
            start_angle = math.atan2(a.y - cy, a.x - cx)
            angle_b = math.atan2(b.y - cy, b.x - cx)
            delta = (angle_b - start_angle + math.pi) % (2 * math.pi) - math.pi
            coords = [(cx + radius * math.cos(start_angle + i * delta),
                       cy + radius * math.sin(start_angle + i * delta), "C")
                      for i in range(size)]
            coords[0] = (a.x, a.y, a.element)
            coords[1] = (b.x, b.y, b.element)
            score = self._geometry_score(coords[2:], excluded={a, b},
                                         angle_difference=0 if side == preferred_side else 1)
            scored.append((score, coords))
        return min(scored, key=lambda item: item[0])[1]

    def _add_ring_fused_to_bond(self, bond, size, aromatic=False, hint_x=None, hint_y=None):
        """Add a ring that shares the selected bond; do not alter that bond."""
        if bond not in self.bonds:
            return
        points = self._fused_bond_ring_points(bond, size, hint_x, hint_y)
        self.save_state()
        cycle = [bond.atom1, bond.atom2]
        for px, py, element in points[2:]:
            atom = Atom(px, py, element)
            self.atoms.append(atom)
            cycle.append(atom)
        # The existing shared bond is deliberately preserved. For a fused
        # benzene template, choose the two bonds at the fusion endpoints to fit
        # their current valence; the new internal bonds then alternate. This is
        # template construction, not mutation of any pre-existing bond.
        endpoint_orders = (1, 1)
        if aromatic and size == 6:
            def endpoint_bond_order(atom):
                total = atom.bond_order_sum()
                other_bonds = [b for b in atom.bonds if b is not bond]
                desired = (3 - total) if not other_bonds else (4 - total)
                return max(1, min(3, int(desired)))
            endpoint_orders = (endpoint_bond_order(bond.atom1),
                               endpoint_bond_order(bond.atom2))
        for i in range(1, size):
            if aromatic and size == 6:
                if i == 1:
                    order = endpoint_orders[1]  # bond from shared atom B to new atom
                elif i == 5:
                    order = endpoint_orders[0]  # bond from new atom to shared atom A
                elif i % 2 == 0:
                    order = 3 - endpoint_orders[1]
                else:
                    order = endpoint_orders[1]
            else:
                order = 1
            self.bonds.append(Bond(cycle[i], cycle[(i + 1) % size], order))
        self.selected_atoms = set(cycle[2:])
        self.selected_bond = None
        self.selected_annotation = None
        self.pending_bond_atom = cycle[0]
        self._invalidate_validation()
        self._redraw_canvas()
        self._set_status("Ring fused along the selected bond. The original bond order was preserved; run Check structure to review it.")

    def _finish_placement(self, x, y):
        kind = self.pending_placement
        anchor = self.placement_start_atom
        target_bond = self.placement_start_bond
        dragged = self.placement_dragged
        start = self.placement_start or (x, y)
        self._clear_placement_preview()
        self.pending_placement = None
        self.placement_start = None
        self.placement_start_atom = None
        self.placement_start_bond = None
        self.placement_dragged = False
        self.last_canvas_pos = (x, y)

        ring_sizes = {"benzene": (6, True), "cyclohexane": (6, False),
                      "cyclopentane": (5, False)}
        if kind in ring_sizes:
            size, aromatic = ring_sizes[kind]
            if target_bond is not None:
                self._add_ring_fused_to_bond(target_bond, size, aromatic, x, y)
            elif anchor is not None:
                # Clicking an atom attaches a distinct ring; dragging from it
                # controls the direction. Click a bond to create a fused ring.
                self.selected_atoms = {anchor}
                self.pending_bond_atom = anchor
                self._new_ring(size, aromatic)
            else:
                self.selected_atoms.clear()
                self.pending_bond_atom = None
                self.last_canvas_pos = (start[0], start[1])
                self._new_ring(size, aromatic)
            return

        # If a group is clicked on a bond rather than an atom, attach it to the
        # closer endpoint. Otherwise place it exactly where the user clicked.
        if anchor is not None:
            self.selected_atoms = {anchor}
            self.pending_bond_atom = anchor
        else:
            self.selected_atoms.clear()
            self.pending_bond_atom = None
            self.last_canvas_pos = (start[0], start[1])
        self.add_functional_group(kind)

    def _add_fused_ring(self, anchor, size, aromatic=False):
        """Add a ring sharing its attachment atom, as common template tools do."""
        def geometry(ux, uy):
            return self._fused_ring_points(anchor, ux, uy, size)[1:]
        ux, uy, _points, crowded = self._best_attached_direction(anchor, geometry)
        points = self._fused_ring_points(anchor, ux, uy, size)
        self.save_state()
        cycle = [anchor]
        for px, py, element in points[1:]:
            atom = Atom(px, py, element)
            self.atoms.append(atom)
            cycle.append(atom)
        for i in range(size):
            order = 2 if aromatic and i % 2 == 0 else 1
            self.bonds.append(Bond(cycle[i], cycle[(i + 1) % size], order))
        self.selected_atoms = {anchor}
        self.selected_bond = None
        self.selected_annotation = None
        self.pending_bond_atom = anchor
        self._invalidate_validation()
        self._redraw_canvas()
        self._set_status("Ring fused at the selected atom. Existing bonds were preserved; run Check structure to review valence.")
        if crowded:
            self._set_status("Ring fused, but nearby atoms may overlap. Move fragments if needed; no atoms were auto-moved.")

    # ------------------------------------------------------------ draw events
    def _bond_order_changed(self):
        """Apply an explicitly chosen order to the selected bond, if any."""
        bond = self.selected_bond
        if bond is None or bond not in self.bonds:
            return
        new_order = int(self.bond_order.get())
        if bond.order == new_order:
            return
        old_order = bond.order
        self.save_state()
        bond.order = new_order
        self._invalidate_validation()
        self._redraw_canvas()
        labels = {1: "single", 2: "double", 3: "triple"}
        self._set_status(
            f"Selected bond changed from {labels.get(old_order, old_order)} to "
            f"{labels.get(new_order, new_order)} by your choice. Run Check structure to review it."
        )

    def _component_union(self, seeds):
        """Return unique connected components reached from a collection of atoms."""
        result = []
        seen = set()
        for seed in seeds:
            if seed not in self.atoms:
                continue
            for atom in self.get_connected_component(seed):
                if atom not in seen:
                    seen.add(atom)
                    result.append(atom)
        return result

    def _tool_changed(self):
        if self.tool.get() != "draw":
            self.pending_bond_atom = None
            self.drag_start_atom = None
            # A pending template is a one-shot drawing tool. Switching tools
            # cancels it, rather than letting a later click unexpectedly place it.
            if self.pending_placement is not None:
                self.pending_placement = None
                self.placement_start = None
                self.placement_start_atom = None
                self.placement_start_bond = None
                self.placement_dragged = False
                self._clear_placement_preview()
        if self.tool.get() != "select" and self.selection_start is not None:
            self.selection_start = None
            self.selection_base_atoms.clear()
            self._clear_temp_preview()
        cursor = "crosshair"
        if self.tool.get() in ("select", "atom"):
            cursor = "arrow" if self.tool.get() == "select" else "crosshair"
        elif self.tool.get() == "move":
            cursor = "fleur"
        elif self.tool.get() == "erase":
            cursor = "X_cursor"
        self.canvas.configure(cursor=cursor)
        self._update_tool_status()

    def _set_element_from_key(self, element):
        try:
            focus = self.root.focus_get()
            if focus in (self.canvas, self.root):
                self.selected_element.set(element)
        except tk.TclError:
            self.selected_element.set(element)

    def _set_bond_order_from_key(self, order):
        self.bond_order.set(int(order))
        self._bond_order_changed()

    def _update_tool_status(self):
        self._set_status(self.TOOL_HELP.get(self.tool.get(), ""))

    def _set_status(self, text):
        if hasattr(self, "status_label"):
            self.status_label.config(text=text)

    def on_click(self, event):
        self.canvas.focus_set()
        self.last_canvas_pos = (event.x, event.y)
        mode = self.tool.get()

        if self.pending_placement:
            self.placement_start = (event.x, event.y)
            self.placement_start_atom = self.find_atom_at(event.x, event.y)
            self.placement_start_bond = None if self.placement_start_atom else self.find_bond_at(event.x, event.y)
            if (self.placement_start_bond is not None and self.pending_placement not in
                    ("benzene", "cyclohexane", "cyclopentane")):
                bond = self.placement_start_bond
                self.placement_start_atom = min(
                    (bond.atom1, bond.atom2), key=lambda a: a.distance_to(event.x, event.y))
                self.placement_start_bond = None
            self.placement_dragged = False
            self._placement_preview_geometry(
                event.x, event.y, anchor=self.placement_start_atom, dragged=False,
                bond=self.placement_start_bond)
            return

        # Reaction annotations live on their own layer and never become atoms/bonds.
        if mode in ("arrow", "equilibrium"):
            self.annotation_start = (event.x, event.y)
            self._draw_annotation_preview(event.x, event.y)
            return
        if mode in ("plus", "equals"):
            self.save_state()
            symbol = "+" if mode == "plus" else "="
            self.annotations.append(Annotation(mode, event.x, event.y, text=symbol))
            self._redraw_canvas(refresh_chemistry=False)
            return
        if mode == "text":
            label = simpledialog.askstring("Reaction label", "Text or condition to place:",
                                           parent=self.root)
            if label is not None and label.strip():
                self.save_state()
                self.annotations.append(Annotation("text", event.x, event.y, text=label.strip()))
                self._redraw_canvas(refresh_chemistry=False)
            return

        if mode == "select":
            self.pending_bond_atom = None
            self.drag_start_atom = None
            self.selection_start = (event.x, event.y)
            self.selection_additive = bool(event.state & 0x0001)  # Shift
            self.selection_base_atoms = set(self.selected_atoms) if self.selection_additive else set()
            self._clear_temp_preview()
            return

        atom = self.find_atom_at(event.x, event.y)
        bond = None if atom else self.find_bond_at(event.x, event.y)
        annotation = None if atom or bond else self.find_annotation_at(event.x, event.y)

        if mode == "atom":
            self.pending_bond_atom = None
            self.drag_start_atom = None
            self.selected_bond = None
            self.selected_annotation = None
            if atom is not None:
                self.selected_atoms = {atom}
                chosen = self.selected_element.get()
                if atom.element != chosen:
                    self.save_state()
                    old_element = atom.element
                    atom.element = chosen
                    self._invalidate_validation()
                    self._redraw_canvas()
                    self._set_status(
                        f"Changed atom {old_element} to {chosen}. Its existing bonds and formal charge were preserved; check valence when ready."
                    )
                else:
                    self._redraw_canvas(refresh_chemistry=False)
                    self._set_status(f"Selected {chosen}; it already has that element.")
            elif bond is None and annotation is None:
                self.save_state()
                new_atom = Atom(event.x, event.y, self.selected_element.get())
                self.atoms.append(new_atom)
                self.selected_atoms = {new_atom}
                self._invalidate_validation()
                self._redraw_canvas()
                self._set_status(f"Placed {new_atom.element}. Click an existing atom to change its element; bonds are not auto-corrected.")
            else:
                self._set_status("Atom tool changes atoms or places a new atom; use Select to choose a bond.")
            return

        if mode == "draw" and bond is not None:
            # Standard sketcher behavior: the active bond order can be applied
            # directly to an existing bond by clicking it.
            self.pending_bond_atom = None
            self.drag_start_atom = None
            self.selected_atoms.clear()
            self.selected_annotation = None
            self.selected_bond = bond
            current_order = bond.order
            active_order = int(self.bond_order.get())
            # Established sketcher convention: the single-bond tool cycles an
            # existing bond 1 -> 2 -> 3 -> 1. Keep the toolbar on the single
            # tool so repeated clicks continue cycling. Double/triple tools set
            # that exact order instead.
            requested_order = (
                1 if current_order == 3 else current_order + 1
            ) if active_order == 1 else active_order
            if current_order != requested_order:
                self.save_state()
                bond.order = requested_order
                self._invalidate_validation()
                self._redraw_canvas()
                labels = {1: "single", 2: "double", 3: "triple"}
                self._set_status(
                    f"Bond changed from {labels[current_order]} to "
                    f"{labels[requested_order]}. Run Check structure to review it."
                )
            else:
                self._redraw_canvas(refresh_chemistry=False)
                self._set_status(
                    f"Bond selected (order {bond.order}). Choose — to cycle, or = / ≡ to set an exact order."
                )
            return

        if mode == "draw":
            if atom is not None:
                if self.pending_bond_atom in self.atoms and self.pending_bond_atom is not atom:
                    self._create_or_update_bond(self.pending_bond_atom, atom)
                    self.pending_bond_atom = None
                    self.drag_start_atom = None
                    self.selected_atoms = {atom}
                    self.selected_bond = None
                    self.selected_annotation = None
                    self._redraw_canvas(refresh_chemistry=False)
                    return
                self.pending_bond_atom = atom
                self.drag_start_atom = atom
                self.drag_moved = False
                self.selected_atoms = {atom}
                self.selected_bond = None
                self.selected_annotation = None
                self._redraw_canvas(refresh_chemistry=False)
            else:
                anchor = self.pending_bond_atom if self.pending_bond_atom in self.atoms else None
                if anchor is not None:
                    self._add_atom_and_bond(anchor, event.x, event.y)
                    self.pending_bond_atom = None
                else:
                    self.save_state()
                    new_atom = Atom(event.x, event.y, self.selected_element.get())
                    self.atoms.append(new_atom)
                    self.selected_atoms = {new_atom}
                    self.selected_bond = None
                    self.selected_annotation = None
                    self._invalidate_validation()
                    self._redraw_canvas()

        elif mode == "erase":
            if atom is not None or bond is not None or annotation is not None:
                self.save_state()
                self._delete_object(atom=atom, bond=bond, annotation=annotation)
                if atom is not None or bond is not None:
                    self._invalidate_validation()
                self._redraw_canvas(refresh_chemistry=(atom is not None or bond is not None))

        elif mode == "move":
            self.pending_bond_atom = None
            self.move_last = (event.x, event.y)
            self.move_undo_saved = False
            self.drag_moved = False
            self.move_before_state = self._capture_state()
            self.moving_annotation = None
            if atom is not None:
                if atom in self.selected_atoms and len(self.selected_atoms) > 1:
                    move_seeds = list(self.selected_atoms)
                else:
                    self.selected_atoms = {atom}
                    move_seeds = [atom]
                self.selected_bond = None
                self.selected_annotation = None
                self.move_component = self._component_union(move_seeds)
                self.drag_start_atom = atom
            elif bond is not None:
                if self.selected_atoms and (bond.atom1 in self.selected_atoms or
                                            bond.atom2 in self.selected_atoms):
                    move_seeds = list(self.selected_atoms)
                else:
                    self.selected_atoms = {bond.atom1}
                    move_seeds = [bond.atom1]
                self.selected_bond = None
                self.selected_annotation = None
                self.move_component = self._component_union(move_seeds)
                self.drag_start_atom = bond.atom1
            elif annotation is not None:
                self.selected_atoms.clear()
                self.selected_bond = None
                self.selected_annotation = annotation
                self.moving_annotation = annotation
                self.move_component = []
                self.drag_start_atom = None
            else:
                self.selected_atoms.clear()
                self.selected_bond = None
                self.selected_annotation = None
                self.move_component = []
                self.drag_start_atom = None
            self._redraw_canvas(refresh_chemistry=False)

    def on_drag(self, event):
        self.last_canvas_pos = (event.x, event.y)
        if self.pending_placement and self.placement_start is not None:
            sx, sy = self.placement_start
            if math.hypot(event.x - sx, event.y - sy) >= max(12.0, self.BOND_LENGTH * 0.35):
                self.placement_dragged = True
            anchor = self.placement_start_atom
            self._placement_preview_geometry(event.x, event.y, anchor=anchor,
                                             dragged=self.placement_dragged,
                                             bond=self.placement_start_bond)
            return
        if self.annotation_start is not None and self.tool.get() in ("arrow", "equilibrium"):
            self._draw_annotation_preview(event.x, event.y)
            return

        if self.tool.get() == "select" and self.selection_start is not None:
            x1, y1 = self.selection_start
            if math.hypot(event.x - x1, event.y - y1) >= 4:
                self._clear_temp_preview()
                self.temp_ids.append(self.canvas.create_rectangle(
                    x1, y1, event.x, event.y,
                    outline="#2674D9", width=1, dash=(4, 3), fill=""))
            return

        if self.tool.get() == "draw" and self.drag_start_atom is not None:
            if math.hypot(event.x - self.drag_start_atom.x,
                          event.y - self.drag_start_atom.y) > 3:
                self.drag_moved = True
            self._clear_temp_preview()
            x2, y2 = self.snap_angle(self.drag_start_atom.x, self.drag_start_atom.y,
                                     event.x, event.y)
            self.temp_ids.append(self.canvas.create_line(
                self.drag_start_atom.x, self.drag_start_atom.y, x2, y2,
                fill="#7A8699", dash=(4, 3), width=2))

        elif self.tool.get() == "move" and self.move_last is not None:
            dx, dy = event.x - self.move_last[0], event.y - self.move_last[1]
            if abs(dx) + abs(dy) > 0:
                self.drag_moved = True
                if not self.move_undo_saved:
                    self._push_snapshot(self.move_before_state)
                    self.move_undo_saved = True
                    if self.moving_annotation is None:
                        self._invalidate_validation()
                if self.moving_annotation is not None:
                    self.moving_annotation.move_by(dx, dy)
                else:
                    for atom in self.move_component:
                        atom.x += dx
                        atom.y += dy
                self.move_last = (event.x, event.y)
                self._redraw_canvas(refresh_chemistry=False)

    def on_release(self, event):
        self.last_canvas_pos = (event.x, event.y)
        if self.pending_placement and self.placement_start is not None:
            self._finish_placement(event.x, event.y)
            return
        if self.annotation_start is not None and self.tool.get() in ("arrow", "equilibrium"):
            x1, y1 = self.annotation_start
            self._clear_temp_preview()
            self.annotation_start = None
            if math.hypot(event.x - x1, event.y - y1) >= 20:
                self.save_state()
                self.annotations.append(Annotation(self.tool.get(), x1, y1, event.x, event.y))
                self._redraw_canvas(refresh_chemistry=False)
            return

        if self.tool.get() == "select" and self.selection_start is not None:
            x1, y1 = self.selection_start
            dragged = math.hypot(event.x - x1, event.y - y1) >= 5
            if dragged:
                left, right = sorted((x1, event.x))
                top, bottom = sorted((y1, event.y))
                in_box = {atom for atom in self.atoms
                          if left <= atom.x <= right and top <= atom.y <= bottom}
                self.selected_atoms = (self.selection_base_atoms | in_box
                                       if self.selection_additive else in_box)
                self.selected_bond = None
                self.selected_annotation = None
                if self.selected_atoms:
                    self._set_status(
                        f"Selected {len(self.selected_atoms)} atom(s). Choose Move and drag a selected atom to move the connected fragment(s)."
                    )
                else:
                    self._set_status("No atoms inside selection box.")
            else:
                atom = self.find_atom_at(event.x, event.y)
                bond = None if atom else self.find_bond_at(event.x, event.y)
                annotation = None if atom or bond else self.find_annotation_at(event.x, event.y)
                if atom is not None:
                    if self.selection_additive:
                        self.selected_atoms = set(self.selection_base_atoms)
                        if atom in self.selected_atoms:
                            self.selected_atoms.remove(atom)
                        else:
                            self.selected_atoms.add(atom)
                    else:
                        self.selected_atoms = {atom}
                    self.selected_bond = None
                    self.selected_annotation = None
                    self._set_status(f"Selected atom: {atom.element}. Shift-click to add or remove atoms.")
                elif bond is not None:
                    self.selected_atoms.clear()
                    self.selected_bond = bond
                    self.selected_annotation = None
                    self.bond_order.set(bond.order)
                    self._set_status(
                        f"Selected {('single', 'double', 'triple')[bond.order - 1]} bond. "
                        "Click —, =, or ≡ to change this bond explicitly."
                    )
                elif annotation is not None:
                    self.selected_atoms.clear()
                    self.selected_bond = None
                    self.selected_annotation = annotation
                    self._set_status("Selected reaction annotation. Use Move to drag it.")
                else:
                    self.selected_atoms.clear()
                    self.selected_bond = None
                    self.selected_annotation = None
                    self._set_status("Selection cleared.")

            self.selection_start = None
            self.selection_base_atoms.clear()
            self._clear_temp_preview()
            self._redraw_canvas(refresh_chemistry=False)
            return

        self._clear_temp_preview()
        if self.tool.get() == "draw" and self.drag_start_atom is not None:
            source = self.drag_start_atom
            target = self.find_atom_at(event.x, event.y)
            was_drag = self.drag_moved
            if was_drag and target is not source:
                if target is not None:
                    self._create_or_update_bond(source, target)
                    self.selected_atoms = {target}
                    self.pending_bond_atom = None
                else:
                    self._add_atom_and_bond(source, event.x, event.y)
                    self.pending_bond_atom = None
            self.drag_start_atom = None
            self.drag_moved = False

        elif self.tool.get() == "move":
            if self.move_undo_saved and self.drag_moved:
                self._set_status("Moved. Run Check structure to refresh the review.")
            self.drag_start_atom = None
            self.move_component = []
            self.move_last = None
            self.move_before_state = None
            self.move_undo_saved = False
            self.moving_annotation = None
            self.drag_moved = False

    def _draw_annotation_preview(self, x2, y2):
        self._clear_temp_preview()
        if self.annotation_start is None:
            return
        x1, y1 = self.annotation_start
        if self.tool.get() == "equilibrium":
            self.temp_ids.append(self.canvas.create_line(x1, y1 - 3, x2, y2 - 3,
                                                         arrow=tk.LAST, width=2,
                                                         fill="#7A8699", dash=(4, 3)))
            self.temp_ids.append(self.canvas.create_line(x2, y2 + 3, x1, y1 + 3,
                                                         arrow=tk.LAST, width=2,
                                                         fill="#7A8699", dash=(4, 3)))
        else:
            self.temp_ids.append(self.canvas.create_line(x1, y1, x2, y2, arrow=tk.LAST,
                                                         width=2, fill="#7A8699", dash=(4, 3)))

    def _clear_temp_preview(self):
        for item_id in self.temp_ids:
            self.canvas.delete(item_id)
        self.temp_ids = []

    def on_right_click(self, event):
        atom = self.find_atom_at(event.x, event.y)
        bond = None if atom else self.find_bond_at(event.x, event.y)
        annotation = None if atom or bond else self.find_annotation_at(event.x, event.y)
        if atom is not None or bond is not None or annotation is not None:
            self.save_state()
            self._delete_object(atom=atom, bond=bond, annotation=annotation)
            if atom is not None or bond is not None:
                self._invalidate_validation()
            self._redraw_canvas(refresh_chemistry=(atom is not None or bond is not None))

    def cancel_pending(self):
        self.pending_bond_atom = None
        self.pending_placement = None
        self.placement_start = None
        self.placement_start_atom = None
        self.placement_start_bond = None
        self.placement_dragged = False
        self._clear_placement_preview()
        self.drag_start_atom = None
        self.annotation_start = None
        self.move_component = []
        self.move_last = None
        self.moving_annotation = None
        self.selection_start = None
        self.selection_base_atoms.clear()
        self.selected_atoms.clear()
        self.selected_bond = None
        self.selected_annotation = None
        self._clear_temp_preview()
        self._redraw_canvas(refresh_chemistry=False)
        self._set_status("Cancelled pending action and cleared selection.")

    # ------------------------------------------------------ placement engine
    def _add_atom_and_bond(self, anchor, target_x, target_y):
        def geometry(ux, uy):
            return [(anchor.x + self.BOND_LENGTH * ux,
                     anchor.y + self.BOND_LENGTH * uy, self.selected_element.get())]

        ux, uy, _points, crowded = self._best_attached_direction(anchor, geometry)
        self.save_state()
        new_atom = Atom(anchor.x + self.BOND_LENGTH * ux,
                        anchor.y + self.BOND_LENGTH * uy,
                        self.selected_element.get())
        self.atoms.append(new_atom)
        self.bonds.append(Bond(anchor, new_atom, self.bond_order.get()))
        self.selected_atoms = {new_atom}
        self.selected_bond = None
        self.selected_annotation = None
        self._invalidate_validation()
        self._redraw_canvas()
        if crowded:
            self._set_status("Placed at the least crowded angle; check for overlap and move if needed.")

    def _create_or_update_bond(self, atom1, atom2):
        if atom1 is atom2:
            return
        existing = next((bond for bond in atom1.bonds
                         if bond.atom1 is atom2 or bond.atom2 is atom2), None)
        new_order = int(self.bond_order.get())
        if existing is not None and existing.order == new_order:
            self.selected_bond = existing
            self._redraw_canvas(refresh_chemistry=False)
            return
        self.save_state()
        if existing is not None:
            existing.order = new_order
        else:
            self.bonds.append(Bond(atom1, atom2, new_order))
        self.selected_bond = None
        self._invalidate_validation()
        self._redraw_canvas()

    def _ring_points_unattached(self, cx, cy, size):
        radius = self.BOND_LENGTH / (2.0 * math.sin(math.pi / size))
        start = -math.pi / 2
        return [(cx + radius * math.cos(start + i * 2 * math.pi / size),
                 cy + radius * math.sin(start + i * 2 * math.pi / size), "C")
                for i in range(size)]

    def _ring_points_attached(self, anchor, ux, uy, size):
        radius = self.BOND_LENGTH / (2.0 * math.sin(math.pi / size))
        center_x = anchor.x + (self.BOND_LENGTH + radius) * ux
        center_y = anchor.y + (self.BOND_LENGTH + radius) * uy
        start = math.atan2(uy, ux) + math.pi
        return [(center_x + radius * math.cos(start + i * 2 * math.pi / size),
                 center_y + radius * math.sin(start + i * 2 * math.pi / size), "C")
                for i in range(size)]

    def _new_ring(self, size, aromatic=False):
        anchor = self._anchor_atom()
        if anchor is not None:
            def geometry(ux, uy):
                return self._ring_points_attached(anchor, ux, uy, size)
            ux, uy, points, crowded = self._best_attached_direction(anchor, geometry)
        else:
            x, y = self.last_canvas_pos
            if x < 5 or y < 5:
                x, y = self._canvas_size()[0] / 2, self._canvas_size()[1] / 2
            ox, oy, points, crowded = self._best_unattached_origin(
                x, y, lambda cx, cy: self._ring_points_unattached(cx, cy, size))

        self.save_state()
        ring_atoms = []
        for x, y, element in points:
            atom = Atom(x, y, element)
            self.atoms.append(atom)
            ring_atoms.append(atom)
        for i in range(size):
            order = 2 if aromatic and i % 2 == 0 else 1
            self.bonds.append(Bond(ring_atoms[i], ring_atoms[(i + 1) % size], order))
        if anchor is not None:
            self.bonds.append(Bond(anchor, ring_atoms[0], 1))

        self.selected_atoms = {ring_atoms[0]}
        self.selected_bond = None
        self.selected_annotation = None
        self.pending_bond_atom = ring_atoms[0]
        self.tool.set("draw")
        self._tool_changed()
        self._invalidate_validation()
        self._redraw_canvas()
        if crowded:
            self._set_status("Ring placed at the least crowded position; inspect spacing and move if needed.")
        else:
            self._set_status("Ring placed. No existing atoms were moved.")

    def add_benzene(self):
        self._new_ring(6, aromatic=True)

    def add_cyclohexane(self):
        self._new_ring(6, aromatic=False)

    def add_cyclopentane(self):
        self._new_ring(5, aromatic=False)

    def _group_geometry_unattached(self, group_type, x, y):
        length = self.BOND_LENGTH
        if group_type == "CH3":
            return [(x, y, "C")]
        if group_type == "OH":
            return [(x, y, "O"), (x + 30, y, "H")]
        if group_type == "NH2":
            return [(x, y, "N")]
        if group_type == "COOH":
            return [(x, y, "C"),
                    (x + length * math.cos(-math.pi / 3), y + length * math.sin(-math.pi / 3), "O"),
                    (x + length * math.cos(math.pi / 3), y + length * math.sin(math.pi / 3), "O")]
        return []

    def _group_geometry_attached(self, anchor, group_type, ux, uy):
        length = self.BOND_LENGTH
        angle = math.atan2(uy, ux)
        gx, gy = anchor.x + length * ux, anchor.y + length * uy
        if group_type in ("CH3", "OH", "NH2"):
            element = {"CH3": "C", "OH": "O", "NH2": "N"}[group_type]
            return [(gx, gy, element)]
        if group_type == "COOH":
            return [(gx, gy, "C"),
                    (gx + length * math.cos(angle + math.pi / 3),
                     gy + length * math.sin(angle + math.pi / 3), "O"),
                    (gx + length * math.cos(angle - math.pi / 3),
                     gy + length * math.sin(angle - math.pi / 3), "O")]
        return []

    def add_functional_group(self, group_type):
        anchor = self._anchor_atom()
        if anchor is not None:
            def geometry(ux, uy):
                return self._group_geometry_attached(anchor, group_type, ux, uy)
            ux, uy, points, crowded = self._best_attached_direction(anchor, geometry)
        else:
            x, y = self.last_canvas_pos
            if x < 5 or y < 5:
                x, y = self._canvas_size()[0] / 2, self._canvas_size()[1] / 2
            ox, oy, points, crowded = self._best_unattached_origin(
                x, y, lambda px, py: self._group_geometry_unattached(group_type, px, py))
            x, y = ox, oy

        self.save_state()
        if anchor is not None:
            if group_type in ("CH3", "OH", "NH2"):
                gx, gy, element = points[0]
                group_atom = Atom(gx, gy, element)
                self.atoms.append(group_atom)
                self.bonds.append(Bond(anchor, group_atom, 1))
                focus_atom = group_atom
            elif group_type == "COOH":
                gx, gy, _ = points[0]
                carboxyl_c = Atom(gx, gy, "C")
                o1 = Atom(*points[1][:2], "O")
                o2 = Atom(*points[2][:2], "O")
                self.atoms.extend((carboxyl_c, o1, o2))
                self.bonds.extend((Bond(anchor, carboxyl_c, 1),
                                   Bond(carboxyl_c, o1, 2),
                                   Bond(carboxyl_c, o2, 1)))
                focus_atom = carboxyl_c
            else:
                return
        else:
            if group_type == "CH3":
                atom = Atom(x, y, "C")
                self.atoms.append(atom)
                focus_atom = atom
            elif group_type == "OH":
                ox, oy, _ = points[0]
                hx, hy, _ = points[1]
                oxygen, hydrogen = Atom(ox, oy, "O"), Atom(hx, hy, "H")
                self.atoms.extend((oxygen, hydrogen))
                self.bonds.append(Bond(oxygen, hydrogen, 1))
                focus_atom = oxygen
            elif group_type == "NH2":
                atom = Atom(x, y, "N")
                self.atoms.append(atom)
                focus_atom = atom
            elif group_type == "COOH":
                cx, cy, _ = points[0]
                c = Atom(cx, cy, "C")
                o1 = Atom(points[1][0], points[1][1], "O")
                o2 = Atom(points[2][0], points[2][1], "O")
                self.atoms.extend((c, o1, o2))
                self.bonds.extend((Bond(c, o1, 2), Bond(c, o2, 1)))
                focus_atom = c
            else:
                return

        self.selected_atoms = {focus_atom}
        self.selected_bond = None
        self.selected_annotation = None
        self.pending_bond_atom = focus_atom
        self.tool.set("draw")
        self._tool_changed()
        self._invalidate_validation()
        self._redraw_canvas()
        if crowded:
            self._set_status("Group placed at the least crowded position; inspect spacing and move if needed.")
        else:
            self._set_status("Functional group placed. Its bonds and charges were not auto-corrected.")

    def apply_charge(self):
        selected = [atom for atom in self.atoms if atom in self.selected_atoms]
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
        for atom in selected:
            atom.charge = charge
        self._invalidate_validation()
        self._redraw_canvas()
        self._set_status("Formal charge changed by user. Run Check structure to review it.")

    # ------------------------------------------------------------ canvas draw
    def _find_simple_cycles(self, max_size=8):
        """Find unique simple cycles up to max_size for drawing geometry only."""
        atom_index = {atom: i for i, atom in enumerate(self.atoms)}
        found = {}

        def canonical_key(path):
            seq = tuple(atom_index[a] for a in path)
            reverse = (seq[0],) + tuple(reversed(seq[1:]))
            return min(seq, reverse)

        for start in self.atoms:
            start_index = atom_index[start]

            def visit(current, path, path_set):
                if len(path) > max_size:
                    return
                for bond in current.bonds:
                    neighbour = bond.atom2 if bond.atom1 is current else bond.atom1
                    if neighbour is start and len(path) >= 3:
                        key = canonical_key(path)
                        found.setdefault(key, list(path))
                    elif (neighbour not in path_set and
                          atom_index[neighbour] > start_index and
                          len(path) < max_size):
                        visit(neighbour, path + [neighbour], path_set | {neighbour})

            visit(start, [start], {start})
        return sorted(found.values(), key=lambda cycle: (len(cycle), tuple(atom_index[a] for a in cycle)))

    @staticmethod
    def _bond_for_atoms(atom1, atom2):
        for bond in atom1.bonds:
            if ((bond.atom1 is atom1 and bond.atom2 is atom2) or
                    (bond.atom1 is atom2 and bond.atom2 is atom1)):
                return bond
        return None

    def _eligible_aromatic_cycle(self, cycle):
        """Return whether the current graph supports aromatic-circle display.

        When RDKit has sanitized the unchanged drawing, use its aromatic bond flags
        for 5- to 7-membered rings (including heteroaromatics). Without RDKit, use
        a deliberately narrow alternating six-membered-ring fallback. This affects
        rendering only; it never changes the editor's bond orders.
        """
        if not 5 <= len(cycle) <= 7:
            return False

        if RDKIT_AVAILABLE and self.chem_mol is not None:
            atom_index = {atom: i for i, atom in enumerate(self.atoms)}
            try:
                for i, atom in enumerate(cycle):
                    j_atom = cycle[(i + 1) % len(cycle)]
                    rd_bond = self.chem_mol.GetBondBetweenAtoms(
                        atom_index[atom], atom_index[j_atom])
                    if rd_bond is None or not rd_bond.GetIsAromatic():
                        return False
                return True
            except (KeyError, RuntimeError, AttributeError):
                pass

        # If sanitization failed (often because an exocyclic double bond was
        # drawn on a still-Kekulized benzene carbon), do not use the alternating
        # six-membered-ring fallback to show an aromatic circle. The circle is
        # reserved for a graph that supports aromaticity; an invalid graph must
        # show its literal bonds so the conflict is visible to the user.
        cycle_atoms = set(cycle)
        for atom in cycle:
            for bond in atom.bonds:
                neighbour = bond.atom2 if bond.atom1 is atom else bond.atom1
                if neighbour not in cycle_atoms and bond.order > 1:
                    return False

        if len(cycle) != 6 or any(atom.element not in ("C", "N") for atom in cycle):
            return False
        orders = []
        for i, atom in enumerate(cycle):
            bond = self._bond_for_atoms(atom, cycle[(i + 1) % len(cycle)])
            if bond is None or bond.order not in (1, 2):
                return False
            orders.append(bond.order)
        return (sum(order == 2 for order in orders) == 3 and
                all(orders[i] != orders[(i + 1) % 6] for i in range(6)))

    def _exocyclic_multiple_bond_suggestion(self, suspect_indices=None):
        """Return a non-destructive, live hint for ring/exocyclic multiple bonds.

        This intentionally does not depend on RDKit declaring the graph invalid.
        Some wrong-for-the-intended-target Kekule drawings still pass local valence
        checks, so we also explain when ring unsaturation remains. No graph data is
        ever edited here.
        """
        if not self.atoms:
            return None

        atom_index = {atom: i + 1 for i, atom in enumerate(self.atoms)}
        hints = []
        seen_hint_keys = set()
        cycles = self._find_simple_cycles(max_size=8)

        for cycle in cycles:
            cycle_atoms = set(cycle)
            ring_bonds = []
            for i, atom in enumerate(cycle):
                bond = self._bond_for_atoms(atom, cycle[(i + 1) % len(cycle)])
                if bond is not None:
                    ring_bonds.append(bond)
            ring_double_bonds = [bond for bond in ring_bonds if bond.order == 2]
            if not ring_double_bonds:
                continue

            # Exocyclic double bonds are bonds from a ring atom to an atom not in
            # this cycle. We keep the external bond and ring bonds conceptually
            # separate so suggestions identify exactly what the user may inspect.
            external_doubles = []
            for ring_atom in cycle:
                for bond in ring_atom.bonds:
                    if bond.order != 2:
                        continue
                    other = bond.atom2 if bond.atom1 is ring_atom else bond.atom1
                    if other not in cycle_atoms:
                        external_doubles.append((ring_atom, other, bond))

            if not external_doubles:
                continue

            for ring_atom, external_atom, _external_bond in external_doubles:
                incident_ring_doubles = [
                    bond for bond in ring_double_bonds
                    if bond.atom1 is ring_atom or bond.atom2 is ring_atom
                ]
                if incident_ring_doubles:
                    ring_bond = incident_ring_doubles[0]
                    other_ring_atom = (ring_bond.atom2 if ring_bond.atom1 is ring_atom
                                       else ring_bond.atom1)
                    key = ("local", frozenset((ring_atom, other_ring_atom)), external_atom)
                    if key not in seen_hint_keys:
                        seen_hint_keys.add(key)
                        hints.append(
                            f"Possible valence conflict at ring atom {atom_index[ring_atom]}: "
                            f"its external {ring_atom.element}={external_atom.element} bond and "
                            f"the in-ring double bond to atom {atom_index[other_ring_atom]} "
                            "share the same atom. Select that in-ring double bond and choose "
                            "— to make it single if that matches your intended structure."
                        )

                # A saturated methylenecyclohexane target has a six-carbon ring
                # made entirely of single bonds, plus one exocyclic C=CH2 double.
                # A current Kekule drawing may still contain other ring doubles
                # without causing a local valence error, so call that out separately.
                if (len(cycle) == 6 and all(a.element == "C" for a in cycle)
                        and external_atom.element == "C"):
                    key = ("saturated-ring", frozenset(cycle), external_atom)
                    if key not in seen_hint_keys:
                        seen_hint_keys.add(key)
                        count = len(ring_double_bonds)
                        hints.append(
                            f"The six-carbon ring still contains {count} in-ring double "
                            f"bond(s), in addition to the external C=C. If you intend a "
                            "saturated methylenecyclohexane derivative (for example, "
                            "1-methyl-3-methylenecyclohexane, C₈H₁₄), every ring bond "
                            "should be single; keep the external =CH₂ double bond. "
                            "Select each in-ring double bond and choose — manually. "
                            "Changing only one ring bond would not produce that target."
                        )

        return "\n\n".join(hints) if hints else None

    def _cycle_centroid(self, cycle):
        return (sum(atom.x for atom in cycle) / len(cycle),
                sum(atom.y for atom in cycle) / len(cycle))

    def _inner_normal_sign(self, bond, x1, y1, x2, y2, px, py):
        """Choose the normal pointing into the smallest ring containing a bond."""
        candidates = [cycle for cycle in self._drawing_cycles
                      if bond.atom1 in cycle and bond.atom2 in cycle]
        if not candidates:
            return 0
        cycle = min(candidates, key=len)
        cx, cy = self._cycle_centroid(cycle)
        mx, my = (x1 + x2) / 2.0, (y1 + y2) / 2.0
        dot = (cx - mx) * px + (cy - my) * py
        return 1 if dot >= 0 else -1

    def _draw_aromatic_circle(self, cycle):
        cx, cy = self._cycle_centroid(cycle)
        mean_radius = sum(math.hypot(atom.x - cx, atom.y - cy) for atom in cycle) / len(cycle)
        # Keep the circle comfortably inside the ring's inner perimeter.
        radius = max(8.0, mean_radius * 0.52)
        colour = "#2674D9" if all(atom in self.selected_atoms for atom in cycle) else "#202124"
        self.canvas.create_oval(cx - radius, cy - radius, cx + radius, cy + radius,
                                outline=colour, width=2 if colour == "#2674D9" else 1.8,
                                fill="")

    def _redraw_canvas(self, refresh_chemistry=True):
        if refresh_chemistry:
            self._refresh_chemistry_cache()
        self.canvas.delete("all")
        for atom in self.atoms:
            atom.canvas_id = None
            atom.text_id = None
        for bond in self.bonds:
            bond.canvas_ids = []
        for annotation in self.annotations:
            annotation.canvas_ids = []

        self._drawing_cycles = self._find_simple_cycles(max_size=8)
        aromatic_cycles = []
        self._aromatic_display_bonds = set()
        if self.aromatic_circle.get():
            aromatic_cycles = [cycle for cycle in self._drawing_cycles
                               if self._eligible_aromatic_cycle(cycle)]
            for cycle in aromatic_cycles:
                for i, atom in enumerate(cycle):
                    bond = self._bond_for_atoms(atom, cycle[(i + 1) % len(cycle)])
                    if bond is not None:
                        self._aromatic_display_bonds.add(bond)

        # Annotation layer first: reaction arrows sit behind molecular structures.
        for annotation in self.annotations:
            self._draw_annotation(annotation)
        for bond in self.bonds:
            self._draw_bond(bond)
        # The aromatic circle is a display convention only. Underlying Kekule
        # single/double orders remain intact for editing, formulas and validation.
        for cycle in aromatic_cycles:
            self._draw_aromatic_circle(cycle)
        for atom in self.atoms:
            self._draw_atom(atom)
        self._update_panel()

    def _atom_has_label(self, atom):
        return atom.element != "C" or not atom.bonds or atom.charge != 0

    def _atom_label(self, atom):
        text = atom.element
        if atom.element != "H" and atom.implicit_h > 0:
            text += "H"
            if atom.implicit_h > 1:
                text += str(atom.implicit_h).translate(SUBSCRIPTS)
        if atom.charge:
            magnitude = abs(atom.charge)
            sign = "+" if atom.charge > 0 else "−"
            text += (str(magnitude).translate(SUBSCRIPTS) if magnitude > 1 else "") + sign
        return text

    def _draw_atom(self, atom):
        selected = atom in self.selected_atoms
        idx = self.atoms.index(atom)
        suspect = idx in self.invalid_atom_indices and self.validation_state == "invalid"

        if self._atom_has_label(atom):
            label = self._atom_label(atom)
            width = max(15, 4.7 * len(label) + 7)
            self.canvas.create_oval(atom.x - width / 2, atom.y - 11,
                                    atom.x + width / 2, atom.y + 11,
                                    fill="white", outline="white")
            colour = "#B42318" if suspect else ELEMENT_COLOURS.get(atom.element, "#202124")
            atom.text_id = self.canvas.create_text(
                atom.x, atom.y, text=label, font=("Arial", 11, "bold"), fill=colour)

        # Draw selection last so the white label backing cannot hide the outline.
        if selected:
            r = 13 if self._atom_has_label(atom) else 8
            atom.canvas_id = self.canvas.create_oval(
                atom.x - r, atom.y - r, atom.x + r, atom.y + r,
                outline="#2674D9", width=2, fill="")

    def _bond_endpoints(self, bond):
        a, b = bond.atom1, bond.atom2
        dx, dy = b.x - a.x, b.y - a.y
        length = math.hypot(dx, dy)
        if length < 1e-6:
            return a.x, a.y, b.x, b.y, 0.0, 0.0, 0.0
        ux, uy = dx / length, dy / length
        offset_a = 10 if self._atom_has_label(a) else 0
        offset_b = 10 if self._atom_has_label(b) else 0
        return (a.x + ux * offset_a, a.y + uy * offset_a,
                b.x - ux * offset_b, b.y - uy * offset_b, ux, uy, length)

    def _draw_bond(self, bond):
        x1, y1, x2, y2, ux, uy, length = self._bond_endpoints(bond)
        if length < 1e-6:
            return
        selected = bond is self.selected_bond
        colour = "#2674D9" if selected else "#202124"
        width = 3 if selected else 2
        px, py = -uy, ux

        # In aromatic-circle mode, draw the perimeter as single strokes and add
        # the aromatic circle after all bond strokes. Bond.order is not modified.
        if bond in self._aromatic_display_bonds:
            bond.canvas_ids.append(self.canvas.create_line(
                x1, y1, x2, y2, fill=colour, width=width, capstyle=tk.ROUND))
            return

        if bond.order == 1:
            bond.canvas_ids.append(self.canvas.create_line(
                x1, y1, x2, y2, fill=colour, width=width, capstyle=tk.ROUND))
        elif bond.order == 2:
            offset = 3.0
            # For double bonds inside a ring, retain the outer edge and offset
            # the second stroke toward the ring interior. Outside rings, use the
            # conventional centered pair of parallel lines.
            inner_sign = self._inner_normal_sign(bond, x1, y1, x2, y2, px, py)
            if inner_sign:
                bond.canvas_ids.append(self.canvas.create_line(
                    x1, y1, x2, y2, fill=colour, width=width, capstyle=tk.ROUND))
                bond.canvas_ids.append(self.canvas.create_line(
                    x1 + px * offset * inner_sign, y1 + py * offset * inner_sign,
                    x2 + px * offset * inner_sign, y2 + py * offset * inner_sign,
                    fill=colour, width=width, capstyle=tk.ROUND))
            else:
                bond.canvas_ids.append(self.canvas.create_line(
                    x1 + px * offset, y1 + py * offset, x2 + px * offset, y2 + py * offset,
                    fill=colour, width=width, capstyle=tk.ROUND))
                bond.canvas_ids.append(self.canvas.create_line(
                    x1 - px * offset, y1 - py * offset, x2 - px * offset, y2 - py * offset,
                    fill=colour, width=width, capstyle=tk.ROUND))
        elif bond.order == 3:
            offset = 4.2
            bond.canvas_ids.append(self.canvas.create_line(x1, y1, x2, y2,
                                                           fill=colour, width=width,
                                                           capstyle=tk.ROUND))
            bond.canvas_ids.append(self.canvas.create_line(
                x1 + px * offset, y1 + py * offset, x2 + px * offset, y2 + py * offset,
                fill=colour, width=width, capstyle=tk.ROUND))
            bond.canvas_ids.append(self.canvas.create_line(
                x1 - px * offset, y1 - py * offset, x2 - px * offset, y2 - py * offset,
                fill=colour, width=width, capstyle=tk.ROUND))

    def _draw_annotation(self, annotation):
        selected = annotation is self.selected_annotation
        colour = "#2674D9" if selected else "#202124"
        width = 2.5 if selected else 2
        if annotation.kind == "arrow":
            annotation.canvas_ids.append(self.canvas.create_line(
                annotation.x1, annotation.y1, annotation.x2, annotation.y2,
                arrow=tk.LAST, width=width, fill=colour, capstyle=tk.ROUND))
        elif annotation.kind == "equilibrium":
            annotation.canvas_ids.append(self.canvas.create_line(
                annotation.x1, annotation.y1 - 3, annotation.x2, annotation.y2 - 3,
                arrow=tk.LAST, width=width, fill=colour, capstyle=tk.ROUND))
            annotation.canvas_ids.append(self.canvas.create_line(
                annotation.x2, annotation.y2 + 3, annotation.x1, annotation.y1 + 3,
                arrow=tk.LAST, width=width, fill=colour, capstyle=tk.ROUND))
        else:
            content = annotation.text or ("+" if annotation.kind == "plus" else "=")
            font_size = 24 if annotation.kind in ("plus", "equals") else 12
            font = ("Arial", font_size, "bold" if annotation.kind != "text" else "normal")
            annotation.canvas_ids.append(self.canvas.create_text(
                annotation.x1, annotation.y1, text=content, fill=colour, font=font,
                justify=tk.CENTER))

    # --------------------------------------------------------- deletion/tools
    def _delete_object(self, atom=None, bond=None, annotation=None):
        if atom is not None and atom in self.atoms:
            for attached in list(atom.bonds):
                self._delete_bond(attached)
            self.atoms.remove(atom)
            self.selected_atoms.discard(atom)
            if self.pending_bond_atom is atom:
                self.pending_bond_atom = None
        elif bond is not None:
            self._delete_bond(bond)
        elif annotation is not None and annotation in self.annotations:
            self.annotations.remove(annotation)
            if self.selected_annotation is annotation:
                self.selected_annotation = None

    def _delete_bond(self, bond):
        if bond in bond.atom1.bonds:
            bond.atom1.bonds.remove(bond)
        if bond in bond.atom2.bonds:
            bond.atom2.bonds.remove(bond)
        if bond in self.bonds:
            self.bonds.remove(bond)
        if self.selected_bond is bond:
            self.selected_bond = None

    def delete_selected(self):
        selected = [atom for atom in self.atoms if atom in self.selected_atoms]
        if selected:
            self.save_state()
            for atom in selected:
                if atom in self.atoms:
                    self._delete_object(atom=atom)
            self.selected_atoms.clear()
            self.selected_bond = None
            self.selected_annotation = None
            self._invalidate_validation()
            self._redraw_canvas()
            return
        if self.selected_bond is not None:
            self.save_state()
            self._delete_bond(self.selected_bond)
            self._invalidate_validation()
            self._redraw_canvas()
            return
        if self.selected_annotation is not None:
            self.save_state()
            self._delete_object(annotation=self.selected_annotation)
            self._redraw_canvas(refresh_chemistry=False)

    def delete_at(self, x, y):
        atom = self.find_atom_at(x, y)
        bond = None if atom else self.find_bond_at(x, y)
        annotation = None if atom or bond else self.find_annotation_at(x, y)
        if atom is not None or bond is not None or annotation is not None:
            self._delete_object(atom=atom, bond=bond, annotation=annotation)
            return True
        return False

    def clear_all(self):
        if self.pending_placement is not None:
            self.pending_placement = None
            self.placement_start = None
            self.placement_start_atom = None
            self.placement_start_bond = None
            self.placement_dragged = False
            self._clear_placement_preview()
        if not self.atoms and not self.annotations:
            self._set_status("Cleared pending placement.")
            return
        if not messagebox.askyesno("Clear drawing", "Clear all atoms, bonds and reaction annotations?",
                                   parent=self.root):
            return
        self.save_state()
        had_chemistry = bool(self.atoms)
        self.atoms.clear()
        self.bonds.clear()
        self.annotations.clear()
        self.selected_atoms.clear()
        self.selected_bond = None
        self.selected_annotation = None
        self.pending_bond_atom = None
        if had_chemistry:
            self._invalidate_validation()
        self._redraw_canvas(refresh_chemistry=had_chemistry)

    # -------------------------------------------------------------- connectivity
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

    def _overlapping_atom_pairs(self):
        pairs = []
        for i, atom1 in enumerate(self.atoms):
            for j in range(i + 1, len(self.atoms)):
                atom2 = self.atoms[j]
                if atom1.distance_to(atom2.x, atom2.y) < 12:
                    pairs.append((i, j))
        return pairs

    # -------------------------------------------------------------- copy/paste
    def _atoms_for_copy(self):
        if not self.selected_atoms:
            return []
        if len(self.selected_atoms) == 1:
            return self.get_connected_component(next(iter(self.selected_atoms)))
        return [atom for atom in self.atoms if atom in self.selected_atoms]

    def copy_selection(self):
        if self.selected_annotation is not None:
            a = self.selected_annotation
            self.clipboard = {"type": "annotation",
                              "annotation": (a.kind, a.x1, a.y1, a.x2, a.y2, a.text)}
            self.paste_count = 0
            self._set_status("Copied reaction annotation.")
            return
        selected = self._atoms_for_copy()
        if not selected:
            self._set_status("Select an atom/fragment or an annotation before copying.")
            return
        idx = {atom: i for i, atom in enumerate(selected)}
        self.clipboard = {
            "type": "molecule",
            "atoms": [(a.x, a.y, a.element, a.charge) for a in selected],
            "bonds": [(idx[b.atom1], idx[b.atom2], b.order) for b in self.bonds
                      if b.atom1 in idx and b.atom2 in idx],
        }
        self.paste_count = 0
        self._set_status(f"Copied {len(selected)} atom(s).")

    def paste_selection(self):
        if not self.clipboard:
            return
        self.save_state()
        self.paste_count += 1
        offset = 32 * self.paste_count
        if self.clipboard.get("type") == "annotation":
            kind, x1, y1, x2, y2, text = self.clipboard["annotation"]
            pasted = Annotation(kind, x1 + offset, y1 + offset,
                                x2 + offset, y2 + offset, text)
            self.annotations.append(pasted)
            self.selected_annotation = pasted
            self.selected_atoms.clear()
            self.selected_bond = None
            self._redraw_canvas(refresh_chemistry=False)
            self._set_status("Pasted reaction annotation.")
            return

        first_new = len(self.atoms)
        pasted_atoms = []
        for x, y, element, charge in self.clipboard["atoms"]:
            atom = Atom(x + offset, y + offset, element, charge)
            self.atoms.append(atom)
            pasted_atoms.append(atom)
        for i, j, order in self.clipboard["bonds"]:
            self.bonds.append(Bond(self.atoms[first_new + i], self.atoms[first_new + j], order))
        self.selected_atoms = set(pasted_atoms)
        self.selected_bond = None
        self.selected_annotation = None
        self.pending_bond_atom = None
        self._invalidate_validation()
        self._redraw_canvas()
        self._set_status(f"Pasted {len(pasted_atoms)} atom(s).")

    # --------------------------------------------------------------- panel
    def _update_panel(self):
        formula = self.calculate_molecular_formula()
        weight = self.calculate_molecular_weight()
        smiles = self.generate_smiles()
        self.formula_label.config(text=f"Formula (all fragments): {formula}")
        if weight is None:
            weight_text = "—"
        elif not RDKIT_AVAILABLE:
            weight_text = f"~{weight} g/mol (estimate)"
        else:
            weight_text = f"{weight} g/mol"
        self.weight_label.config(text=f"Average MW: {weight_text}")
        self.smiles_label.config(text=f"SMILES: {smiles}")
        self.atom_count_label.config(text=f"Atoms: {len(self.atoms)}")
        self.bond_count_label.config(text=f"Bonds: {len(self.bonds)}")
        self.fragment_count_label.config(text=f"Fragments: {len(self.get_connected_components())}")

        if self.validation_state == "unchecked":
            self.validation_label.config(text="Not checked — click Check structure", fg="#5B6573")
        elif self.validation_state == "valid":
            self.validation_label.config(text="✓ Chemistry checks passed", fg="#187344")
        elif self.validation_state == "limited":
            self.validation_label.config(text="Limited checks only", fg="#9A6700")
        else:
            self.validation_label.config(text="⚠ Needs review", fg="#B42318")

    def _set_diagnostics(self, lines):
        self.diagnostics_text.config(state=tk.NORMAL)
        self.diagnostics_text.delete("1.0", tk.END)
        self.diagnostics_text.insert(tk.END, "\n\n".join(lines))
        self.diagnostics_text.config(state=tk.DISABLED)
        self._refresh_suggestion_action()

    def _saturated_ring_suggestions(self):
        """Return safe, explicit saturation options for six-carbon exocyclic-alkene rings.

        This is a user-invoked suggestion for cases like methyl-methylenecyclohexane.
        Fused/shared-edge rings are excluded so one click cannot silently alter a
        neighboring ring. The method does not change any bonds.
        """
        cycles = self._find_simple_cycles(max_size=8)
        if not cycles:
            return []

        edge_use_count = defaultdict(int)
        cycle_bonds = {}
        for cycle in cycles:
            edges = []
            for i, atom in enumerate(cycle):
                other = cycle[(i + 1) % len(cycle)]
                bond = self._bond_for_atoms(atom, other)
                if bond is None:
                    edges = []
                    break
                edge = frozenset((atom, other))
                edges.append((edge, bond))
                edge_use_count[edge] += 1
            cycle_bonds[tuple(cycle)] = edges

        candidates = []
        seen = set()
        for cycle in cycles:
            if len(cycle) != 6 or any(atom.element != "C" for atom in cycle):
                continue
            edges = cycle_bonds.get(tuple(cycle), [])
            if len(edges) != 6:
                continue
            # Do not offer bulk saturation for fused/bridged drawings where a
            # ring edge is also part of another detected cycle.
            if any(edge_use_count[edge] > 1 for edge, _bond in edges):
                continue
            ring_bonds = [bond for _edge, bond in edges]
            if any(bond.order not in (1, 2) for bond in ring_bonds):
                continue
            ring_double_bonds = [bond for bond in ring_bonds if bond.order == 2]
            if not ring_double_bonds:
                continue

            cycle_set = set(cycle)
            for ring_atom in cycle:
                for external_bond in ring_atom.bonds:
                    if external_bond.order != 2:
                        continue
                    external_atom = (external_bond.atom2 if external_bond.atom1 is ring_atom
                                     else external_bond.atom1)
                    if external_atom in cycle_set or external_atom.element != "C":
                        continue
                    # Use the external bond as part of the key to avoid duplicate
                    # recommendations for the same ring/external alkene pair.
                    key = (frozenset(cycle), frozenset((ring_atom, external_atom)))
                    if key in seen:
                        continue
                    seen.add(key)
                    candidates.append({
                        "cycle": tuple(cycle),
                        "ring_bonds": tuple(ring_bonds),
                        "double_bonds": tuple(ring_double_bonds),
                        "ring_atom": ring_atom,
                        "external_atom": external_atom,
                        "external_bond": external_bond,
                    })
        return candidates

    def _refresh_suggestion_action(self):
        """Show the optional action only when there is one unambiguous candidate."""
        if not hasattr(self, "suggestion_action_button") or not hasattr(self, "engine_label"):
            return
        candidates = self._saturated_ring_suggestions()
        if len(candidates) == 1:
            count = len(candidates[0]["double_bonds"])
            self.suggestion_action_button.config(
                text=f"Make ring saturated ({count} bond{'s' if count != 1 else ''})")
            if not self.suggestion_action_button.winfo_manager():
                self.suggestion_action_button.pack(fill=tk.X, pady=(0, 5), before=self.engine_label)
        elif self.suggestion_action_button.winfo_manager():
            self.suggestion_action_button.pack_forget()

    def apply_saturated_ring_suggestion(self):
        """Apply the proposed ring saturation only after an explicit user click/confirmation."""
        candidates = self._saturated_ring_suggestions()
        if len(candidates) != 1:
            self._set_status("No single, unambiguous saturated-ring suggestion is available.")
            self._refresh_suggestion_action()
            return

        candidate = candidates[0]
        double_bonds = candidate["double_bonds"]
        if not double_bonds:
            return
        message = (
            f"Change {len(double_bonds)} double bond(s) inside this six-carbon ring to single bonds?\n\n"
            "The external C=C, atom positions, substituents and charges will be preserved.\n"
            "This is an explicit edit, not an automatic correction, and can be undone."
        )
        if not messagebox.askyesno("Apply suggested ring edit", message, parent=self.root):
            return

        self.save_state()
        for bond in double_bonds:
            bond.order = 1
        self.selected_bond = None
        self._invalidate_validation()
        self._redraw_canvas()
        self._set_status(
            f"Applied your choice: changed {len(double_bonds)} in-ring double bond(s) to single; "
            "the external C=C was preserved. Use Undo to revert."
        )


def main():
    root = tk.Tk()
    MoleculeEditor(root)
    root.mainloop()


if __name__ == "__main__":
    main()
