 Molecule & Reaction Editor

A lightweight, offline desktop editor for drawing 2D chemical structures and
reaction schemes. It is implemented in one Python file with Tkinter; RDKit adds
chemical validation, molecular properties, SMILES import, 2D cleanup, and
`.mol` export.

 Requirements

- Python 3 with Tkinter available.
- RDKit for the chemistry features. Install it from `requirements.txt`.

The editor can still draw and edit structures without RDKit, but chemistry
checks are limited and RDKit-dependent features are unavailable. On Windows,
the standard Python installer normally includes Tcl/Tk; if Tkinter is missing,
install or modify Python to include **Tcl/Tk and IDLE**.

 Run on Windows

Open PowerShell in the project folder and run:

```powershell
py -m venv .venv
.\.venv\Scripts\python.exe -m pip install --upgrade pip
.\.venv\Scripts\python.exe -m pip install -r requirements.txt
.\.venv\Scripts\python.exe .\draw.py
```

If the `py` launcher is unavailable, use `python` in its place. To launch
without installing RDKit, create the environment and run `draw.py` directly,
skipping the `pip install -r requirements.txt` command.

 Drawing and editing

The toolbar contains element and bond-order selectors, the Draw/Select/Move/
Erase tools, structure checks, cleanup, undo/redo, and SMILES import and Molfile
export. The ring, functional-group, and reaction-symbol controls are on the
second toolbar row.

- **Draw:** click empty canvas to place an isolated carbon; click an atom to
  extend it with a bond; drag from an atom to draw a bond. Dragging onto an
  existing atom closes the bond. Click an existing bond to cycle its order.
- **Select:** click an atom, bond, or annotation. Shift-click toggles atoms in
  the selection; drag on empty canvas to select atoms in a box.
- **Move:** drag a molecule fragment or reaction annotation.
- **Erase:** click an atom, bond, or annotation to remove it. Right-click
  deletes the object under the pointer.
- **Elements and bond orders:** choose from the toolbar, or move the pointer
  over an atom and press a supported element key (`c`, `n`, `o`, `s`, `p`, `f`,
  `h`, `l` for chlorine, `b` for bromine, or `i` for iodine). Keys `1`, `2`,
  and `3` set the selected bond order or the bond under the pointer.
- **Rings and groups:** choose a template, click its placement button, then
  click empty canvas to place it separately or an atom to attach it.
  Carbocyclic rings can also be fused to a bond; heteroring fusion is not
  supported.
- **Reaction schemes:** choose a reaction arrow or equilibrium arrow and drag
  on the canvas. Choose plus, equals, or text and click to place it. Double-click
  a text box to edit it.
- **Formal charge:** select one or more atoms, choose a charge, and apply it.
- **Undo/redo and editor clipboard:** `Ctrl+Z` undo, `Ctrl+Y` redo, `Ctrl+C`
  copy the selected drawing, `Ctrl+V` paste it, and `Ctrl+A` select all.
  `Delete` or `Backspace` removes the selection; `Esc` cancels a pending
  placement. This copy/paste is internal to the editor; **Copy info** copies
  chemistry details to the system clipboard.

 Chemistry features

With RDKit installed:

- **Check structure** reports sanitization/valence issues without changing the
  drawing. The right panel shows the result and available structure properties.
- **Clean up** recalculates the 2D layout. This is an explicit action and can
  be undone.
- **Import SMILES** parses a SMILES string and adds the resulting structure to
  the canvas.
- **Export .mol** writes a Molfile for the valid molecular drawing. Reaction
  arrows, labels, and other canvas annotations are not included in the Molfile.
- **Copy info** copies available molecular information to the system clipboard;
  **Paste info** places an information annotation on the canvas.

Without RDKit, the app uses basic valence heuristics where possible. Treat those
results as limited: they are not a substitute for full chemical validation.

 Saving work

The editor has no native project-file save/load feature. Export a valid
molecular drawing as `.mol` if you need to preserve its chemical structure;
this does not preserve the complete reaction scheme or canvas layout. Copy
important reaction annotations separately before closing the app.

 Project files

- `draw.py` - application and editor implementation.
- `requirements.txt` - RDKit dependency for chemistry functionality.
