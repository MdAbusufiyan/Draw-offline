import tkinter as tk
from tkinter import ttk, messagebox
import math
import copy
from collections import defaultdict, deque

# Atomic weights for molecular formula calculation
ATOMIC_WEIGHTS = {
    'H': 1.008, 'C': 12.011, 'N': 14.007, 'O': 15.999,
    'F': 18.998, 'P': 30.974, 'S': 32.065, 'Cl': 35.453,
    'Br': 79.904, 'I': 126.904
}

# Valence electrons for implicit hydrogen calculation
VALENCES = {
    'C': 4, 'N': 3, 'O': 2, 'S': 2, 'P': 3,
    'F': 1, 'Cl': 1, 'Br': 1, 'I': 1, 'H': 1
}

# Common valence states for validation
COMMON_VALENCES = {
    'C': [4],
    'N': [3, 5],  # NH3 or NO3-
    'O': [2],
    'S': [2, 4, 6],  # H2S, SO2, SO3
    'P': [3, 5],
    'F': [1],
    'Cl': [1, 3, 5, 7],
    'Br': [1, 3, 5, 7],
    'I': [1, 3, 5, 7],
    'H': [1]
}

# Electronegativity for bond polarity
ELECTRONEGATIVITY = {
    'H': 2.20, 'C': 2.55, 'N': 3.04, 'O': 3.44,
    'F': 3.98, 'P': 2.19, 'S': 2.58, 'Cl': 3.16,
    'Br': 2.96, 'I': 2.66
}

class Atom:
    def __init__(self, x, y, element='C'):
        self.x = x
        self.y = y
        self.element = element
        self.bonds = []
        self.canvas_id = None
        self.text_id = None
        self.charge = 0  # For charge indicators
        self.implicit_h = 0  # Number of implicit hydrogens
        self.is_valid = True  # Valence validation flag
        self.smiles_index = -1  # For SMILES generation
    
    def distance_to(self, x, y):
        return math.sqrt((self.x - x)**2 + (self.y - y)**2)
    
    def get_bond_order_sum(self):
        """Calculate total bond order for this atom"""
        return sum(bond.order for bond in self.bonds)
    
    def calculate_implicit_h(self):
        """Calculate number of implicit hydrogens"""
        if self.element not in VALENCES:
            self.implicit_h = 0
            return
        
        valence = VALENCES[self.element]
        bond_sum = self.get_bond_order_sum()
        self.implicit_h = max(0, valence - bond_sum - abs(self.charge))
    
    def validate_valence(self):
        """Check if atom has valid valence"""
        if self.element not in COMMON_VALENCES:
            self.is_valid = True
            return True
        
        total_bonds = self.get_bond_order_sum() + self.implicit_h
        
        # Check against common valence states
        self.is_valid = total_bonds in COMMON_VALENCES[self.element]
        return self.is_valid
    
    def get_total_valence(self):
        """Get total valence (bonds + implicit H)"""
        return self.get_bond_order_sum() + self.implicit_h

class Bond:
    def __init__(self, atom1, atom2, order=1):
        self.atom1 = atom1
        self.atom2 = atom2
        self.order = order
        self.canvas_ids = []
        self.is_aromatic = False  # For aromatic bond detection
        
        # Add bond reference to both atoms
        atom1.bonds.append(self)
        atom2.bonds.append(self)

class MoleculeEditor:
    def __init__(self, root):
        self.root = root
        self.root.title("ChemDraw Clone")
        
        # Data structures
        self.atoms = []
        self.bonds = []
        
        # Undo/Redo
        self.undo_stack = []
        self.redo_stack = []
        self.max_undo = 50
        
        # State
        self.selected_element = tk.StringVar(value='C')
        self.bond_order = tk.IntVar(value=1)
        self.tool = tk.StringVar(value='draw')  # draw, erase, move
        self.drag_start_atom = None
        self.temp_line = None
        self.selected_atoms = []
        self.clipboard = None
        
        # Constants
        self.ATOM_RADIUS = 15
        self.SNAP_ANGLES = [0, 30, 60, 90, 120, 150, 180, 210, 240, 270, 300, 330]
        self.DEFAULT_BOND_LENGTH = 40
        
        self.setup_ui()
        self.bind_events()
    
    def setup_ui(self):
        # Top toolbar
        toolbar = tk.Frame(self.root, relief=tk.RAISED, borderwidth=2)
        toolbar.pack(side=tk.TOP, fill=tk.X)
        
        # Element selector
        tk.Label(toolbar, text="Element:").pack(side=tk.LEFT, padx=5)
        elements = ['C', 'N', 'O', 'S', 'P', 'F', 'Cl', 'Br', 'I', 'H']
        element_menu = ttk.Combobox(toolbar, textvariable=self.selected_element, 
                                     values=elements, width=5, state='readonly')
        element_menu.pack(side=tk.LEFT, padx=5)
        
        # Bond order
        tk.Label(toolbar, text="Bond:").pack(side=tk.LEFT, padx=5)
        for i, label in [(1, 'Single'), (2, 'Double'), (3, 'Triple')]:
            tk.Radiobutton(toolbar, text=label, variable=self.bond_order, 
                          value=i).pack(side=tk.LEFT)
        
        # Tools
        tk.Label(toolbar, text="Tool:").pack(side=tk.LEFT, padx=5)
        for tool, label in [('draw', 'Draw'), ('erase', 'Erase'), ('move', 'Move')]:
            tk.Radiobutton(toolbar, text=label, variable=self.tool, 
                          value=tool).pack(side=tk.LEFT)
        
        # Undo/Redo buttons
        tk.Button(toolbar, text="Undo (Ctrl+Z)", command=self.undo).pack(side=tk.LEFT, padx=5)
        tk.Button(toolbar, text="Redo (Ctrl+Y)", command=self.redo).pack(side=tk.LEFT, padx=5)
        
        # Clear button
        tk.Button(toolbar, text="Clear All", command=self.clear_all).pack(side=tk.LEFT, padx=10)
        
        # Templates toolbar
        template_bar = tk.Frame(self.root, relief=tk.RAISED, borderwidth=2)
        template_bar.pack(side=tk.TOP, fill=tk.X)
        
        tk.Label(template_bar, text="Templates:").pack(side=tk.LEFT, padx=5)
        tk.Button(template_bar, text="Benzene", command=self.add_benzene).pack(side=tk.LEFT, padx=2)
        tk.Button(template_bar, text="Cyclohexane", command=self.add_cyclohexane).pack(side=tk.LEFT, padx=2)
        tk.Button(template_bar, text="Cyclopentane", command=self.add_cyclopentane).pack(side=tk.LEFT, padx=2)
        
        tk.Label(template_bar, text="Groups:").pack(side=tk.LEFT, padx=5)
        tk.Button(template_bar, text="CH₃", command=lambda: self.add_functional_group('CH3')).pack(side=tk.LEFT, padx=2)
        tk.Button(template_bar, text="OH", command=lambda: self.add_functional_group('OH')).pack(side=tk.LEFT, padx=2)
        tk.Button(template_bar, text="NH₂", command=lambda: self.add_functional_group('NH2')).pack(side=tk.LEFT, padx=2)
        tk.Button(template_bar, text="COOH", command=lambda: self.add_functional_group('COOH')).pack(side=tk.LEFT, padx=2)
        
        # Main container
        main_container = tk.Frame(self.root)
        main_container.pack(expand=True, fill=tk.BOTH)
        
        # Canvas
        self.canvas = tk.Canvas(main_container, width=900, height=700, bg='white', cursor='crosshair')
        self.canvas.pack(side=tk.LEFT, expand=True, fill=tk.BOTH)
        
        # Info panel
        info_panel = tk.Frame(main_container, width=200, relief=tk.SUNKEN, borderwidth=2)
        info_panel.pack(side=tk.RIGHT, fill=tk.Y)
        info_panel.pack_propagate(False)
        
        tk.Label(info_panel, text="Molecule Info", font=('Arial', 12, 'bold')).pack(pady=10)
        
        self.formula_label = tk.Label(info_panel, text="Formula: -", font=('Arial', 10))
        self.formula_label.pack(pady=5)
        
        self.weight_label = tk.Label(info_panel, text="MW: -", font=('Arial', 10))
        self.weight_label.pack(pady=5)
        
        self.smiles_label = tk.Label(info_panel, text="SMILES: -", font=('Arial', 9), 
                                     wraplength=180, justify=tk.LEFT)
        self.smiles_label.pack(pady=5)
        
        self.validation_label = tk.Label(info_panel, text="✓ Valid", 
                                         font=('Arial', 10, 'bold'), fg='green')
        self.validation_label.pack(pady=5)
        
        self.atom_count_label = tk.Label(info_panel, text="Atoms: 0", font=('Arial', 10))
        self.atom_count_label.pack(pady=5)
        
        self.bond_count_label = tk.Label(info_panel, text="Bonds: 0", font=('Arial', 10))
        self.bond_count_label.pack(pady=5)
        
        tk.Label(info_panel, text="\nKeyboard Shortcuts", font=('Arial', 10, 'bold')).pack(pady=10)
        
        shortcuts_text = """
Ctrl+Z: Undo
Ctrl+Y: Redo
Ctrl+C: Copy
Ctrl+V: Paste
Delete: Delete selected
1,2,3: Bond order
C,N,O,H: Elements
        """
        tk.Label(info_panel, text=shortcuts_text, font=('Arial', 8), justify=tk.LEFT).pack(pady=5)
    
    def bind_events(self):
        self.canvas.bind('<Button-1>', self.on_click)
        self.canvas.bind('<B1-Motion>', self.on_drag)
        self.canvas.bind('<ButtonRelease-1>', self.on_release)
        self.canvas.bind('<Button-3>', self.on_right_click)  # Right-click to delete
        
        # Keyboard shortcuts
        self.root.bind('<Control-z>', lambda e: self.undo())
        self.root.bind('<Control-y>', lambda e: self.redo())
        self.root.bind('<Control-c>', lambda e: self.copy_selection())
        self.root.bind('<Control-v>', lambda e: self.paste_selection())
        self.root.bind('<Delete>', lambda e: self.delete_selected())
        
        # Quick element selection
        self.root.bind('c', lambda e: self.selected_element.set('C'))
        self.root.bind('n', lambda e: self.selected_element.set('N'))
        self.root.bind('o', lambda e: self.selected_element.set('O'))
        self.root.bind('h', lambda e: self.selected_element.set('H'))
        self.root.bind('s', lambda e: self.selected_element.set('S'))
        self.root.bind('p', lambda e: self.selected_element.set('P'))
        
        # Quick bond order
        self.root.bind('1', lambda e: self.bond_order.set(1))
        self.root.bind('2', lambda e: self.bond_order.set(2))
        self.root.bind('3', lambda e: self.bond_order.set(3))
    
    def save_state(self):
        """Save current state for undo"""
        # Deep copy of atoms and bonds
        state = {
            'atoms': [(a.x, a.y, a.element, a.charge) for a in self.atoms],
            'bonds': [(self.atoms.index(b.atom1), self.atoms.index(b.atom2), b.order) 
                     for b in self.bonds]
        }
        self.undo_stack.append(state)
        if len(self.undo_stack) > self.max_undo:
            self.undo_stack.pop(0)
        self.redo_stack.clear()
    
    def undo(self):
        """Undo last action"""
        if not self.undo_stack:
            return
        
        # Save current state to redo
        current = {
            'atoms': [(a.x, a.y, a.element, a.charge) for a in self.atoms],
            'bonds': [(self.atoms.index(b.atom1), self.atoms.index(b.atom2), b.order) 
                     for b in self.bonds]
        }
        self.redo_stack.append(current)
        
        # Restore previous state
        state = self.undo_stack.pop()
        self.restore_state(state)
    
    def redo(self):
        """Redo last undone action"""
        if not self.redo_stack:
            return
        
        # Save current state to undo
        current = {
            'atoms': [(a.x, a.y, a.element, a.charge) for a in self.atoms],
            'bonds': [(self.atoms.index(b.atom1), self.atoms.index(b.atom2), b.order) 
                     for b in self.bonds]
        }
        self.undo_stack.append(current)
        
        # Restore redo state
        state = self.redo_stack.pop()
        self.restore_state(state)
    
    def restore_state(self, state):
        """Restore molecule from saved state"""
        # Clear current
        self.canvas.delete('all')
        self.atoms.clear()
        self.bonds.clear()
        
        # Restore atoms
        for x, y, element, charge in state['atoms']:
            atom = Atom(x, y, element)
            atom.charge = charge
            self.atoms.append(atom)
        
        # Restore bonds
        for idx1, idx2, order in state['bonds']:
            bond = Bond(self.atoms[idx1], self.atoms[idx2], order)
            self.bonds.append(bond)
        
        # Redraw everything
        self.redraw_all()
        self.update_info_panel()
    
    def redraw_all(self):
        """Redraw all atoms and bonds"""
        self.canvas.delete('all')
        
        # Update implicit H for all atoms
        for atom in self.atoms:
            atom.calculate_implicit_h()
            atom.validate_valence()
        
        # Draw bonds first (so they appear behind atoms)
        for bond in self.bonds:
            self.draw_bond(bond)
        
        # Draw atoms
        for atom in self.atoms:
            self.draw_atom(atom)
    
    def find_atom_at(self, x, y):
        """Find atom near the given coordinates"""
        for atom in self.atoms:
            if atom.distance_to(x, y) < self.ATOM_RADIUS:
                return atom
        return None
    
    def snap_angle(self, x1, y1, x2, y2):
        """Snap the line to common angles"""
        dx = x2 - x1
        dy = y2 - y1
        angle = math.degrees(math.atan2(dy, dx))
        
        # Find nearest snap angle
        nearest = min(self.SNAP_ANGLES, key=lambda a: abs(angle - a) if abs(angle - a) < 180 else abs(abs(angle - a) - 360))
        
        # Calculate new endpoint
        distance = math.sqrt(dx**2 + dy**2)
        rad = math.radians(nearest)
        new_x = x1 + distance * math.cos(rad)
        new_y = y1 + distance * math.sin(rad)
        
        return new_x, new_y
    
    def on_click(self, event):
        if self.tool.get() == 'draw':
            atom = self.find_atom_at(event.x, event.y)
            
            if atom:
                # Start dragging from this atom to create a bond
                self.drag_start_atom = atom
            else:
                # Create new atom
                self.save_state()
                new_atom = Atom(event.x, event.y, self.selected_element.get())
                self.atoms.append(new_atom)
                self.draw_atom(new_atom)
                self.update_info_panel()
        
        elif self.tool.get() == 'erase':
            self.save_state()
            self.delete_at(event.x, event.y)
            self.update_info_panel()
        
        elif self.tool.get() == 'move':
            atom = self.find_atom_at(event.x, event.y)
            if atom:
                self.drag_start_atom = atom
    
    def on_drag(self, event):
        if self.tool.get() == 'draw' and self.drag_start_atom:
            # Show temporary line while dragging
            if self.temp_line:
                self.canvas.delete(self.temp_line)
            
            # Snap to angle
            new_x, new_y = self.snap_angle(self.drag_start_atom.x, self.drag_start_atom.y, 
                                          event.x, event.y)
            
            self.temp_line = self.canvas.create_line(
                self.drag_start_atom.x, self.drag_start_atom.y,
                new_x, new_y, fill='gray', dash=(4, 4)
            )
        
        elif self.tool.get() == 'move' and self.drag_start_atom:
            # Move the atom
            dx = event.x - self.drag_start_atom.x
            dy = event.y - self.drag_start_atom.y
            
            self.drag_start_atom.x = event.x
            self.drag_start_atom.y = event.y
            
            # Redraw everything connected to this atom
            self.redraw_atom(self.drag_start_atom)
            for bond in self.drag_start_atom.bonds:
                self.redraw_bond(bond)
    
    def on_release(self, event):
        if self.temp_line:
            self.canvas.delete(self.temp_line)
            self.temp_line = None
        
        if self.tool.get() == 'draw' and self.drag_start_atom:
            # Check if we released on another atom
            target_atom = self.find_atom_at(event.x, event.y)
            
            if target_atom and target_atom != self.drag_start_atom:
                # Create bond between atoms
                self.save_state()
                # Check if bond already exists
                existing = False
                for bond in self.drag_start_atom.bonds:
                    if bond.atom1 == target_atom or bond.atom2 == target_atom:
                        # Update bond order
                        bond.order = self.bond_order.get()
                        self.redraw_bond(bond)
                        existing = True
                        break
                
                if not existing:
                    bond = Bond(self.drag_start_atom, target_atom, self.bond_order.get())
                    self.bonds.append(bond)
                    self.draw_bond(bond)
                
                # Update implicit H
                self.drag_start_atom.calculate_implicit_h()
                target_atom.calculate_implicit_h()
                self.redraw_atom(self.drag_start_atom)
                self.redraw_atom(target_atom)
                self.update_info_panel()
            
            elif not target_atom:
                # Create new atom at snapped position
                self.save_state()
                new_x, new_y = self.snap_angle(self.drag_start_atom.x, self.drag_start_atom.y,
                                              event.x, event.y)
                
                # Set to default bond length
                dx = new_x - self.drag_start_atom.x
                dy = new_y - self.drag_start_atom.y
                distance = math.sqrt(dx**2 + dy**2)
                if distance > 0:
                    scale = self.DEFAULT_BOND_LENGTH / distance
                    new_x = self.drag_start_atom.x + dx * scale
                    new_y = self.drag_start_atom.y + dy * scale
                
                new_atom = Atom(new_x, new_y, self.selected_element.get())
                self.atoms.append(new_atom)
                self.draw_atom(new_atom)
                
                # Create bond
                bond = Bond(self.drag_start_atom, new_atom, self.bond_order.get())
                self.bonds.append(bond)
                self.draw_bond(bond)
                
                # Update implicit H
                self.drag_start_atom.calculate_implicit_h()
                new_atom.calculate_implicit_h()
                self.redraw_atom(self.drag_start_atom)
                self.redraw_atom(new_atom)
                self.update_info_panel()
        
        elif self.tool.get() == 'move' and self.drag_start_atom:
            # Save state after move is complete
            self.save_state()
        
        self.drag_start_atom = None
    
    def on_right_click(self, event):
        """Right-click to delete"""
        self.delete_at(event.x, event.y)
    
    def delete_at(self, x, y):
        """Delete atom or bond at position"""
        # Try to find atom
        atom = self.find_atom_at(x, y)
        if atom:
            self.delete_atom(atom)
            return
        
        # Try to find bond
        for bond in self.bonds:
            if self.point_near_line(x, y, bond.atom1.x, bond.atom1.y, 
                                   bond.atom2.x, bond.atom2.y, threshold=5):
                self.delete_bond(bond)
                return
    
    def point_near_line(self, px, py, x1, y1, x2, y2, threshold=5):
        """Check if point is near a line segment"""
        dx = x2 - x1
        dy = y2 - y1
        length_sq = dx*dx + dy*dy
        
        if length_sq == 0:
            return math.sqrt((px-x1)**2 + (py-y1)**2) < threshold
        
        t = max(0, min(1, ((px-x1)*dx + (py-y1)*dy) / length_sq))
        proj_x = x1 + t * dx
        proj_y = y1 + t * dy
        
        dist = math.sqrt((px-proj_x)**2 + (py-proj_y)**2)
        return dist < threshold
    
    def delete_atom(self, atom):
        """Delete an atom and all its bonds"""
        # Delete all bonds connected to this atom
        bonds_to_delete = atom.bonds.copy()
        for bond in bonds_to_delete:
            self.delete_bond(bond)
        
        # Remove from canvas
        if atom.canvas_id:
            self.canvas.delete(atom.canvas_id)
        if atom.text_id:
            self.canvas.delete(atom.text_id)
        
        # Remove from list
        self.atoms.remove(atom)
    
    def delete_bond(self, bond):
        """Delete a bond"""
        # Remove from atoms
        if bond in bond.atom1.bonds:
            bond.atom1.bonds.remove(bond)
        if bond in bond.atom2.bonds:
            bond.atom2.bonds.remove(bond)
        
        # Remove from canvas
        for cid in bond.canvas_ids:
            self.canvas.delete(cid)
        
        # Remove from list
        if bond in self.bonds:
            self.bonds.remove(bond)
    
    def draw_atom(self, atom):
        """Draw an atom on the canvas"""
        # Update implicit H count and validation
        atom.calculate_implicit_h()
        atom.validate_valence()
        
        # Color based on validation
        text_color = 'black' if atom.is_valid else 'red'
        
        # Only show label if not carbon or if carbon with no bonds or has charge
        show_label = atom.element != 'C' or len(atom.bonds) == 0 or atom.charge != 0
        
        if show_label:
            # Build label text with implicit H and charge
            label = atom.element
            
            if atom.implicit_h > 0:
                label += 'H'
                if atom.implicit_h > 1:
                    label += str(atom.implicit_h)
            
            if atom.charge != 0:
                charge_str = '+' if atom.charge > 0 else ''
                charge_str += str(atom.charge) if abs(atom.charge) > 1 else ('+' if atom.charge > 0 else '-')
                label += charge_str
            
            atom.text_id = self.canvas.create_text(
                atom.x, atom.y, text=label,
                font=('Arial', 12, 'bold'), fill=text_color
            )
        else:
            # Draw small dot for carbon (red if invalid)
            r = 2
            color = 'black' if atom.is_valid else 'red'
            atom.canvas_id = self.canvas.create_oval(
                atom.x - r, atom.y - r, atom.x + r, atom.y + r,
                fill=color, outline=color
            )
    
    def redraw_atom(self, atom):
        """Redraw an atom"""
        if atom.canvas_id:
            self.canvas.delete(atom.canvas_id)
            atom.canvas_id = None
        if atom.text_id:
            self.canvas.delete(atom.text_id)
            atom.text_id = None
        self.draw_atom(atom)
    
    def draw_bond(self, bond):
        """Draw a bond on the canvas"""
        x1, y1 = bond.atom1.x, bond.atom1.y
        x2, y2 = bond.atom2.x, bond.atom2.y
        
        # Clear old drawings
        for cid in bond.canvas_ids:
            self.canvas.delete(cid)
        bond.canvas_ids = []
        
        if bond.order == 1:
            # Single bond
            line_id = self.canvas.create_line(x1, y1, x2, y2, fill='black', width=2)
            bond.canvas_ids.append(line_id)
        
        elif bond.order == 2:
            # Double bond - parallel lines
            dx = x2 - x1
            dy = y2 - y1
            length = math.sqrt(dx**2 + dy**2)
            
            if length > 0:
                # Perpendicular offset
                offset = 3
                px = -dy / length * offset
                py = dx / length * offset
                
                line1 = self.canvas.create_line(x1+px, y1+py, x2+px, y2+py, fill='black', width=2)
                line2 = self.canvas.create_line(x1-px, y1-py, x2-px, y2-py, fill='black', width=2)
                bond.canvas_ids.extend([line1, line2])
        
        elif bond.order == 3:
            # Triple bond
            dx = x2 - x1
            dy = y2 - y1
            length = math.sqrt(dx**2 + dy**2)
            
            if length > 0:
                offset = 4
                px = -dy / length * offset
                py = dx / length * offset
                
                line1 = self.canvas.create_line(x1, y1, x2, y2, fill='black', width=2)
                line2 = self.canvas.create_line(x1+px, y1+py, x2+px, y2+py, fill='black', width=2)
                line3 = self.canvas.create_line(x1-px, y1-py, x2-px, y2-py, fill='black', width=2)
                bond.canvas_ids.extend([line1, line2, line3])
    
    def redraw_bond(self, bond):
        """Redraw a bond"""
        self.draw_bond(bond)
    
    def clear_all(self):
        """Clear all atoms and bonds"""
        if messagebox.askyesno("Clear All", "Are you sure you want to clear everything?"):
            self.save_state()
            self.canvas.delete('all')
            self.atoms = []
            self.bonds = []
            self.update_info_panel()
    
    # ===== TEMPLATE METHODS =====
    
    def add_benzene(self):
        """Add benzene ring template"""
        self.save_state()
        center_x, center_y = 400, 300
        radius = 40
        atoms = []
        
        # Create 6 carbon atoms in a hexagon
        for i in range(6):
            angle = math.radians(90 + i * 60)  # Start at top
            x = center_x + radius * math.cos(angle)
            y = center_y + radius * math.sin(angle)
            atom = Atom(x, y, 'C')
            atoms.append(atom)
            self.atoms.append(atom)
        
        # Create alternating single and double bonds
        for i in range(6):
            next_i = (i + 1) % 6
            bond_order = 2 if i % 2 == 0 else 1
            bond = Bond(atoms[i], atoms[next_i], bond_order)
            self.bonds.append(bond)
        
        self.redraw_all()
        self.update_info_panel()
    
    def add_cyclohexane(self):
        """Add cyclohexane ring template"""
        self.save_state()
        center_x, center_y = 400, 300
        radius = 40
        atoms = []
        
        # Create 6 carbon atoms in a hexagon
        for i in range(6):
            angle = math.radians(90 + i * 60)
            x = center_x + radius * math.cos(angle)
            y = center_y + radius * math.sin(angle)
            atom = Atom(x, y, 'C')
            atoms.append(atom)
            self.atoms.append(atom)
        
        # Create single bonds
        for i in range(6):
            next_i = (i + 1) % 6
            bond = Bond(atoms[i], atoms[next_i], 1)
            self.bonds.append(bond)
        
        self.redraw_all()
        self.update_info_panel()
    
    def add_cyclopentane(self):
        """Add cyclopentane ring template"""
        self.save_state()
        center_x, center_y = 400, 300
        radius = 40
        atoms = []
        
        # Create 5 carbon atoms in a pentagon
        for i in range(5):
            angle = math.radians(90 + i * 72)
            x = center_x + radius * math.cos(angle)
            y = center_y + radius * math.sin(angle)
            atom = Atom(x, y, 'C')
            atoms.append(atom)
            self.atoms.append(atom)
        
        # Create single bonds
        for i in range(5):
            next_i = (i + 1) % 5
            bond = Bond(atoms[i], atoms[next_i], 1)
            self.bonds.append(bond)
        
        self.redraw_all()
        self.update_info_panel()
    
    def add_functional_group(self, group_type):
        """Add functional group at mouse position or center"""
        self.save_state()
        x, y = 400, 300  # Default center position
        
        if group_type == 'CH3':
            c = Atom(x, y, 'C')
            self.atoms.append(c)
        
        elif group_type == 'OH':
            o = Atom(x, y, 'O')
            h = Atom(x + 30, y, 'H')
            self.atoms.extend([o, h])
            bond = Bond(o, h, 1)
            self.bonds.append(bond)
        
        elif group_type == 'NH2':
            n = Atom(x, y, 'N')
            self.atoms.append(n)
        
        elif group_type == 'COOH':
            c = Atom(x, y, 'C')
            o1 = Atom(x + 30, y - 20, 'O')
            o2 = Atom(x + 30, y + 20, 'O')
            h = Atom(x + 60, y + 20, 'H')
            
            self.atoms.extend([c, o1, o2, h])
            self.bonds.extend([
                Bond(c, o1, 2),
                Bond(c, o2, 1),
                Bond(o2, h, 1)
            ])
        
        self.redraw_all()
        self.update_info_panel()
    
    # ===== CHEMISTRY CALCULATION METHODS =====
    
    def calculate_molecular_formula(self):
        """Calculate molecular formula including implicit hydrogens"""
        element_counts = defaultdict(int)
        
        for atom in self.atoms:
            element_counts[atom.element] += 1
            # Add implicit hydrogens
            if atom.implicit_h > 0:
                element_counts['H'] += atom.implicit_h
        
        if not element_counts:
            return "-"
        
        # Format formula (C, H first, then alphabetical)
        formula = ""
        for elem in ['C', 'H']:
            if elem in element_counts:
                count = element_counts[elem]
                formula += elem
                if count > 1:
                    formula += str(count)
                del element_counts[elem]
        
        # Add remaining elements alphabetically
        for elem in sorted(element_counts.keys()):
            count = element_counts[elem]
            formula += elem
            if count > 1:
                formula += str(count)
        
        return formula
    
    def calculate_molecular_weight(self):
        """Calculate molecular weight"""
        weight = 0.0
        
        for atom in self.atoms:
            if atom.element in ATOMIC_WEIGHTS:
                weight += ATOMIC_WEIGHTS[atom.element]
                # Add implicit hydrogens
                weight += atom.implicit_h * ATOMIC_WEIGHTS['H']
        
        return round(weight, 2) if weight > 0 else 0
    
    def update_info_panel(self):
        """Update the info panel with current molecule stats"""
        formula = self.calculate_molecular_formula()
        weight = self.calculate_molecular_weight()
        smiles = self.generate_smiles()
        is_valid, issues = self.validate_structure()
        
        self.formula_label.config(text=f"Formula: {formula}")
        self.weight_label.config(text=f"MW: {weight} g/mol")
        self.smiles_label.config(text=f"SMILES: {smiles}")
        
        if is_valid:
            self.validation_label.config(text="✓ Valid Structure", fg='green')
        else:
            self.validation_label.config(text=f"✗ Invalid: {issues}", fg='red')
        
        self.atom_count_label.config(text=f"Atoms: {len(self.atoms)}")
        self.bond_count_label.config(text=f"Bonds: {len(self.bonds)}")
    
    # ===== ADVANCED CHEMISTRY METHODS =====
    
    def validate_structure(self):
        """Comprehensive structure validation"""
        if not self.atoms:
            return True, ""
        
        issues = []
        
        # Check each atom's valence
        invalid_atoms = []
        for atom in self.atoms:
            if not atom.is_valid:
                invalid_atoms.append(atom.element)
        
        if invalid_atoms:
            issues.append(f"Invalid valence on {len(invalid_atoms)} atom(s)")
        
        # Check for disconnected fragments
        if len(self.atoms) > 1:
            visited = set()
            self._dfs_visit(self.atoms[0], visited)
            if len(visited) < len(self.atoms):
                issues.append("Disconnected fragments")
        
        # Check for odd number of electrons (radicals)
        total_electrons = 0
        for atom in self.atoms:
            if atom.element in VALENCES:
                total_electrons += VALENCES[atom.element]
                total_electrons += atom.implicit_h  # Each H adds 1 electron
        
        # Subtract bonding electrons
        for bond in self.bonds:
            total_electrons -= bond.order * 2
        
        # Check common chemistry rules
        if self.has_invalid_bonds():
            issues.append("Unusual bond detected")
        
        return len(issues) == 0, "; ".join(issues) if issues else ""
    
    def _dfs_visit(self, atom, visited):
        """Depth-first search to check connectivity"""
        visited.add(atom)
        for bond in atom.bonds:
            neighbor = bond.atom2 if bond.atom1 == atom else bond.atom1
            if neighbor not in visited:
                self._dfs_visit(neighbor, visited)
    
    def has_invalid_bonds(self):
        """Check for chemically unusual bonds"""
        for bond in self.bonds:
            elem1 = bond.atom1.element
            elem2 = bond.atom2.element
            
            # H can't have double/triple bonds
            if 'H' in [elem1, elem2] and bond.order > 1:
                return True
            
            # Halogens rarely form multiple bonds
            halogens = {'F', 'Cl', 'Br', 'I'}
            if elem1 in halogens and elem2 in halogens and bond.order > 1:
                return True
        
        return False
    
    def generate_smiles(self):
        """Generate SMILES string for the molecule"""
        if not self.atoms:
            return "-"
        
        try:
            # Reset SMILES indices
            for atom in self.atoms:
                atom.smiles_index = -1
            
            # Handle disconnected fragments
            fragments = self.get_connected_components()
            if len(fragments) > 1:
                smiles_parts = []
                for fragment in fragments:
                    smiles_parts.append(self._generate_smiles_fragment(fragment))
                return ".".join(smiles_parts)
            else:
                return self._generate_smiles_fragment(self.atoms)
        
        except Exception as e:
            return f"Error: {str(e)[:20]}"
    
    def get_connected_components(self):
        """Get all disconnected fragments"""
        visited = set()
        components = []
        
        for atom in self.atoms:
            if atom not in visited:
                component = []
                self._collect_component(atom, visited, component)
                components.append(component)
        
        return components
    
    def _collect_component(self, atom, visited, component):
        """Collect all atoms in a connected component"""
        visited.add(atom)
        component.append(atom)
        
        for bond in atom.bonds:
            neighbor = bond.atom2 if bond.atom1 == atom else bond.atom1
            if neighbor not in visited:
                self._collect_component(neighbor, visited, component)
    
    def _generate_smiles_fragment(self, atoms):
        """Generate SMILES for a connected fragment"""
        if not atoms:
            return ""
        
        # Start from a terminal atom or first atom
        start_atom = self._find_smiles_start(atoms)
        
        # Build SMILES using DFS
        visited = set()
        ring_closures = {}
        ring_counter = [1]  # Use list to allow modification in nested function
        
        smiles = self._smiles_dfs(start_atom, None, visited, ring_closures, ring_counter)
        return smiles
    
    def _find_smiles_start(self, atoms):
        """Find best starting atom for SMILES (prefer terminal atoms)"""
        # Prefer atoms with fewest bonds
        return min(atoms, key=lambda a: len(a.bonds))
    
    def _smiles_dfs(self, atom, from_bond, visited, ring_closures, ring_counter):
        """DFS traversal to build SMILES string"""
        if atom in visited:
            # Ring closure
            if atom not in ring_closures:
                ring_closures[atom] = ring_counter[0]
                ring_counter[0] += 1
            return str(ring_closures[atom])
        
        visited.add(atom)
        
        # Build atom symbol
        smiles = self._get_smiles_atom(atom)
        
        # Add ring closure if needed
        if atom in ring_closures:
            smiles += str(ring_closures[atom])
            del ring_closures[atom]
        
        # Sort bonds for canonical SMILES (put main chain first)
        bonds = sorted([b for b in atom.bonds if b != from_bond],
                      key=lambda b: len((b.atom2 if b.atom1 == atom else b.atom1).bonds))
        
        # Process bonds
        first_branch = True
        for bond in bonds:
            if bond == from_bond:
                continue
            
            neighbor = bond.atom2 if bond.atom1 == atom else bond.atom1
            
            # Add bond symbol
            bond_symbol = self._get_bond_symbol(bond)
            
            # Add branch notation
            if not first_branch and neighbor not in visited:
                smiles += "("
                smiles += bond_symbol
                smiles += self._smiles_dfs(neighbor, bond, visited, ring_closures, ring_counter)
                smiles += ")"
            else:
                smiles += bond_symbol
                smiles += self._smiles_dfs(neighbor, bond, visited, ring_closures, ring_counter)
                first_branch = False
        
        return smiles
    
    def _get_smiles_atom(self, atom):
        """Get SMILES representation of an atom"""
        # Organic subset atoms (C, N, O, S, P, F, Cl, Br, I) can be lowercase
        organic = {'C', 'N', 'O', 'S', 'P', 'F', 'Cl', 'Br', 'I'}
        
        if atom.element == 'C' and atom.charge == 0 and atom.implicit_h in [0, 1, 2, 3, 4]:
            return 'C'  # Simple carbon
        elif atom.element in ['Cl', 'Br']:
            return atom.element  # Two-letter halogens
        elif atom.element in organic and atom.charge == 0:
            # Lowercase for organic atoms
            return atom.element.lower() if len(atom.element) == 1 else atom.element
        else:
            # Bracketed atom [element]
            result = '['
            result += atom.element
            
            if atom.implicit_h > 0:
                result += 'H'
                if atom.implicit_h > 1:
                    result += str(atom.implicit_h)
            
            if atom.charge != 0:
                if atom.charge > 0:
                    result += '+' * atom.charge if atom.charge <= 3 else f'+{atom.charge}'
                else:
                    result += '-' * abs(atom.charge) if abs(atom.charge) <= 3 else f'{atom.charge}'
            
            result += ']'
            return result
    
    def _get_bond_symbol(self, bond):
        """Get SMILES bond symbol"""
        if bond.order == 1:
            return ''  # Single bonds are implicit
        elif bond.order == 2:
            return '='
        elif bond.order == 3:
            return '#'
        return ''
    
    def detect_aromaticity(self):
        """Detect aromatic rings (simplified Hückel's rule)"""
        # Find all rings
        rings = self.find_rings()
        
        for ring in rings:
            # Check if all atoms are sp2 hybridized and follow Hückel's rule
            if self._is_aromatic_ring(ring):
                # Mark bonds as aromatic
                for i in range(len(ring)):
                    atom1 = ring[i]
                    atom2 = ring[(i + 1) % len(ring)]
                    bond = self._find_bond(atom1, atom2)
                    if bond:
                        bond.is_aromatic = True
    
    def find_rings(self):
        """Find all rings in the molecule (simplified)"""
        rings = []
        visited = set()
        
        for atom in self.atoms:
            if atom not in visited:
                self._find_rings_dfs(atom, atom, [atom], visited, rings, set())
        
        return rings
    
    def _find_rings_dfs(self, start, current, path, visited, rings, path_set):
        """DFS to find rings"""
        path_set.add(current)
        
        for bond in current.bonds:
            neighbor = bond.atom2 if bond.atom1 == current else bond.atom1
            
            if neighbor == start and len(path) >= 3:
                # Found a ring
                rings.append(path[:])
            elif neighbor not in path_set and len(path) < 10:  # Limit ring size
                self._find_rings_dfs(start, neighbor, path + [neighbor], 
                                    visited, rings, path_set)
        
        path_set.remove(current)
    
    def _is_aromatic_ring(self, ring):
        """Check if ring is aromatic (very simplified)"""
        # For now, just check if it's a 6-membered ring of carbons
        if len(ring) != 6:
            return False
        
        # All carbons or N
        for atom in ring:
            if atom.element not in ['C', 'N']:
                return False
        
        return True
    
    def _find_bond(self, atom1, atom2):
        """Find bond between two atoms"""
        for bond in atom1.bonds:
            if (bond.atom1 == atom1 and bond.atom2 == atom2) or \
               (bond.atom1 == atom2 and bond.atom2 == atom1):
                return bond
        return None
    
    # ===== COPY/PASTE METHODS =====
    
    def copy_selection(self):
        """Copy selected atoms (for now, copy all)"""
        if not self.atoms:
            return
        
        self.clipboard = {
            'atoms': [(a.x, a.y, a.element, a.charge) for a in self.atoms],
            'bonds': [(self.atoms.index(b.atom1), self.atoms.index(b.atom2), b.order) 
                     for b in self.bonds]
        }
    
    def paste_selection(self):
        """Paste clipboard contents"""
        if not self.clipboard:
            return
        
        self.save_state()
        
        # Offset pasted structure
        offset_x, offset_y = 50, 50
        
        old_atom_count = len(self.atoms)
        
        # Create new atoms
        for x, y, element, charge in self.clipboard['atoms']:
            atom = Atom(x + offset_x, y + offset_y, element)
            atom.charge = charge
            self.atoms.append(atom)
        
        # Create new bonds
        for idx1, idx2, order in self.clipboard['bonds']:
            new_idx1 = old_atom_count + idx1
            new_idx2 = old_atom_count + idx2
            bond = Bond(self.atoms[new_idx1], self.atoms[new_idx2], order)
            self.bonds.append(bond)
        
        self.redraw_all()
        self.update_info_panel()
    
    def delete_selected(self):
        """Delete selected atoms (for now, does nothing - would need selection tool)"""
        pass

def main():
    root = tk.Tk()
    app = MoleculeEditor(root)
    root.mainloop()

if __name__ == '__main__':
    main()