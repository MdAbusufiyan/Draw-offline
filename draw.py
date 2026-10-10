import tkinter as tk
from tkinter import ttk, messagebox
import math

class Atom:
    def __init__(self, x, y, element='C'):
        self.x = x
        self.y = y
        self.element = element
        self.bonds = []
        self.canvas_id = None
        self.text_id = None
    
    def distance_to(self, x, y):
        return math.sqrt((self.x - x)**2 + (self.y - y)**2)

class Bond:
    def __init__(self, atom1, atom2, order=1):
        self.atom1 = atom1
        self.atom2 = atom2
        self.order = order
        self.canvas_ids = []
        
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
        
        # State
        self.selected_element = tk.StringVar(value='C')
        self.bond_order = tk.IntVar(value=1)
        self.tool = tk.StringVar(value='draw')  # draw, erase, move
        self.drag_start_atom = None
        self.temp_line = None
        
        # Constants
        self.ATOM_RADIUS = 15
        self.SNAP_ANGLES = [0, 30, 60, 90, 120, 150, 180, 210, 240, 270, 300, 330]
        self.DEFAULT_BOND_LENGTH = 40
        
        self.setup_ui()
        self.bind_events()
    
    def setup_ui(self):
        # Toolbar
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
        
        # Clear button
        tk.Button(toolbar, text="Clear All", command=self.clear_all).pack(side=tk.LEFT, padx=10)
        
        # Canvas
        self.canvas = tk.Canvas(self.root, width=900, height=700, bg='white', cursor='crosshair')
        self.canvas.pack(expand=True, fill=tk.BOTH)
    
    def bind_events(self):
        self.canvas.bind('<Button-1>', self.on_click)
        self.canvas.bind('<B1-Motion>', self.on_drag)
        self.canvas.bind('<ButtonRelease-1>', self.on_release)
        self.canvas.bind('<Button-3>', self.on_right_click)  # Right-click to delete
    
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
                new_atom = Atom(event.x, event.y, self.selected_element.get())
                self.atoms.append(new_atom)
                self.draw_atom(new_atom)
        
        elif self.tool.get() == 'erase':
            self.delete_at(event.x, event.y)
        
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
            
            elif not target_atom:
                # Create new atom at snapped position
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
        # Only show label if not carbon or if carbon with no bonds or explicit
        show_label = atom.element != 'C' or len(atom.bonds) == 0
        
        if show_label:
            atom.text_id = self.canvas.create_text(
                atom.x, atom.y, text=atom.element,
                font=('Arial', 12, 'bold'), fill='black'
            )
        else:
            # Draw small dot for carbon
            r = 2
            atom.canvas_id = self.canvas.create_oval(
                atom.x - r, atom.y - r, atom.x + r, atom.y + r,
                fill='black', outline='black'
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
            self.canvas.delete('all')
            self.atoms = []
            self.bonds = []

def main():
    root = tk.Tk()
    app = MoleculeEditor(root)
    root.mainloop()

if __name__ == '__main__':
    main()