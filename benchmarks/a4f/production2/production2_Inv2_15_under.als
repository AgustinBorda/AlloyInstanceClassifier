open util/ordering[Position]

// Consider the following model of an automated production line
// The production line consists of several positions in sequence
sig Position {}

// Products are either components assembled in the production line or 
// other resources (e.g. pre-assembled products or base materials)
sig Product {}

// Components are assembled in a given position from other parts
sig Component extends Product {
    parts : set Product,
    position : one Position
}
sig Resource extends Product {}

// Robots work somewhere in the production line
sig Robot {
        position : one Position
}

// Specify the following invariants!
// You can check their correctness with the different commands and
// specifying a given invariant you can assume the others to be true.

// Every component has at least one part.
pred Inv1 {
    all c : Component | some c.parts
}

// No component is part of itself, either directly or indirectly (no cycles in the part-of relation).
pred Inv2 {
 all c:Component | c.parts in (univ-c) 
}

// For every component, the position where that component is assembled must have at least one robot assigned to it.
pred Inv3 {
    all c : Component | some position.(c.position) & Robot
}

// For any component, if one of its parts is also a component, that part must be assembled at a position that is not after the component's own position (the part's position is less than or equal to the component's position in the production sequence).
pred Inv4 {
    all c : Component, p : c.parts & Component | lte[p.position,c.position]
}
