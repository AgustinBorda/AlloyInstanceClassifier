open util/ordering[Position]

sig Position {}
sig Product {}
sig Component extends Product {
    parts: set Product,
    position: one Position
}
sig Resource extends Product {}
sig Robot {
    position: one Position
}

pred Inv1 { 
    all c: Component | some c.parts
}

pred Inv2 { 
    all c: Component | c not in c.^parts
}

pred Inv3 { 
    all c: Component | c.position in Robot.position
}

pred Inv4 { 
    all c: Component | all p: c.parts | p in Resource or (p in Component and c.position in p.position.*prev)
}

pred Inv1_OK {
    all c: Component | some c.parts
}

assert Inv1_Repaired {
    Inv1[] iff Inv1_OK[]
}

pred Inv2_OK {
    all c: Component | c not in c.^parts
}

assert Inv2_Repaired {
    Inv2[] iff Inv2_OK[]
}

pred Inv3_OK {
    all c: Component | c.position in Robot.position
}

assert Inv3_Repaired {
    Inv3[] iff Inv3_OK[]
}

pred Inv4_OK {
    all c: Component | all p: c.parts | p in Resource or (p in Component and c.position in p.position.*prev)
}

assert Inv4_Repaired {
    Inv4[] iff Inv4_OK[]
}


pred repair_pred_1 { Inv4[] iff Inv4_OK[] }

assert repair_assert_1 { Inv4[] iff Inv4_OK[] }
