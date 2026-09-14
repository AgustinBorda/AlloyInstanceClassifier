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
// You can 
// specifying a given invariant you can assume the others to be true.
pred Inv1 { // A component requires at least one part
all c:Component | some c.parts
}
pred Inv2 { // A component cannot be a part of itself
all c:Component | c not in c.^parts
}
pred Inv3 { // The position where a component is assembled must have at least one robot
all c:Component | c.position in Robot.position
}
pred Inv4 { // The parts required by a component cannot be assembled in a later position
all c:Component | all p: c.parts | p in Product implies p.position in c.position.*prev
}
/*======== IFF PERFECT ORACLE ===============*/
pred Inv1_OK {
all c:Component | some c.parts
}
assert Inv1_Repaired {
Inv1[] iff Inv1_OK[]
}
---------
pred Inv2_OK {
all c:Component | c not in c.^parts
}
assert Inv2_Repaired {
Inv2[] iff Inv2_OK[]
}
--------
pred Inv3_OK {
all c:Component | c.position in Robot.position
}
assert Inv3_Repaired {
Inv3[] iff Inv3_OK[]
}
--------
pred Inv4_OK {
all c:Component | all p: c.parts | p in Product implies p.position in c.position.*prev
}
assert Inv4_Repaired {
Inv4[] iff Inv4_OK[]
}
-- PerfectOracleCommands
pred repair_pred_1{Inv4[] iff Inv4_OK[] }
assert repair_assert_1{Inv4[] iff Inv4_OK[] }
