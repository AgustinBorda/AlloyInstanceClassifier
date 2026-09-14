open util/ordering[Position]

sig Position {}
sig Product {}
sig Component extends Product {
  parts : set Product,
  position : one Position
}
sig Resource extends Product {}
sig Robot {
  position : one Position
}

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
  all c:Component | all p: c.parts | p.position in c.position.*prev
}

pred Inv1_OK {
  all c:Component | some c.parts
}
assert Inv1_Repaired {
  Inv1[] iff Inv1_OK[]
}

pred Inv2_OK {
  all c:Component | c not in c.^parts
}
assert Inv2_Repaired {
  Inv2[] iff Inv2_OK[]
}

pred Inv3_OK {
  all c:Component | c.position in Robot.position
}
assert Inv3_Repaired {
  Inv3[] iff Inv3_OK[]
}

pred Inv4_OK {
  all c:Component | all p: c.parts | p.position in c.position.*prev
}
assert Inv4_Repaired {
  Inv4[] iff Inv4_OK[]
}


pred repair_pred_1 {
  Inv2[] iff Inv2_OK[]
}

assert repair_assert_1 {
  Inv2[] iff Inv2_OK[]
}
