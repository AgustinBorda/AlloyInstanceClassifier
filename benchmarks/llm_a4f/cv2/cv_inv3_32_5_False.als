abstract sig Source {}
sig User extends Source {
  profile : set Work,
  visible : set Work
}
sig Institution extends Source {}
sig Id {}
sig Work {
  ids : some Id,
  source : one Source
}
pred Inv1 { // The works publicly visible in a curriculum must be part of its profile
  all u:User | u.visible in u.profile
}
pred Inv2 { // A user profile can only have works added by himself or some external institution
  all u:User, w:Work | w in u.profile implies (u in w.source or some i:Institution | i in w.source)
}
pred Inv3 { // The works added to a profile by a given source cannot have common identifiers

  all w1,w2:Work | w1.ids = w2.ids implies w1 = w2
}
/*======== IFF PERFECT ORACLE ===============*/
pred Inv1_OK {
  all u:User | u.visible in u.profile
}
assert Inv1_Repaired {
  Inv1[] iff Inv1_OK[]
}
---------
pred Inv2_OK {
  all u:User, w:Work | w in u.profile implies (u in w.source or some i:Institution | i in w.source)
}
assert Inv2_Repaired {
  Inv2[] iff Inv2_OK[]
}
--------
pred Inv3_OK {
  all w1, w2 : Work, u : User | w1 != w2 and (w1 + w2) in u.profile and (w1.source = w2.source) implies no w1.ids & w2.ids
}
assert Inv3_Repaired {
  Inv3[] iff Inv3_OK[]
}
-- PerfectOracleCommands
pred repair_pred_1{Inv3[] iff Inv3_OK[] }
assert repair_assert_1{Inv3[] iff Inv3_OK[] }
// The profile of a user cannot have two visible versions of the same work
pred Inv4 {
	all u : User, disj x,y : u.visible | x not in y.^((u.profile <: ids).~(u.profile <: ids))
}