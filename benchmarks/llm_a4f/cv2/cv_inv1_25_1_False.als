abstract sig Source {} sig User extends Source { profile : set Work, visible : set Work } sig Institution extends Source {} sig Id {} sig Work { ids : some Id, source : one Source } pred Inv1 { all u : User, w : Work | u->w in profile and w in u.visible } pred Inv1_OK { all u:User | u.visible in u.profile } assert Inv1_Repaired { Inv1[] iff Inv1_OK[] } // The profile of a user cannot have two visible versions of the same work
pred Inv4 {
	all u : User, disj x,y : u.visible | x not in y.^((u.profile <: ids).~(u.profile <: ids))
}