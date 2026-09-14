/* 
    Consider the following model of an online CV platform that allows a
    profile to be updated not only by its owner but also by external institutions,
    to certify that the user indeed has produced certain works. 
    Works must have some unique global identifiers, that are used to
    clarify if two works are in fact the same.
*/

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

// Specify the following invariants!
// You can check their correctness with the different commands and
// specifying a given invariant you can assume the others to be true.

// For every user, the set of works they have marked as visible must be a subset of the works in their profile.
pred Inv1 {
 all w : Work | w in User.visible => w in User.profile 
}

// For any user, every work in their profile must have as its source either that same user or an institution.
pred Inv2 {
    all u : User | u.profile.source in Institution+u
}

// For any user, any two distinct works in that user's profile that come from the same source (the user or the same institution) cannot share any identifier.
pred Inv3 {
    all u : User, disj x,y : u.profile | x.source = y.source implies no (x.ids & y.ids)
}

// For any user, no two distinct works in their visible set may be linked, directly or indirectly, through shared identifiers (i.e., there must be no chain of identifier sharing that connects them).
pred Inv4 {
    all u : User, disj x,y : u.visible | x not in y.^(ids.~ids)
}
