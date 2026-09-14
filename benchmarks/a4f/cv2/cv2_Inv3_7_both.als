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

// For every user, the set of works that are marked as visible on their CV must be entirely contained within the works that belong to that user’s profile.
pred Inv1 {
    all u : User | u.visible in u.profile
}

// For any user, every work that appears in their profile must have been contributed by a source that is either that same user or an institution.
pred Inv2 {
    all u : User | u.profile.source in Institution+u
}

// For a given user, any two distinct works in their profile that originate from the very same source (the user themself or a specific institution) are not allowed to share any identifier.
pred Inv3 {
 all s : Source | profile.(source.s<:ids.~(source.s<:ids)).~profile in iden 
}

// For any user, it is forbidden to have two distinct visible works such that one can be reached from the other by a chain of identifier sharing, provided that every work involved in that chain (including the two visible works themselves) belongs to that user’s profile.
pred Inv4 {
	all u : User, disj x,y : u.visible | x not in y.^((u.profile <: ids).~(u.profile <: ids))
}
