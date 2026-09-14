sig Track {
	succs : set Track,
	signals : set Signal
}
sig Junction, Entry, Exit in Track {}

sig Signal {}
sig Semaphore, Speed extends Signal {}

// Specify the following properties
// You can check their correctness with the different commands and
// when specifying each property you can assume all the previous ones to be true

	// There is at least one entry track and at least one exit track.
pred inv1 {
	(some Entry) and (some Exit)
}

	// Every signal is placed on exactly one track.
pred inv2 {
	all s : Signal | one signals.s
}

	// A track is an exit if and only if it has no successors.
pred inv3 {
	all t : Track | t in Exit iff no t.succs
}

	// A track is an entry if and only if no other track has it as a successor.
pred inv4 {
	all t : Track | t in Entry iff no succs.t
}


	// A track is a junction if and only if it has more than one predecessor (i.e., at least two tracks have it as a successor).
pred inv5 {
	all t : Track | t not in Junction iff lone succs.t
}

	// Every entry track has at least one speed signal.
pred inv6 {
	all t : Entry | some t.signals & Speed
}

	// The track layout contains no cycles; no track can reach itself by following successors.
pred inv7 {
	no t : Track | t in t.^succs
}

	// Every exit track is reachable from every entry track via zero or more successor steps.
pred inv8 {
	all e : Entry, x : Exit | x in e.*succs
}

	// If a track has no junction as an immediate successor, then that track has no semaphore signal.
pred inv9 {
	all t : Track | no t.succs & Junction implies no t.signals & Semaphore
}

	// For every junction, every track that directly precedes it (i.e., has the junction as a successor) must have at least one semaphore signal.
pred inv10 {
  	all x: Track | some y: x.signals | Junction in x.succs implies y in Semaphore 
}
