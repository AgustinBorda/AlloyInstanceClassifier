// Model of a train station

sig Track {
	prox : set Track,
	signal : lone Signal
}
sig Junction extends Track {}
sig Entry, Exit in Track {}

sig Signal {}
var sig Green in Signal {}

sig Train {
	var pos : lone Track
}

fact Layout {
	// A track is a junction iff it has more than one successor or more than one predecessor
	all t : Track | t not in Junction iff (lone t.prox and lone prox.t)
	// No cycles
	no t : Track | t in t.^prox
	// Signals belong to one and only one track
	all s : Signal | one signal.s
	// All tracks before junctions have signals
	all j : Junction, t : prox.j | some t.signal
	// Entry tracks are those without predecessors and exit tracks are those without no successors
	all t : Track | t in Entry iff no prox.t
	all t : Track | t in Exit iff no t.prox
}

	// Intially all signals are red
pred prop1 {
	no Green
}

	// Every signal will eventually become green
pred prop2 {
	all s : Signal | eventually s in Green
}
	
    // Trains never move
pred prop3 {
	always pos' = pos
}
	
    // There are no collisions between trains
pred prop4 {
  all t1,t2:Train | always t1.pos!=t2.pos 
}

	// A train inside the station can only move to one of the next tracks (or exit the station if it is in an exit track)
pred prop5 {
	all t : Train | always (some t.pos implies (t.pos' = t.pos or (t.pos in Exit implies no t.pos' else (some t.pos' and t.pos' in t.pos.prox))))
}

	// Signals are always alternating
pred prop6 {
	all s : Signal | always eventually (s in Green) and always eventually (s not in Green)
}

	// All trains inside the station will eventually leave the station
pred prop7 {
	all t : Train | always (some t.pos implies eventually no t.pos)
}
	
    // A train at a track with a red signal can only move after the signal becomes green
pred prop8 {
	all t : Train, p : Track | always (t.pos = p and p.signal not in Green implies (p.signal in Green releases t.pos = p))
}

	// All trains will eventually enter the station in entry tracks
pred prop9 {
	all t : Train | no t.pos until (some t.pos & Entry)
}

	// Is is always the case that at most one signal before a junction can be green
pred prop10 {
	all j : Junction | always lone (prox.j).signal & Green	
}
	
    // It is always the case that trains inside the station where previously at a an entry track
pred prop11 {
	all t : Train | always (some t.pos implies once some t.pos & Entry)
}

	// A train positioned in a track previously passed through all tracks that connect it to an entry track
pred prop12 {
	all t : Train | always (some t.pos implies some e : *prox.(t.pos) & Entry | all x : *prox.(t.pos) & e.*prox | once t.pos = x)
}

	// Trains that left the station never return
pred prop13 {
	all t : Train | always ((no t.pos and once some t.pos) implies always no t.pos)
}

	// Immediately after a train leaves a track with a green signal the signal turns red
pred prop14 {
	all s : Signal, t : Train | always (s in Green and t.pos = signal.s and t.pos' != signal.s implies after s not in Green)
}

	// Trains cannot remain forever stopped in same position
pred prop15 {
	all t : Train, p : Track | not (eventually always t.pos = p)
}

	// A train in an exit track was always inside the station since it arrived at an entry track
pred prop16 {
	all t : Train | always (some t.pos & Exit implies (some t.pos since some t.pos & Entry))
}

	// The first train to be inside the station will be the first to arrive at an exit track
pred prop17 {
	all t : Train | always ((some t.pos and historically no (Train-t).pos) implies (no Train.pos & Exit until some t.pos & Exit))
}

	//  When several trains are trying to enter a junction the first that arrived will have priority
pred prop18 {
	all j : Junction | always (all disj x,y : pos.(prox.j) | before (x in pos.(prox.j) and y not in pos.(prox.j)) implies (x in pos.j releases (y not in pos.j)))
}
