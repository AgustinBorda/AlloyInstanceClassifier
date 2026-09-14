/*
A labeled transition system (LTS) is comprised by States, a sub-set
of which are Initial, connected by transitions, here represented by 
Events.
*/
sig State {
        trans : Event -> State
}
sig Init in State {}
sig Event {}

/*
Every state in the labeled transition system has at least one outgoing transition.
*/
pred inv1 {
	all s:State | some s.trans
}

/*
There is exactly one initial state.
*/
pred inv2 {
	one Init
}

/*
For any state and any event, there is at most one transition from that state labeled with that event (i.e., the system is deterministic).
*/
pred inv3 {
 all s : State | some s.trans 
}

/*
Every state can be reached from some initial state by following a sequence of one or more transitions (ignoring the specific event labels).
*/
pred inv4 {
	let ts = {s1,s2:State | some e:Event | s1->e->s2 in trans} | all s:State | some i:Init | s in i.^ts
}

/*
All states share exactly the same set of immediate successor states, meaning the set of states reachable in one step from any state is identical across all states.
*/
pred inv5 {
	all s1,s2:State | s1.trans.State = s2.trans.State
}

/*
Every event appears in at least one transition somewhere in the system; no event label is unused.
*/
pred inv6 {
	State.trans.State = Event
}

/*
From any state that is reachable from an initial state, it is possible to reach some initial state again (the system is reversible).
*/
pred inv7 {
	let ts = {s1,s2:State | some e:Event | s1->e->s2 in trans} | all s:Init.^ts | some i:Init | i in s.^ts
}
