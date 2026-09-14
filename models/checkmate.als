module checkmate

/////////////////////////////////////////////////////////////////////////////////////
// Candidate Executions module
/////////////////////////////////////////////////////////////////////////////////////

// A CPU core on which events execute. Every event is associated with exactly one core.
sig Core { }

// An abstract execution context or security principal. Events belong to exactly one process,
// and physical memory regions are owned by exactly one process.
abstract sig Process { }

// The malicious process in the model.
one sig Attacker extends Process { }

// The victim process in the model.
one sig Victim extends Process { }

// Abstract address. Concrete addresses are either virtual or physical.
abstract sig Address { }

// Classifies whether a virtual address is cacheable or non-cacheable.
abstract sig Cacheability { }

// The unique cacheable cacheability designation.
one sig Cacheable extends Cacheability { }

// The non-cacheable designation. It is `lone`, so at most one such object exists.
lone sig NonCacheable extends Cacheability { }

// L1 cache index associated with a virtual address.
sig CacheIndexL1 { }

// A virtual memory address. It has an L1 cache index, maps to exactly one physical address,
// and has a cacheability attribute.
sig VirtualAddress extends Address { 
	indexL1: one CacheIndexL1,
	map: one PhysicalAddress,
	cacheability: one Cacheability
}

// A physical memory address. It records which processes may read or write it, and
// which process owns the memory region containing this physical address.
sig PhysicalAddress extends Address {
    readers: set Process,
    writers: set Process,
    region: one Process
}

// An abstract event in the candidate execution. It carries program order, process, core,
// coherence-related events, and many 4-ary universal-happens-before sub-relations over
// (event, location) nodes. NodeRel lists the locations at which this event is instantiated.
abstract sig Event {	
	po: lone Event,                 // immediate program-order successor
	NodeRel: set Location,          // event-location pairs instantiated as Nodes

	process: one Process,           // process that performs the event
	coh: set Event,                 // coherence-related events (not constrained further)
   	core: one Core,                 // core on which the event executes

	sub_uhb: set Location->Event->Location,  // overall universal happens-before sub-relation
	urf : set Location->Event->Location,
	uco : set Location->Event->Location,
	ufr : set Location->Event->Location,
	ustb_flush: set Location->Event->Location,
	udep : set Location->Event->Location,
	uhb_spec : set Location->Event->Location,
	ucoh_inter : set Location->Event->Location,
	ucoh_intra : set Location->Event->Location,
	ustb: set Location->Event->Location,
	uvicl: set Location->Event->Location,		
  	ucci: set Location->Event->Location,
  	usquash: set Location->Event->Location,
  	ufence: set Location->Event->Location,
	uflush: set Location->Event->Location,	
	uhb_inter: set Location->Event->Location,
	uhb_intra: set Location->Event->Location,
	uhb_proc: set Location->Event->Location
}

// An event that accesses a virtual address.
abstract sig MemoryEvent extends Event {
	address: one VirtualAddress
}

// A read event. The `dep` field relates this read to memory events or cache flushes
// that depend on it.
sig Read extends MemoryEvent {
    dep : set { MemoryEvent + CacheFlush }
}

// A write event. `rf` relates this write to reads that obtain their value from it,
// and `co` relates this write to later writes in coherence order for the same address.
sig Write extends MemoryEvent {
	rf: set Read,
	co: set Write
}

// Abstract fence event.
abstract sig Fence extends Event { }

// A sequentially consistent fence. The `sc` field totally orders SC fences.
sig FenceSC extends Fence { 
	sc: set FenceSC
}

// A cache flush event. It flushes the cache line corresponding to a virtual address.
sig CacheFlush extends Event { 
    flush_addr : one VirtualAddress
}

// A branch event. It records the actual outcome and the predicted outcome.
sig Branch extends Event {
	outcome : one Outcome,
	prediction : one Outcome
}

// Abstract branch outcome.
abstract sig Outcome { }

// Branch was taken.
one sig Taken extends Outcome { }

// Branch was not taken.
one sig NotTaken extends Outcome { }

// Program order is acyclic.
fact po_acyclic { acyclic[po] }

// Each event has at most one immediate program-order predecessor.
fact po_prior { all e: Event | lone e.~po }

// Pairs of memory events in the transitive closure of program order that access
// the same physical address.
fun po_loc : MemoryEvent->MemoryEvent { ^po & (address.map).~(address.map) }	

// All dependency edges are contained in transitive program order.
fact dep_in_po { dep in ^po }

// The communication relation is the union of read-from, from-read, and coherence-order.
fun com : MemoryEvent->MemoryEvent { rf + fr + co }

// Communication only occurs between events that access the same physical address.
fact com_in_same_addr { com in (address.map).~(address.map) }	

// Coherence order is transitive.
fact co_transitive { transitive[co] }

// Writes to the same physical address are totally ordered by coherence.
fact co_total { all a: Address | total[co, a.~(address.map) & Write] }

// Each read has at most one source write in the read-from relation.
fact lone_source_write { rf.~rf in iden }

// From-read relation: a read is from-read before a write if it reads from a write
// coherence-before that write, or if it is an initial-state read and the write is
// to the same physical address.
fun fr : Read->Write {							
  ~rf.co																							
  +
  ((Read - (Write.rf)) <:  ((address.map).~(address.map)) :> Write)		
}

// SC fences are totally ordered by the `sc` relation.
fact sc_total { total[sc, FenceSC] }

// Pairs of memory events that are separated in program order by an SC fence.
fun fence_sc : MemoryEvent->MemoryEvent { (MemoryEvent <: *po :> FenceSC).(FenceSC <: *po :> MemoryEvent) }

/////////////////////////////////////////////////////////////////////////////////////
// Check module
/////////////////////////////////////////////////////////////////////////////////////

// An abstract location used to instantiate events as Nodes.
abstract sig Location { }

// A Node represents an event occurrence at a location. The `uhb` relation is the
// universal happens-before relation between Nodes.
sig Node {
	event: one Event,
	loc: one Location,
	uhb: set Node
}

// Every 4-ary sub_uhb edge is between event-location pairs that actually exist in NodeRel.
fact { 
all e, e" : Event | all l, l" : Location | e->l->e"->l" in sub_uhb => ( e->l in NodeRel and e"->l" in NodeRel ) 
}

// `sub_uhb` is exactly the union of all the individual universal-happens-before sub-relations.
fact {
			{ 	urf +
         		uco +
				ufr + 
				udep +
				uhb_spec +
				ucoh_inter +
				ucoh_intra +
				ustb +
				ustb_flush +
				uvicl	+
				ucci +
				usquash +
				uflush +
				uhb_inter +
				uhb_intra +
				uhb_proc
			} = sub_uhb
}

// No self-loop edge is allowed in sub_uhb.
fact { all e, e" : Event | all l, l" : Location | e->e" in iden and l->l" in iden => not e->l->e"->l" in sub_uhb  }

// Every NodeRel event-location pair has exactly one Node.
fact { all e : Event | all l : Location  | e->l in NodeRel => one n : Node | n.event = e and n.loc = l }

// Every Node corresponds to a NodeRel pair.
fact { all n : Node | n.event->n.loc in NodeRel }

// The Node-level uhb relation is equivalent to the 4-ary sub_uhb relation.
fact { all n, n" : Node | n->n" in uhb <=> n.event->n.loc->n".event->n".loc in sub_uhb }

// uhb_intra only relates the same event to different locations.
fact { all e, e" : Event | all l, l" : Location | EdgeExists[e, l, e", l", uhb_intra] => SameEvent[e, e"] }

// uhb_inter only relates different events.
fact { all e, e" : Event | all l, l" : Location | EdgeExists[e, l, e", l", uhb_inter] => not SameEvent[e, e"] }

// uhb_inter only relates events on the same thread/program-order component.
fact { all e, e" : Event | all l, l" : Location | EdgeExists[e, l, e", l", uhb_inter] => SameThread[e, e"] }

// The universal happens-before relation on Nodes must be acyclic.
pred ucheck { acyclic[uhb] }

//////////////////////////////////////////////////////////////////////////////////////////////////////////////
// =Alloy shortcuts=
//////////////////////////////////////////////////////////////////////////////////////////////////////////////

// Returns the reflexive closure of a binary relation.
fun optional[f: univ->univ] : univ->univ { iden + f }

// True if the binary relation on Event is transitive.
pred transitive[rel: Event->Event] { rel.rel in rel }

// True if the binary relation on Event is irreflexive.
pred irreflexive[rel: Event->Event] { no iden & rel }

// True if the binary relation on Node is irreflexive.
pred irreflexive[rel: Node->Node] { no iden & rel }

// True if the binary relation on Event is acyclic.
pred acyclic[rel: Event->Event] { irreflexive[^rel] }

// True if the binary relation on Node is acyclic.
pred acyclic[rel: Node->Node] { irreflexive[^rel] }

// True if the relation totally orders all distinct elements of `bag` and is acyclic.
pred total[rel: Event->Event, bag: Event] {
  all disj e, e": bag | e->e" in rel + ~rel	
  acyclic[rel]											
}

// True if the 4-ary node relation has no self-loop on (event, location) pairs.
pred u_irreflexive[node_rel: Event->Location->Event->Location] {
	no node_rel or (		all e, e": Event |
								all l, l": Location |
								e->l->e"->l" in node_rel => not ( (e->e") in iden and (l->l") in iden )
							)
}

//////////////////////////////////////////////////////////////////////////////////////////////////////////////
// =Alloy Check predicates and functions=
//////////////////////////////////////////////////////////////////////////////////////////////////////////////

// Returns the root event of the program-order chain containing e, i.e., the first
// event in program order on the same thread as e.
fun CoreOf[e: Event] : Event { ( (Event - (Event.po)) & e ) + ( (Event - (Event.po)) & (^po.e) ) }

// All reads whose virtual address is cacheable.
fun CacheableRead : Read { Read <: address.cacheability.Cacheable }

// All reads whose virtual address is non-cacheable.
fun NonCacheableRead : Read { Read <: address.cacheability.NonCacheable }

// All writes whose virtual address is cacheable.
fun CacheableWrite : Write { Write <: address.cacheability.Cacheable }

// All writes whose virtual address is non-cacheable.
fun NonCacheableWrite : Write { Write <: address.cacheability.NonCacheable }

// All memory events whose virtual address is cacheable.
fun CacheableEvent : MemoryEvent { MemoryEvent <: address.cacheability.Cacheable }

// All memory events whose virtual address is non-cacheable.
fun NonCacheableEvent : MemoryEvent { MemoryEvent <: address.cacheability.NonCacheable }

// All events performed by the Attacker process.
fun AttackerEvent : Event { process.Attacker }

// All events performed by the Victim process.
fun VictimEvent : Event { process.Victim }

// All reads performed by the Attacker.
fun AttackerRead : Event { Read <: process.Attacker }

// All writes performed by the Attacker.
fun AttackerWrite : Event { Write <: process.Attacker }

// All reads performed by the Victim.
fun VictimRead : Event { Read <: process.Victim }

// All writes performed by the Victim.
fun VictimWrite : Event { Write <:  process.Victim }

// Returns the physical address(es) associated with an event, for either a memory
// access or a cache flush. Returns empty set if the event is neither.
fun PhysicalAddress[e: Event] : PhysicalAddress { e.address.map + e.flush_addr.map }

// Returns the virtual address(es) associated with an event, for either a memory
// access or a cache flush. Returns empty set if the event is neither.
fun VirtualAddress[e: Event] : VirtualAddress { e.address + e.flush_addr }

// Branches whose predicted outcome equals their actual outcome.
fun PredictedBranch : Branch { ((outcome.~prediction) & iden).Branch }

// Branches whose predicted outcome differs from their actual outcome.
fun MispredictedBranch : Branch { Branch - ((outcome.~prediction) & iden).Branch }

// True if the event-location pair exists in NodeRel.
pred NodeExists[e: Event, l: Location] { e->l in NodeRel }

// True if there is an edge in the given 4-ary node relation from (e,l) to (e",l").
pred EdgeExists[e: Event, l: Location, e": Event, l": Location, node_rel: Event->Location->Event->Location] {
	e->l->e"->l" in node_rel
}

// True if the read obtains its value from the initial state (has no source write).
pred DataFromInitialStateAtPA[r: Read] { r in {Read - Write.rf} }

// True if event e depends on read r via the `dep` relation.
pred HasDependency[r: Event, e: Event] { r->e in dep }

// True if e is a MemoryEvent.
pred IsAnyMemory[e: Event] { e in MemoryEvent }

// True if e is a Read.
pred IsAnyRead[e: Event] { e in Read }

// True if e is a Write.
pred IsAnyWrite[e: Event] { e in Write }

// True if e is a Fence.
pred IsAnyFence[e: Event] { e in Fence }

// Despite the name, this predicate checks whether e is a Fence.
// It appears to be a typo: the body is `e in Fence`, not `e in Branch`.
pred IsAnyBranch[e: Event] { e in Fence }

// True if e is a CacheFlush.
pred IsCacheFlush[e: Event] { e in CacheFlush }

// True if e and e" are performed by the same process.
pred SameProcess[e: Event, e": Event] { e->e" in process.~process }

// True if e and e" execute on the same core.
pred SameCore[e: Event, e": Event] { e->e" in core.~core }

// True if e and e" are in the same program-order thread (same connected component of po).
pred SameThread[e: Event, e": Event] { e->e" in ^po + ^~po }

// True if locations l and l" are the same object.
pred SameLocation[l: Location, l": Location] { l->l" in iden }

// True if events e and e" are the same object.
pred SameEvent[e: Event, e": Event] { e->e" in iden }

// True if e is before e" in transitive program order.
pred ProgramOrder[e: Event, e": Event] { e->e" in ^po }

// True if the memory event e accesses a cacheable virtual address.
pred IsCacheable[e: MemoryEvent] { (e.address).cacheability = Cacheable }

// True if e is a read or cache flush and its process is not an allowed reader of the physical address.
pred IsIllegalRead[e: MemoryEvent] {
	(IsAnyRead[e] or IsCacheFlush[e]) and (not (e.process in PhysicalAddress[e].readers))
}

// True if e is a write and its process is not an allowed writer of the physical address.
pred IsIllegalWrite[e: MemoryEvent] {
	IsAnyWrite[e] and (not (e.process in PhysicalAddress[e].writers))
}

// True if event e depends on an illegal read.
pred DependsOnIllegal[e : MemoryEvent] {
	some r: Read | r->e in dep and IsIllegalRead[r]
}

// True if e is a read that reads from an illegal write.
pred ReadsFromIllegal[e : MemoryEvent] {
	IsAnyRead[e] and (some w: Write | w->e in rf and IsIllegalWrite[w])
}

// True if the L1 cache indexes of the two events" virtual addresses are equal.
pred SameIndexL1 [e: Event, e": Event] { (e.address).indexL1 = (e".address).indexL1 }

// True if process P has exactly i program-order roots (threads).
pred NumProcessThreads[i: Int, P: Process] {
	#((Event - (Event.po)) & process.P) = i
}

// True if there are exactly i program-order roots (threads) in total.
pred NumThreads[i: Int] {
	#(Event - (Event.po)) = i
}

// True if e and e" refer to the same physical address, considering both memory accesses and cache flushes.
pred SamePhysicalAddress[e: Event, e": Event] {
    e->e" in (address.map).~(address.map) or
	e->e" in (flush_addr.map).~(address.map) or
	e->e" in (address.map).~(flush_addr.map) or
	e->e" in (flush_addr.map).~(flush_addr.map)
}

// True if e and e" refer to the same virtual address, considering both memory accesses and cache flushes.
pred SameVirtualAddress[e: Event, e": Event] { 
    e->e" in address.~address or
	e->e" in flush_addr.~address or
	e->e" in address.~flush_addr or
    e->e" in flush_addr.~flush_addr
}

// True if reads r and r" obtain their value from the same source: either both read
// from the initial state, or both read from the same write.
pred SameSourcingWrite[r: Read, r": Read] {
	not SameEvent[r, r"] and (
		DataFromInitialStateAtPA[r] and DataFromInitialStateAtPA[r"] or
    	r->r" in ~rf.rf 
	)
}
