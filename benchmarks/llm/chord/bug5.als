
open util/ordering[Time] as trace
open util/ordering[Node] as ring


sig Time { }

abstract sig Event {
   pre:  Time,
   post: Time,
   cause: lone (Event - Null)
}

sig Null extends Event { } { no cause }

fact TemporalStructure {
   all t: Time - trace/last | one e: Event | e.pre = t 
   all t: trace/last | no  e: Event | e.pre = t 
   all e: Event | e.post = (e.pre).next  
}

fact CauseHasSingleEffect { cause in Event lone -> Event }

fact CausePrecedesEffect { 
   all e1, e2: Event | e1 = e2.cause => lt[e1.pre,e2.pre]  }


sig Node {
   succ: Node -> Time,
   succ2: Node -> Time,
   prdc: Node -> Time,
   bestSucc: Node -> Time }
{  
   all t: Time | lone n : Node | n -> t in succ
   all t: Time | lone n : Node | n -> t in succ2
   all t: Time | lone n : Node | n -> t in prdc
   all t: Time | lone n : Node | n -> t in bestSucc
-- This defines bestSucc.
   all t: Time |
      (Member[succ.t,t] && Member[succ2.t,t] => bestSucc.t = succ.t)
   && (Member[succ.t,t] && NonMember[succ2.t,t] => bestSucc.t = succ.t)
   && (NonMember[succ.t,t] && Member[succ2.t,t] => bestSucc.t = succ2.t)
   && (NonMember[succ.t,t] && NonMember[succ2.t,t] => no bestSucc.t)

-- A node is unambiguously a member or not.
   all t: Time | Member[this,t] || NonMember[this,t]  
}

pred Member [n: Node, t: Time] { some n.succ.t or some n.prdc.t } // Added prdc condition
pred NonMember [n: Node, t: Time] {  
   no n.succ.t && no n.prdc.t && no n.succ2.t  }

pred Between [n1, n2, n3: Node] {
   lt[n1,n3] =>   ( lt[n1,n2] && lt[n2,n3] )
             else ( lt[n1,n2] || lt[n2,n3] )  }
                                       -- for all x and y,   Between{x,y,x]
                                             -- for all x, ! Between{x,x,x]
                                       -- for all x and y, ! Between{x,x,y]
                                       -- for all x and y, ! Between{y,x,x]


pred OneOrderedRing [t: Time] {
   let ringMembers = { n: Node | n in n.(^(bestSucc.t)) } |
      some ringMembers                                 -- at least one ring
   && (all disj n1, n2: ringMembers | n1 in n2.(^(bestSucc.t)) ) -- not two
   && (all disj n1, n2, n3: ringMembers |               -- ring is globally
         n2 = n1.bestSucc.t => ! Between[n1,n3,n2]      -- ordered
      )
}

pred ConnectedAppendages [t: Time] { 
   let members = { n: Node | Member[n,t] } |
   let ringMembers = { n: members | n in n.(^(bestSucc.t)) } |
      all na: members - ringMembers |                           -- na is in
         some nc: ringMembers | nc in na.(^(bestSucc.t))    -- an appendage
                                                        -- yet reaches ring
}

pred AntecedentPredecessors [t: Time] {
   all n: Node | let antes = (succ.t).n | 
      Member[n.prdc.t,t] => n.prdc.t in antes
}  

pred OrderedAppendages [t: Time] {
   let members = { n: Node | Member[n,t] } |
   let ringMembers = { n: members | n in n.(^(bestSucc.t)) } |
   let appendSucc = bestSucc.t - (ringMembers -> Node) |
      all n: ringMembers |
         all disj a1, a2, a3: (members - ringMembers) + n |
            (  n in a1.(^appendSucc)
            && a2 = a1.appendSucc
            && (a1 in a3.(^appendSucc) || a3 in a2.(^appendSucc) )
            )  => ! Between[a1,a3,a2]
}

pred OrderedMerges [t: Time] {
   let ringMembers = { n: Node | n in n.(^(succ.t)) } |
      all disj n1, n2, n3: Node |
         (  n3 in n1.bestSucc.t
         && n3 in n2.bestSucc.t
         && n1 in ringMembers 
         && n2 !in ringMembers
         && n3 in ringMembers 
         ) => Between[n1,n2,n3]
}

pred DistinctSuccessors [t: Time] {
   let members = { n: Node | Member[n,t] } |
      let ringMembers = { n: members | n in n.(^(succ.t)) } |
         all n: members |
         (  (n.succ2.t = n.succ.t => 
                                (# ringMembers  = 1 && n in ringMembers))
         && (n.succ2.t = n        => 
                                (# ringMembers <= 2 && n in ringMembers))
         )
}

pred OrderedSuccessors [t: Time] {
   let members = { n: Node | Member[n,t] } |
      let ringMembers = { n: members | n in n.(^(succ.t)) } |
         all n: members | 
            some n.succ2.t => 
            (  Between[n,n.succ.t,n.succ2.t] || n = ringMembers  )
}

pred ValidSuccessorList [t: Time] { 
   let members = { n: Node | Member[n,t] } |
   all disj n, m: members | 
      let antes = (succ.t).n |
         Between[n.succ.t,m,n.succ2.t]
                                  -- n's successors skip over a live node m
         => m !in antes.succ2.t
                          -- m is not in successor list of any n antecedent
}  

pred ReachableSuccessor2 [t: Time] {
   let members = { n: Node | Member[n,t] } |
   let ringMembers = { n: Node | n in n.(^(bestSucc.t)) } |
   (  (all n: members - ringMembers | 
         Member[n.succ2.t,t] => n.succ2.t in n.(^(bestSucc.t))
      )
   && (all n: ringMembers | 
         Member[n.succ2.t,t] 
      => (  n.succ2.t in ringMembers
         || (  let altSucc = bestSucc.t + n->n.succ2.t - n->n.succ.t |
               let altRingMembers = { a: Node | a in n.(^(altSucc)) } |
                  all disj a1, a2, a3: altRingMembers |  
                     a2 = a1.altSucc => ! Between[a1,a3,a2]  
            )
         )
      )
   )
}

pred AvengerInvariant [t: Time] {
   let members = { n: Node | Member[n,t] } |
      all n: members | 
         Member[n.prdc.t,t] => ! Between[n.prdc.t,n.bestSucc.t,n]
}

pred Valid [t: Time] { 
      OneOrderedRing[t]                          -- from PODC Full, revised
   && ConnectedAppendages[t]                     -- from PODC Full, revised
   && AntecedentPredecessors[t]                                      -- new
   && OrderedAppendages[t]                                -- from PODC Full
   && OrderedMerges[t]                                    -- from PODC Full
   && DistinctSuccessors[t]                                          -- new
   && OrderedSuccessors[t]                                           -- new
   && ValidSuccessorList[t]                      -- from PODC Full, revised
   && ReachableSuccessor2[t]                                         -- new
}

-- These are the only properties needed for an undisturbed network to
-- become ideal through stabilization and reconciliation.
pred CoreValid [t: Time] { 
      OneOrderedRing[t]       
   && ConnectedAppendages[t] 
}

pred SomeBestSuccessor [t: Time] { 
   all n: Node | Member[n,t] => some n.bestSucc.t  }

assert ValidImpliesSomeBestSuccessor {
   all t: Time | Valid[t] => SomeBestSuccessor[t] }
check ValidImpliesSomeBestSuccessor for 7 but 0 Event, 1 Time


pred Stable [t: Time] { let members = { n: Node | Member[n,t] } |
   all n1, n2: members | n2 = n1.succ.t <=> n1 = n2.prdc.t
}

pred AllRing [t: Time] { let members = { n: Node | some n.succ.t } |
   all n1, n2: members | n2 in n1.(^(succ.t))
}

pred Reconciled [t: Time] { let members = { n: Node | Member[n,t] } |
   all n: members | 
         Member[n.succ.t,t] 
      && Member[n.succ2.t,t]
      && n.succ2.t = (n.succ.t).succ.t
}

pred Succ2Correctness [t: Time] { let members = { n: Node | Member[n,t] } |
   all n: members |
      (Member[n.succ2.t,t] && n.succ2.t != n.bestSucc.t)
   => n.succ2.t = (n.bestSucc.t).bestSucc.t
}

pred Ideal [t: Time] {  
      Valid[t] 
   && Stable[t]                                  -- from PODC Full, revised
   && Reconciled[t]                              -- from PODC Full, revised
}

assert IdealImpliesAllRing { all t: Time | Ideal[t] => AllRing[t] }
check IdealImpliesAllRing for 7 but 0 Event, 1 Time

assert IdealImpliesSucc2Correct { all t: Time | 
   Ideal[t] => Succ2Correctness[t] }
check IdealImpliesSucc2Correct for 7 but 0 Event, 1 Time


abstract sig RingEvent extends Event { node: Node }
sig Join extends RingEvent { } { no cause }
sig Stabilize extends RingEvent { } { no cause  }
sig Notified extends RingEvent { newPrdc: Node } { some cause }
sig Fail extends RingEvent { } { no cause }
sig Flush extends RingEvent { } { no cause }
sig Update extends RingEvent { } { no cause }
sig Reconcile extends RingEvent { } { no cause }

fact NonMemberCanJoin {
   all j: Join, n: j.node, t: j.pre | {
      NonMember[n,t]
      (some m: Node |    Member[m,t]
                      && Between[m,n,m.succ.t]
                      && Member[m.succ.t,t]
                      && n.succ.(j.post) = m.succ.t
      )
      no n.prdc.(j.post)
      no cause:>j
}  }

fact StabilizeMayChangeSuccessor {
   all s: Stabilize, n: s.node, t: s.pre |
   let newSucc = (n.succ.t).prdc.t       | {
      Member[n,t]
      Member[n.succ.t,t]
      (  (  some newSucc
         && Between[n,newSucc,n.succ.t]
         && Member[newSucc,t]
         )
         -- accept new successor or not
         => n.succ.(s.post) = newSucc else n.succ.(s.post) = n.succ.t
      )
      (some f: Notified |   f.cause = s
                       && f.node = n.succ.(s.post)
                       && f.newPrdc = n
      )
}  }

fact NotifiedMayChangePredecessor {
   all f: Notified, n: f.node, p: f.newPrdc, t: f.pre |
      (   Member[n,t]
      && (no n.prdc.t || Between[n.prdc.t,p,n])
      )
   -- accept new predecessor
      =>   (n.prdc.(f.post) = p && no cause:>f)
   -- else do nothing
      else (n.prdc.(f.post) = n.prdc.t && no cause:>f)
}

fact MemberCanFail {
   all f: Fail, n: f.node, t: f.pre | {
      Member[n,t]
      (all m: Node | m.succ.t = n => Member[m.succ2.t,t])
      (all m: Node | m.succ2.t = n => Member[m.succ.t,t])
      n.succ.t != n.succ2.t
      NonMember[n,f.post] 
      no cause:>f
}  }

fact FlushMayChangePredecessor {
   all f: Flush, n: f.node, t: f.pre | {
      (Member[n,t] && NonMember[n.prdc.t,t])
         =>   no n.prdc.(f.post) 
         else n.prdc.(f.post) = n.prdc.t
      no cause:>f
}  }

fact UpdateMayChangeSuccessor {
   all u: Update, n: u.node, t: u.pre |
      let oldSucc = n.succ.t |  
      let oldSucc2 = n.succ2.t | {
         (Member[n,t] && NonMember[oldSucc,t] && some oldSucc2)
         =>   (  n.succ.(u.post) = oldSucc2
              && no n.succ2.(u.post)
              )
         else (n.succ.(u.post) = oldSucc && n.succ2.(u.post) = oldSucc2)
                               --  at least one of the two must be a member
      no cause:>u
}  }

fact ReconcileMayChangeSuccessor2 {
   all r: Reconcile, n: r.node, t: r.pre |
      let oldSucc2 = n.succ2.t      | 
      let newSucc2 = (n.succ.t).succ.t | {      -- not necessarily a member
         (  Member[n,t] 
         && Member[n.succ.t,t]
         && newSucc2 != oldSucc2                   -- this must be a change
         && (newSucc2 = n.succ.t =>           -- this must not be redundant
                 n.succ.t = n)                  
         )  =>   n.succ2.(r.post) = newSucc2
            else n.succ2.(r.post) = oldSucc2
         no cause:>r
}  }


fact SuccessorFieldFrameCondition {
   all e: Event, n: Node | n.succ.(e.pre) != n.succ.(e.post)
   => (  (e in Join && e.node = n)
      || (e in Stabilize && e.node = n)
      || (e in Fail && e.node = n)
      || (e in Update && e.node = n)
      )
}

fact Successor2FieldFrameCondition {
   all e: Event, n: Node | n.succ2.(e.pre) != n.succ2.(e.post)
   => (  (e in Fail && e.node = n)
      || (e in Update && e.node = n)
      || (e in Reconcile && e.node = n)
      )
}

fact PredecessorFieldFrameCondition {
   all e: Event, n: Node | n.prdc.(e.pre) != n.prdc.(e.post)
   => (  (e in Notified && e.node = n)
      || (e in Fail && e.node = n)
      || (e in Flush && e.node = n)
      )
}

pred StabilizationWillChangeSuccessor [n, nSucc: Node, t: Time] {
   let newSucc = (n.succ.t).prdc.t |
         Member[n,t]
      && some newSucc
      && Between[n,newSucc,n.succ.t]
      && Member[newSucc,t]
      && nSucc = newSucc
}

pred StabilizationShouldChangePredecessor [n, nSucc: Node, t: Time] {
   (  (  StabilizationWillChangeSuccessor[n,nSucc,t]
      || (nSucc = n.succ.t && Member[n,t] && Member[nSucc,t])
      )
   && (  no nSucc.prdc.t 
      || (some nSucc.prdc.t && Between[nSucc.prdc.t,n,nSucc])
      )
   )
}

pred ReconciliationWillFlushPredecessor [n: Node, t: Time] {
   Member[n,t] && some n.prdc.t && NonMember[n.prdc.t,t] }

pred ReconciliationWillChangeSuccessor [n, nSucc: Node, t: Time] {
      Member[n,t] && NonMember[n.succ.t,t] 
   && some n.succ2.t && nSucc = n.succ2.t }

pred ReconciliationWillChangeSuccessor2 [n, nSucc2: Node, t: Time] {
   let oldSucc2 = n.succ2.t |
   let newSucc2 = (n.succ.t).succ.t | 
         Member[n,t] 
      && Member[n.succ.t,t]
      && nSucc2 = newSucc2
      && newSucc2 != oldSucc2
      && (newSucc2 = n.succ.t => n.succ.t = n)                  
}

assert ValidRingIsImprovable {
   (  CoreValid[trace/first] && ! Ideal[trace/first]  ) 
   =>
   (  (some n1, n2: Node | 
         StabilizationWillChangeSuccessor[n1,n2,trace/first])
   || (some n1, n2: Node | 
         StabilizationShouldChangePredecessor[n1,n2,trace/first])
   || (some n: Node | ReconciliationWillFlushPredecessor[n,trace/first])
   || (some n1, n2: Node | 
         ReconciliationWillChangeSuccessor[n1,n2,trace/first])
   || (some n1, n2: Node | 
         ReconciliationWillChangeSuccessor2[n1,n2,trace/first])
   )
}
check ValidRingIsImprovable for 5 but 0 Event, 1 Time 
check ValidRingIsImprovable for 7 but 0 Event, 1 Time 

assert IdealRingCannotImprove {
   Ideal[trace/first]
   =>
   (  (no n1, n2: Node | 
         StabilizationWillChangeSuccessor[n1,n2,trace/first])
   && (no n1, n2: Node | 
         StabilizationShouldChangePredecessor[n1,n2,trace/first])
   && (no n: Node | ReconciliationWillFlushPredecessor[n,trace/first])
   && (no n1, n2: Node | 
         ReconciliationWillChangeSuccessor[n1,n2,trace/first])
   && (no n1, n2: Node | 
         ReconciliationWillChangeSuccessor2[n1,n2,trace/first])
   )
}
check IdealRingCannotImprove for 5 but 0 Event, 1 Time 
check IdealRingCannotImprove for 7 but 0 Event, 1 Time 


assert InitialIsValid { 
   let members = { n: Node | Member[n,trace/first] } |
   (  one members 
   && members.succ.trace/first = members
   && no members.prdc.trace/first 
   && no members.succ2.trace/first
   ) => Valid[trace/first]
}
check InitialIsValid for 1 but 0 Event, 1 Time

assert JoinPreservesValidity {
   some Join && Valid[trace/first] => WeakJValid[trace/last] }
check JoinPreservesValidity for 3 but 1 Event, 2 Time
check JoinPreservesValidity for 4 but 1 Event, 2 Time
check JoinPreservesValidity for 5 but 1 Event, 2 Time 

pred WeakJValid [t: Time] { 
      OneOrderedRing[t]                       
   && ConnectedAppendages[t]               
-- && AntecedentPredecessors[t]    
-- && OrderedAppendages[t]        
-- && OrderedMerges[t]           
   && DistinctSuccessors[t]           
   && OrderedSuccessors[t]         
-- && ValidSuccessorList[t]     
-- && ReachableSuccessor2[t]  
}

assert StabilizationPreservesValidity {
   some Stabilize && Valid[trace/first] => WeakSValid[trace/last] }
check StabilizationPreservesValidity for 3 but 2 Event, 3 Time--    1587 ms
check StabilizationPreservesValidity for 4 but 2 Event, 3 Time--   19853 ms
check StabilizationPreservesValidity for 5 but 2 Event, 3 Time--  362522 ms

pred WeakSValid [t: Time] { 
      OneOrderedRing[t]                     
   && ConnectedAppendages[t]              
   && AntecedentPredecessors[t]         
   && OrderedAppendages[t]             
-- && OrderedMerges[t]              
-- && DistinctSuccessors[t]       
-- && OrderedSuccessors[t]      
   && ReachableSuccessor2[t]  
-- && ValidSuccessorList[t]    
}

assert FailPreservesValidity {
   some Fail && Valid[trace/first] => WeakFValid[trace/last] }
check FailPreservesValidity for 3 but 1 Event, 2 Time
check FailPreservesValidity for 4 but 1 Event, 2 Time
check FailPreservesValidity for 5 but 1 Event, 2 Time 

pred WeakFValid [t: Time] { 
      OneOrderedRing[t]                     
   && ConnectedAppendages[t]              
   && AntecedentPredecessors[t]         
-- && OrderedMerges[t]              
-- && OrderedAppendages[t]             
-- && DistinctSuccessors[t]       
-- && OrderedSuccessors[t]      
   && ValidSuccessorList[t]    
-- && ReachableSuccessor2[t]  
}

assert FlushPreservesValidity {
   some Flush && Valid[trace/first] => Valid[trace/last] }
check FlushPreservesValidity for 3 but 1 Event, 2 Time
check FlushPreservesValidity for 4 but 1 Event, 2 Time
check FlushPreservesValidity for 5 but 1 Event, 2 Time 

assert UpdatePreservesValidity { 
   some Update && Valid[trace/first] => Valid[trace/last]  }
check UpdatePreservesValidity for 3 but 1 Event, 2 Time
check UpdatePreservesValidity for 4 but 1 Event, 2 Time
check UpdatePreservesValidity for 5 but 1 Event, 2 Time

assert ReconcilePreservesValidity { 
   some Reconcile && Valid[trace/first] => WeakRValid[trace/last]  }
check ReconcilePreservesValidity for 3 but 1 Event, 2 Time
check ReconcilePreservesValidity for 4 but 1 Event, 2 Time
check ReconcilePreservesValidity for 5 but 1 Event, 2 Time 

pred WeakRValid [t: Time] { 
      OneOrderedRing[t]                     
   && ConnectedAppendages[t]              
   && AntecedentPredecessors[t]         
   && OrderedAppendages[t]             
   && OrderedMerges[t]              
   && DistinctSuccessors[t]       
-- && OrderedSuccessors[t]      
-- && ValidSuccessorList[t]    
   && ReachableSuccessor2[t]  
}

