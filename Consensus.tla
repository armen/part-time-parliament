----------------------------- MODULE Consensus ------------------------------
EXTENDS Naturals,
        FiniteSets

CONSTANT Value

VARIABLE chosen

TypeOK == chosen \subseteq Value

Init == chosen = {}

Next == /\ chosen = {}
        /\ \E v \in Value : chosen' = {v}

Spec == Init /\ [][Next]_chosen
-----------------------------------------------------------------------------
(***************************************************************************)
(* Safety: At most one value is chosen.                                    *)
(***************************************************************************)
Safety == /\ TypeOK
          /\ Cardinality(chosen) <= 1

THEOREM Spec => []Safety
-----------------------------------------------------------------------------
(***************************************************************************)
(* Liveness: A value is eventually chosen.                                 *)
(***************************************************************************)
Liveness == <>(chosen # {})
FairSpec == Spec /\ WF_chosen(Next)

THEOREM FairSpec => Liveness
=============================================================================
