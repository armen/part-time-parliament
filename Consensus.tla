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
Inv == /\ TypeOK
       /\ Cardinality(chosen) <= 1

THEOREM Spec => []Inv
-----------------------------------------------------------------------------
(***************************************************************************)
(* Liveness: A value is eventually chosen.                                 *)
(***************************************************************************)
Success  == <>(chosen # {})
LiveSpec == Spec /\ WF_chosen(Next)

THEOREM LiveSpec => Success
=============================================================================
