-------------------------------- MODULE Basic -------------------------------
EXTENDS Integers

CONSTANTS Decree, Prist, Quorum, Ballot

ASSUME /\ \A Q \in Quorum : Q \subseteq Prist
       /\ \A Q1, Q2 \in Quorum : Q1 \cap Q2 # {}
       /\ Ballot \subseteq Nat

Blank   == CHOOSE b : b \notin Decree \* Blank is not a decree
Null    == [pst : Prist, bal : {-1}, dec : {Blank}]
Vote    == [pst : Prist, bal : Ballot, dec : Decree]
Message ==      [type : {"NextBallot"}, bal : Ballot]
           \cup [type : {"LastVote"}, bal : Ballot, vot : Vote \cup Null]
           \cup [type : {"BeginBallot"}, bal : Ballot, dec : Decree]
           \cup [type : {"Voted"}, vot : Vote]
           \cup [type : {"Success"}, dec : Decree]
-----------------------------------------------------------------------------
VARIABLES msgs, ledger, lastTried, prevVote, nextBal

vars == <<msgs, ledger, lastTried, prevVote, nextBal>>

TypeOK == /\ msgs \subseteq Message
          /\ ledger \in SUBSET Decree
          /\ lastTried \in [Prist -> Ballot \cup {-1}]
          /\ prevVote \in [Prist -> Vote \cup Null]
          /\ nextBal \in [Prist -> Ballot \cup {-1}]
-----------------------------------------------------------------------------
(***************************************************************************)
(* Series of definitions to simplify the specification                     *)
(***************************************************************************)
null(p) == [pst |-> p, bal |-> -1, dec |-> Blank]
Voted == {v.vot : v \in {m \in msgs : m.type = "Voted"}}
LastVotes(b) == {v.vot : v \in {m \in msgs : m.type = "LastVote" /\ m.bal = b}}
Max(V) == CHOOSE v \in V : (\A w \in V : v.bal >= w.bal)
Cast(m) == msgs' = msgs \cup {m}
-----------------------------------------------------------------------------
CastNextBallot(p, b) == /\ b > lastTried[p]
                        /\ lastTried' = [lastTried EXCEPT ![p] = b]
                        /\ Cast([type |-> "NextBallot", bal |-> b])
                        /\ UNCHANGED <<ledger, prevVote, nextBal>>

CastLastVote(q) ==
  \E m \in msgs :
     /\ m.type = "NextBallot"
     /\ m.bal > nextBal[q]
     /\ nextBal' = [nextBal EXCEPT ![q] = m.bal]
     /\ Cast([type |-> "LastVote", bal |-> m.bal, vot |-> prevVote[q]])
     /\ UNCHANGED <<ledger, lastTried, prevVote>>

CastBeginBallot(p, b) ==
  /\ ~ \E m \in msgs : m.type = "BeginBallot" /\ m.bal = b
  /\ \E Q \in Quorum, d \in Decree :
        LET lVotes  == LastVotes(b)
            maxVote == Max(lVotes)
            dec     == IF maxVote.dec = Blank THEN d ELSE maxVote.dec
        IN /\ \A q \in Q : (\E v \in lVotes : v.pst = q)
           /\ b = lastTried[p]
           /\ Cast([type |-> "BeginBallot", bal |-> b, dec |-> dec])
           /\ UNCHANGED <<ledger, lastTried, prevVote, nextBal>>

CastVote(q) ==
  \E m \in msgs :
     /\ m.type = "BeginBallot"
     /\ LET vote == [pst |-> q, bal |-> m.bal, dec |-> m.dec]
        IN /\ m.bal = nextBal[q]
           /\ prevVote' = [prevVote EXCEPT ![q] = vote]
           /\ Cast([type |-> "Voted", vot |-> vote])
           /\ UNCHANGED <<ledger, lastTried, nextBal>>

CastSuccess(p, b) ==
  \E Q \in Quorum, d \in Decree :
     /\ b = lastTried[p]
     /\ \A q \in Q : (\E v \in Voted : v.pst = q /\ v.bal = b /\ v.dec = d)
     /\ ledger' = ledger \cup {d}
     /\ Cast([type |-> "Success", dec |-> d])
     /\ UNCHANGED <<lastTried, prevVote, nextBal>>

Write == \E m \in msgs : /\ m.type = "Success"
                         /\ ledger' = ledger \cup {m.dec}
                         /\ UNCHANGED <<msgs, lastTried, prevVote, nextBal>>

-----------------------------------------------------------------------------

Init == /\ msgs = {}
        /\ ledger = {}
        /\ lastTried = [p \in Prist |-> -1]
        /\ prevVote = [p \in Prist |-> null(p)]
        /\ nextBal = [p \in Prist |-> -1]

Next == \/ \E p \in Prist, b \in Ballot :
           \/ CastNextBallot(p, b)
           \/ CastBeginBallot(p, b)
           \/ CastSuccess(p, b)
        \/ \E q \in Prist : CastLastVote(q) \/ CastVote(q)
        \/ Write

-----------------------------------------------------------------------------
Spec == Init /\ [][Next]_vars
FairSpec == Spec /\ WF_vars(Next)

THEOREM Spec => []TypeOK
-----------------------------------------------------------------------------
C == INSTANCE Consensus WITH chosen <- ledger,
                             Value <- Decree
THEOREM Spec => C!Spec
THEOREM Spec => []C!Safety
THEOREM FairSpec => C!FairSpec
THEOREM FairSpec => C!Liveness
-----------------------------------------------------------------------------
P == INSTANCE Preliminary

THEOREM Spec => P!Spec
THEOREM FairSpec => P!FairSpec
=============================================================================
