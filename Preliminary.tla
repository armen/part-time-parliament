----------------------------- MODULE Preliminary ----------------------------
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
VARIABLES msgs, ledger

vars == <<msgs, ledger>>

TypeOK == /\ msgs \subseteq Message
          /\ ledger \in SUBSET Decree
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
CastNextBallot(b) == /\ Cast([type |-> "NextBallot", bal |-> b])
                     /\ UNCHANGED ledger

CastLastVote(q) ==
  \E m \in msgs :
     LET votes == {v \in Voted : v.pst = q /\ v.bal < m.bal} \cup {null(q)}
         maxVote == Max(votes)
     IN /\ m.type = "NextBallot"
        /\ Cast([type |-> "LastVote", bal |-> m.bal, vot |-> maxVote])
        /\ UNCHANGED ledger

CastBeginBallot(b) ==
  /\ ~ \E m \in msgs : m.type = "BeginBallot" /\ m.bal = b
  /\ \E Q \in Quorum, d \in Decree :
        LET lVotes  == LastVotes(b)
            maxVote == Max(lVotes)
            dec     == IF maxVote.dec = Blank THEN d ELSE maxVote.dec
        IN /\ \A q \in Q : (\E v \in lVotes : v.pst = q)
           /\ Cast([type |-> "BeginBallot", bal |-> b, dec |-> dec])
           /\ UNCHANGED ledger

CastVote(q) ==
  \E m \in msgs :
     /\ m.type = "BeginBallot"
     /\ ~ \E l \in msgs :
             /\ l.type = "LastVote" /\ l.vot.pst = q
             /\ l.vot.bal < m.bal /\ m.bal < l.bal
     /\ Cast([type |-> "Voted", vot |-> [pst |-> q, bal |-> m.bal, dec |-> m.dec]])
     /\ UNCHANGED ledger

CastSuccess(b) ==
  \E Q \in Quorum, d \in Decree :
     /\ \A q \in Q : (\E v \in Voted : v.pst = q /\ v.bal = b /\ v.dec = d)
     /\ ledger' = ledger \cup {d}
     /\ Cast([type |-> "Success", dec |-> d])

Write == \E m \in msgs : /\ m.type = "Success"
                         /\ ledger' = ledger \cup {m.dec}
                         /\ UNCHANGED msgs
-----------------------------------------------------------------------------
Init == /\ msgs = {}
        /\ ledger = {}

Next == \/ \E b \in Ballot : \/ CastNextBallot(b)
                             \/ CastBeginBallot(b)
                             \/ CastSuccess(b)
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
=============================================================================
