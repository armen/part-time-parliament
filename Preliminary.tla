----------------------------- MODULE Preliminary ----------------------------
EXTENDS Integers

CONSTANTS Decree, Prist, Quorum

ASSUME /\ \A Q \in Quorum : Q \subseteq Prist
       /\ \A Q1, Q2 \in Quorum : Q1 \cap Q2 # {}

Ballot == Nat

Blank == CHOOSE b : b \notin Decree \* Blank is not a decree

Vote    == [pst : Prist, bal : Ballot \cup {-1}, dec : Decree \cup {Blank}]
Message ==      [type : {"NextBallot"}, bal : Ballot]
           \cup [type : {"LastVote"}, bal : Ballot, vote : Vote]
           \cup [type : {"BeginBallot"}, bal : Ballot, dec : Decree]
           \cup [type : {"Voted"}, vote : Vote]
           \cup [type : {"Success"}, bal : Ballot, dec : Decree]
-----------------------------------------------------------------------------
VARIABLES
    msgs,
    ledger

vars == <<msgs, ledger>>

TypeOK == /\ msgs \subseteq Message
          /\ ledger \in SUBSET Decree
-----------------------------------------------------------------------------
(***************************************************************************)
(* Series of definitions to simplify the specification                     *)
(***************************************************************************)
Votes(M)   == {m.vote : m \in M}
MaxVote(V) == CHOOSE v \in V : (\A w \in V : v.bal >= w.bal)

Cast(m) == msgs' = msgs \cup {m}
-----------------------------------------------------------------------------
CastNextBallot(b) == /\ Cast([type |-> "NextBallot", bal |-> b])
                     /\ UNCHANGED ledger

CastLastVote(p) ==
  \E m \in msgs :
     LET null(pst) == [pst |-> pst, bal |-> -1, dec |-> Blank]
         voted == {v \in msgs : /\ v.type = "Voted"}
         votes == {v \in Votes(voted) : v.pst = p /\ v.bal < m.bal} \cup {null(p)}
         maxVote == MaxVote(votes)
     IN /\ m.type = "NextBallot"
        /\ Cast([type |-> "LastVote", bal |-> m.bal, vote |-> maxVote])
        /\ UNCHANGED ledger

CastBeginBallot(b, d) ==
  /\ ~ \E m \in msgs : m.type = "BeginBallot" /\ m.bal = b
  /\ \E Q \in Quorum :
        LET lvotes  == {m \in msgs : m.type = "LastVote" /\ m.bal = b}
            votes   == Votes(lvotes)
            maxVote == MaxVote(votes)
            dec     == IF maxVote.dec = Blank THEN d ELSE maxVote.dec
        IN /\ \A q \in Q : \E v \in votes : v.pst = q
           /\ Cast([type |-> "BeginBallot", bal |-> b, dec |-> dec])
           /\ UNCHANGED ledger

CastVote(p) ==
  \E m \in msgs :
     /\ m.type = "BeginBallot"
     /\ ~ \E l \in msgs : /\ l.type = "LastVote" /\ l.vote.pst = p
                          /\ IF l.bal > l.vote.bal THEN
                                l.bal > m.bal /\ l.vote.bal < m.bal
                             ELSE
                                l.vote.bal > m.bal /\ l.bal < m.bal
     /\ Cast([type |-> "Voted", vote |-> [pst |-> p, bal |-> m.bal, dec |-> m.dec]])
     /\ UNCHANGED ledger

CastSuccess(b, d) ==
  \E Q \in Quorum :
     LET voted == {m \in msgs : m.type = "Voted"}
         votes == {v.vote : v \in voted}
     IN /\ \A q \in Q : (\E v \in votes : v.pst = q /\ v.dec = d)
        /\ ledger' = ledger \cup {d}
        /\ Cast([type |-> "Success", bal |-> b, dec |-> d])

Write == \E m \in msgs : /\ m.type = "Success"
                         /\ ledger' = ledger \cup {m.dec}
                         /\ UNCHANGED msgs
-----------------------------------------------------------------------------
Init == /\ msgs = {}
        /\ ledger = {}

Next == \/ \E b \in Ballot :
           \/ CastNextBallot(b)
           \/ \E d \in Decree : CastBeginBallot(b, d) \/ CastSuccess(b, d)
        \/ \E p \in Prist : CastLastVote(p) \/ CastVote(p)
        \/ Write

Spec == Init /\ [][Next]_vars
LiveSpec == Spec /\ WF_vars(Next)

THEOREM Spec => []TypeOK
-----------------------------------------------------------------------------
C == INSTANCE Consensus WITH chosen <- ledger,
                             Value <- Decree
THEOREM Spec => C!Spec
THEOREM Spec => []C!Inv /\ C!Success
THEOREM LiveSpec => C!LiveSpec
=============================================================================
\* Modification History
\* Last modified Tue Nov 20 21:14:58 AEDT 2018 by armen
\* Created Wed Oct 24 20:58:12 AEDT 2018 by armen
