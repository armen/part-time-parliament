----------------------------- MODULE Preliminary ----------------------------
EXTENDS Integers

CONSTANTS Decree, Prist, Quorum

ASSUME /\ \A Q \in Quorum : Q \subseteq Prist
       /\ \A Q1, Q2 \in Quorum : Q1 \cap Q2 # {}

Ballot == Nat

Blank == CHOOSE b : b \notin Decree \* Blank is not a decree

Message ==      [type : {"NextBallot"}, bal : Ballot]
           \cup [type : {"LastVote"}, pst : Prist, bal : Ballot,
                 mbal : Ballot \cup {-1}, mdec : Decree \cup {Blank}]
           \cup [type : {"BeginBallot"}, bal : Ballot, dec : Decree]
           \cup [type : {"Voted"}, pst : Prist, bal : Ballot, dec : Decree]
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
Maximum(S) == CHOOSE i \in S : (\A j \in S : i >= j)
Cast(m)    == msgs' = msgs \cup {m}

MsgsFrom(Q, b, t) == {m \in msgs : m.type = t /\ m.pst \in Q /\ m.bal = b}
-----------------------------------------------------------------------------
CastNextBallot(b) == /\ Cast([type |-> "NextBallot", bal |-> b])
                     /\ UNCHANGED ledger

CastLastVote(p) ==
  \E m \in msgs :
     LET null(pst) == [pst |-> pst, bal |-> -1, dec |-> Blank]
         votes == {v \in msgs : /\ v.type = "Voted"
                                /\ v.pst = p
                                /\ v.bal < m.bal} \cup {null(p)}
         maxBal == Maximum({v.bal : v \in votes})
         maxVote == CHOOSE v \in votes : v.bal = maxBal
     IN /\ m.type = "NextBallot"
        /\ Cast([type |-> "LastVote", pst |-> p, bal |-> m.bal,
                 mbal |-> maxVote.bal, mdec |-> maxVote.dec])
        /\ UNCHANGED ledger

CastBeginBallot(b, d) ==
  /\ ~ \E m \in msgs : m.type = "BeginBallot" /\ m.bal = b
  /\ \E Q \in Quorum :
        LET lVotes == MsgsFrom(Q, b, "LastVote")
            maxBal == Maximum({l.mbal : l \in lVotes})
            mdec   == (CHOOSE l \in lVotes : l.mbal = maxBal).mdec
            dec    == IF mdec = Blank THEN d ELSE mdec
        IN /\ \A q \in Q : \E l \in lVotes : l.pst = q
           /\ Cast([type |-> "BeginBallot", bal |-> b, dec |-> dec])
           /\ UNCHANGED ledger

(***************************************************************************)
(* CastBeginBallot(b, d) ==                                                *)
(*   /\ ~ \E m \in msgs : m.type = "BeginBallot" /\ m.bal = b              *)
(*   /\ \E Q \in Quorum :                                                  *)
(*         LET QLastVote == MsgsFrom(Q, b, "LastVote")                     *)
(*             QLastVoteDec == {m \in QLastVote : m.mbal >= 0}             *)
(*         IN                                                              *)
(*            /\ \A q \in Q : \E m \in QLastVote : m.pst = q               *)
(*            /\ \/ QLastVoteDec = {}                                      *)
(*               \/ \E m \in QLastVoteDec :                                *)
(*                     /\ m.mdec = d                                       *)
(*                     /\ \A mm \in QLastVoteDec : m.mbal >= mm.mbal       *)
(*   /\ Cast([type |-> "BeginBallot", bal |-> b, dec |-> d])               *)
(*   /\ UNCHANGED ledger                                                   *)
(***************************************************************************)

CastVote(p) ==
  \E m \in msgs :
     /\ m.type = "BeginBallot"
     /\ ~ \E l \in msgs : /\ l.type = "LastVote"
                          /\ l.pst = p
                          /\ IF l.bal > l.mbal THEN
                                /\ l.bal > m.bal
                                /\ l.mbal < m.bal
                             ELSE
                                /\ l.mbal > m.bal
                                /\ l.bal < m.bal
     /\ Cast([type |-> "Voted", pst |-> p, bal |-> m.bal, dec |-> m.dec])
     /\ UNCHANGED ledger

CastSuccess(b, d) ==
  \E Q \in Quorum :
     LET votes == MsgsFrom(Q, b, "Voted")
     IN /\ \A q \in Q : (\E v \in votes : v.pst = q /\ v.dec = d)
        /\ ledger' = ledger \cup {d}
        /\ Cast([type |-> "Success", bal |-> b, dec |-> d])

Write == \E m \in msgs : /\ m.type = "Success"
                         /\ ledger' = ledger \cup {m.dec}
                         /\ UNCHANGED msgs

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
\* Last modified Sun Nov 18 22:33:23 AEDT 2018 by armen
\* Created Wed Oct 24 20:58:12 AEDT 2018 by armen
