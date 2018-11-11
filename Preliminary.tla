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

Cast(m) == msgs' = msgs \cup {m}

CastNextBallot(b) == /\ Cast([type |-> "NextBallot", bal |-> b])
                     /\ UNCHANGED ledger

CastLastVote(p) ==
  \E m \in msgs :
     LET null(pst) == [pst |-> pst, bal |-> -1, dec |-> Blank]
         votes == {v \in msgs : /\ v.type = "Voted"
                                /\ v.pst = p
                                /\ v.bal < m.bal} \cup {null(p)}
         maxVote(V) == CHOOSE v1 \in V : \A v2 \in V : v1.bal >= v2.bal
         mVote == maxVote(votes)
     IN /\ m.type = "NextBallot"
        /\ Cast([type |-> "LastVote", pst |-> p, bal |-> m.bal,
                 mbal |-> mVote.bal, mdec |-> mVote.dec])
        /\ UNCHANGED ledger

CastBeginBallot(b, d) ==
  /\ ~ \E m \in msgs : m.type = "BeginBallot" /\ m.bal = b
  /\ \E Q \in Quorum :
        LET QLastVote == {m \in msgs : /\ m.type = "LastVote"
                                       /\ m.pst \in Q
                                       /\ m.bal = b}
            QLastVoteDec == {m \in QLastVote : m.mbal >= 0}
        IN  /\ \A q \in Q : \E m \in QLastVote : m.pst = q
            /\ \/ QLastVoteDec = {}
               \/ \E m \in QLastVoteDec :
                     /\ m.mdec = d
                     /\ \A mm \in QLastVoteDec : m.mbal >= mm.mbal
  /\ Cast([type |-> "BeginBallot", bal |-> b, dec |-> d])
  /\ UNCHANGED ledger

(***************************************************************************)
(* CastBeginBallot(b, d) ==                                                *)
(*   /\ ~ \E m \in msgs : m.type = "BeginBallot" /\ m.bal = b              *)
(*   /\ \E Q \in Quorum :                                                  *)
(*         LET mset == {m \in msgs : /\ m.type = "LastVote"                *)
(*                                   /\ m.pst \in Q                        *)
(*                                   /\ m.bal = b}                         *)
(*             maxLastVote(V) ==                                           *)
(*               CHOOSE m \in V : \A v \in V : m.mbal >= v.mbal            *)
(*             mdec == maxLastVote(mset).mdec                              *)
(*             dec == IF mdec = Blank THEN d ELSE mdec                     *)
(*         IN /\ \A q \in Q : \E m \in mset : m.pst = q                    *)
(*            /\ Cast([type |-> "BeginBallot", bal |-> b, dec |-> dec])    *)
(*            /\ UNCHANGED ledger                                          *)
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
     LET votes == {m \in msgs : /\ m.type = "Voted"
                                /\ m.pst \in Q
                                /\ m.bal = b}
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

THEOREM Spec => []TypeOK

=============================================================================
\* Modification History
\* Last modified Sun Nov 11 14:18:03 AEDT 2018 by armen
\* Created Wed Oct 24 20:58:12 AEDT 2018 by armen
