---------------------------- MODULE Preliminary ----------------------------
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

-----------------------------------------------------------------------------
VARIABLE msgs

TypeOK == msgs \subseteq Message

Cast(m) == msgs' = msgs \cup {m}

null(p)     == [pst |-> p, bal |-> -1, dec |-> Blank]
Votes(b, p) == { m \in msgs : m.type = "Voted" /\ m.pst = p /\ m.bal < b} \cup {null(p)}
MaxVote(V)  == CHOOSE m \in V : \A v \in V : m.bal >= v.bal

MaxLastVote(V) == CHOOSE m \in V : \A v \in V : m.mbal >= v.mbal

CastNextBallot(b) == Cast([type |-> "NextBallot", bal |-> b])

CastLastVote(p) == \E m \in msgs :
                     /\ m.type = "NextBallot"
                     /\ Cast([type |-> "LastVote", pst |-> p, bal |-> m.bal,
                              mbal |-> MaxVote(Votes(m.bal, p)).bal,
                              mdec |-> MaxVote(Votes(m.bal, p)).dec])

CastBeginBallot(b, d) ==
  /\ ~ \E m \in msgs : m.type = "BeginBallot" /\ m.bal = b
  /\ \E Q \in Quorum :
        LET mset == {m \in msgs : /\ m.type = "LastVote"
                                  /\ m.pst \in Q
                                  /\ m.bal = b}
            mdec == MaxLastVote(mset).mdec
            dec  == IF mdec = Blank THEN d ELSE mdec
        IN /\ \A q \in Q : \E m \in mset : m.pst = q
           /\ Cast([type |-> "BeginBallot", bal |-> b, dec |-> dec])

CastVote(p) == \E m \in msgs : /\ m.type = "BeginBallot"
                               /\ Cast([type |-> "Voted", pst |-> p, bal |-> m.bal, dec |-> m.dec])

Init == /\ msgs = {}

Next == \/ \E b \in Ballot : \/ CastNextBallot(b)
                             \/ \E d \in Decree : CastBeginBallot(b, d)
        \/ \E p \in Prist : CastLastVote(p) \/ CastVote(p)

Spec == Init /\ [][Next]_msgs

THEOREM Spec => []TypeOK

=============================================================================
\* Modification History
\* Last modified Wed Nov 07 20:22:35 AEDT 2018 by armen
\* Created Wed Oct 24 20:58:12 AEDT 2018 by armen
