---------------------- MODULE innerfifo ---------------------------
EXTENDS Naturals, Sequences
VARIABLES in, out, q
CONSTANT Message, MaxSize
ASSUME MaxSize \in Nat /\ MaxSize > 0
InChan == INSTANCE channel WITH Data <- Message, chan <- in
OutChan == INSTANCE channel WITH Data <- Message, chan <- out
--------------------------------------------------------------
Init ==             /\ InChan!Init
                    /\ OutChan!Init
                    /\ q = << >> 
 
TypeOK ==           /\ InChan!TypeOK
                    /\ OutChan!TypeOK
                    /\ q \in Seq(Message)

SSend(msg) ==       /\ InChan!Send(msg)
                    /\ UNCHANGED <<q, out>>
    
BufSend ==          /\ q # <<>>
                    /\ OutChan!Send(Head(q))
                    /\ q' = Tail(q)
                    /\ UNCHANGED in
    
BufRcv ==           /\ Len(q) < MaxSize
                    /\ InChan!Receive
                    /\ q' = Append(q, in.val)
                    /\ UNCHANGED out

RRcv ==             /\ OutChan!Receive
                    /\ UNCHANGED <<q, in>>


Next ==             \/ \E msg \in Message : SSend(msg)
                    \/ BufRcv
                    \/ BufSend
                    \/ RRcv

Spec ==             Init /\ [][Next]_<<in, out, q>>
--------------------------------------------------------------
THEOREM Spec => TypeOK
==============================================================