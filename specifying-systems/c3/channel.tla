---------------------- MODULE channel ----------------------
EXTENDS Naturals
CONSTANT Data
VARIABLES chan

TypeOK ==       chan \in [ready : {0,1}, ack : {0,1}, val : Data]

Init ==         /\ TypeOK
                /\ chan.ready = chan.ack

Send(d) ==      /\ chan.ready = chan.ack
                /\ chan' = [chan EXCEPT !.ready = 1-@, !.val=d]

Receive ==      /\ chan.ready # chan.ack
                /\ chan' = [chan EXCEPT !.ack = 1-@]

Next ==         \/ \E d \in Data: Send(d)
                \/ Receive
    
Spec == Init /\ [Next]_<<chan>>

--------------------------------------------------------------
THEOREM Spec => TypeOK
==============================================================