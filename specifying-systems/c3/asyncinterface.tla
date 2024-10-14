---------------------- MODULE asyncinterface ----------------------
EXTENDS Naturals
CONSTANT Data
VARIABLES ready, ack, val

vars == <<ready,ack,val>>

TypeOK ==       /\ val \in Data 
                /\ ack \in {0, 1}
                /\ ready \in {0, 1}

Init ==         /\ TypeOK
                /\ ready = ack

Send ==         /\ ready = ack
                /\ ready' = 1 - ready
                /\ UNCHANGED ack
                /\ val' \in Data

Receive ==      /\ ready # ack
                /\ UNCHANGED ready
                /\ ack' = 1 - ack
                /\ UNCHANGED val

Next ==         \/ Send
                \/ Receive
    
Spec == Init /\ [Next]_vars

--------------------------------------------------------------
THEOREM Spec => TypeOK
==============================================================