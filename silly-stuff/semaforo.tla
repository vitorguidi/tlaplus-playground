---------------MODULE semaforo-----------------
EXTENDS Integers
VARIABLE cor

Init == cor \in {"red","yellow","green"}
Next == \/  /\ cor = "red"
            /\ cor' = "green"
        
        \/  /\ cor = "green"
            /\ cor' = "yellow"

        \/  /\ cor = "yellow"
            /\ cor' = "red"

TypeOK == cor \in {"red","yellow","green"}

Spec == Init /\ [][Next]_<<cor>>
-----------------------------------------------
THEOREM Spec => TypeOK /\ []<>(cor = "red") /\ []<>(cor = "yellow") /\ []<>(cor = "green")
===============================================