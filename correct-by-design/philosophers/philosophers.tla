---------------------- MODULE philosophers ----------------------
EXTENDS Integers
CONSTANTS NrPhilosophers, maxMeals
VARIABLES cutlery, grabCount, eaten

Init == 
    /\ cutlery = [x \in 0..NrPhilosophers-1 |-> -1]
    /\ grabCount = [ x \in 0..NrPhilosophers-1 |-> 0]
    /\ eaten = [ x \in 0..NrPhilosophers-1 |-> 0]

TypeOK ==   /\ NrPhilosophers >= 1
            /\ \A x \in DOMAIN cutlery: cutlery[x] \in {-1} \cup 0..(NrPhilosophers-1)
            /\ \A x \in DOMAIN grabCount: grabCount[x] >= 0
            /\ \A x \in DOMAIN eaten: eaten[x] >= 0

AtMostOneOwner ==
    /\ \A x \in 0..NrPhilosophers-1 : grabCount[x] <= 1

AllHaveEaten == \A x \in DOMAIN cutlery: eaten[x] = maxMeals

first(x) == IF x = 0 THEN x ELSE (NrPhilosophers - 1 + x) % NrPhilosophers

second(x) == IF x = 0 THEN NrPhilosophers-1 ELSE x

available(x) == grabCount[x] = 0     

hasFirst(x) == 
    cutlery[first(x)] = x

hasSecond(x) ==
    cutlery[second(x)] = x

eat(x) ==
    /\ hasFirst(x)
    /\ hasSecond(x)
    /\ cutlery' = [cutlery EXCEPT ![first(x)] = -1, ![second(x)] = -1]
    /\ grabCount' = [grabCount EXCEPT ![first(x)] =@-1, ![second(x)] = @-1]
    /\ eaten' = [eaten EXCEPT ![x] = @+1]

takeFirst(x) ==
    /\ ~hasFirst(x)
    /\ ~hasSecond(x)
    /\ available(first(x))
    /\ cutlery' = [cutlery EXCEPT ![first(x)] = x]
    /\ grabCount' = [grabCount EXCEPT ![first(x)] =@+1]
    /\ UNCHANGED eaten

takeSecond(x) ==
    /\ hasFirst(x)
    /\ ~hasSecond(x)
    /\ available(second(x))
    /\ cutlery' = [cutlery EXCEPT ![second(x)] = x]
    /\ grabCount' = [grabCount EXCEPT ![second(x)] =@+1]
    /\ UNCHANGED eaten

Next == \E x \in 0..(NrPhilosophers-1) :
            /\ eaten[x] < maxMeals
            /\  \/ takeFirst(x)
                \/ takeSecond(x)
                \/ eat(x)

Spec == Init /\ [][Next]_<<cutlery, grabCount, eaten>>
--------------------------------------------------------------
THEOREM Spec => AllHaveEaten
==============================================================
