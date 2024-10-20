---------------MODULE leaderelection-----------------
EXTENDS Integers, Sequences, FiniteSets, Naturals
CONSTANTS NrNodes, MaxTerms, MaxReboots
VARIABLES nodes, messages, leaderHistory, reboots

ValidStates == {
    "CANDIDATE", 
    "FOLLOWER", 
    "LEADER"
}

NodeIds == 1..NrNodes

ValidMessageTypes == {
    "AppendEntriesRequest", 
    "AppendEntriesResponse", 
    "RequestVoteRequest", 
    "RequestVoteResponse"
}

Init == 
    /\ nodes = [x \in 1..NrNodes |-> [ term |-> 0, state |-> "FOLLOWER", votedFor |-> -1, id |-> x, receivedVotes |-> {}] ]
    /\ messages = {}
    /\ leaderHistory = {}
    /\ reboots = 0

AppendEntriesRequestOK(msg) ==
    /\ msg.type = "AppendEntriesRequest"
    /\ msg.term <= MaxTerms
    /\ msg.leaderId \in NodeIds

AppendEntriesResponseOK(msg) ==
    /\ msg.type = "AppendEntriesResponse"
    /\ msg.term <= MaxTerms

RequestVoteRequestOK(msg) ==
    /\ msg.type = "RequestVoteRequest"
    /\ msg.term <= MaxTerms
    /\ msg.candidateId \in NodeIds

RequestVoteResponseOK(msg) ==
    /\ msg.type = "RequestVoteResponse"
    /\ msg.term <= MaxTerms
    /\ msg.voteGranted \in {"FALSE", "TRUE"}

NodeOK ==
    \A id \in NodeIds : 
        /\ nodes[id].term <= MaxTerms
        /\ nodes[id].state \in ValidStates
        /\ nodes[id].votedFor \in NodeIds \cup {-1}
        /\ \A vote \in nodes[id].receivedVotes: vote \in NodeIds

MessageOK ==
    \A msg \in messages :
        /\ msg.type \in ValidMessageTypes
        /\ msg.from \in NodeIds
        /\ msg.to \in NodeIds
        /\ \/ AppendEntriesRequestOK(msg)
           \/ AppendEntriesResponseOK(msg)
           \/ RequestVoteRequestOK(msg)
           \/ RequestVoteResponseOK(msg)

LeaderHistoryOk ==
    \A entry \in leaderHistory:
        /\ entry.term <= MaxTerms
        /\ entry.nodeId \in NodeIds

TypeOK ==
    /\ NodeOK
    /\ MessageOK
    /\ LeaderHistoryOk

ElectionSafety ==
    /\ \A entry, otherEntry \in leaderHistory: entry.nodeId # otherEntry.nodeId => entry.term # otherEntry.term

Reboot(n) ==
    /\ reboots < MaxReboots
    /\ nodes' = [nodes EXCEPT ![n] = [term |-> 0, votedFor |-> -1, state |-> "FOLLOWER", id |-> n, receivedVotes |-> {}]]
    /\ UNCHANGED <<messages, leaderHistory>>
    /\ reboots' = reboots + 1

BecomeFollower(n, term, votedFor) ==
    /\ nodes' = [nodes EXCEPT ![n] = [nodes[n] EXCEPT !.term = term, !.state ="FOLLOWER", !.votedFor=votedFor, !.receivedVotes={}]]
    /\ UNCHANGED <<messages, leaderHistory, reboots>>

BecomeCandidate(n) ==
        /\ nodes[n].state \in {"CANDIDATE", "FOLLOWER"} 
        /\ nodes[n].term < MaxTerms
        /\ nodes' = [nodes EXCEPT ![n] = [term |-> nodes[n].term + 1, votedFor |-> n, state |-> "CANDIDATE", id |-> n, receivedVotes |-> {n}]]
        /\ UNCHANGED <<messages, leaderHistory, reboots>>    

HandleAppendEntriesRequest(msg) ==
    /\ msg.type = "AppendEntriesRequest"
    /\ UNCHANGED <<reboots>>
    /\
        \* Reject due to having larger term
        \/  /\  msg.term < nodes[msg.to].term
            /\ UNCHANGED <<nodes, leaderHistory>>
            /\ messages' = messages \cup {[type|-> "AppendEntriesResponse", from |-> msg.to, to|-> msg.from, term|-> nodes[msg.to].term]}

        \*  Become follower again
        \/  /\ msg.term > nodes[msg.to].term
            /\ BecomeFollower(msg.to, msg.term, -1)
            /\ messages' = messages \cup {[type|-> "AppendEntriesResponse", from|-> msg.to, to|-> msg.from, term|-> msg.term]}
        \* Do nothing, leader won election so we respect
        \/  /\  msg.term = nodes[msg.to].term
            /\  UNCHANGED <<nodes, leaderHistory>>
            /\  messages' = messages \cup {[type|-> "AppendEntriesResponse", from|-> msg.to, to|-> msg.from, term|-> nodes[msg.to].term]}

HandleAppendEntriesResponse(msg) ==
    /\ msg.type = "AppendEntriesResponse"
    /\ UNCHANGED <<reboots>>
    /\
        \* Do nothing for now, no logs involved
        \/  /\  msg.term <= nodes[msg.to].term
            /\ UNCHANGED <<messages, nodes, leaderHistory>>

        \*  Become follower again
        \/  /\ msg.term > nodes[msg.to].term
            /\ BecomeFollower(msg.to, msg.term, -1)
            /\ UNCHANGED <<messages, leaderHistory>>


HandleRequestVoteRequest(msg) ==
    /\  msg.type = "RequestVoteRequest"
    /\ UNCHANGED <<reboots>>
    /\
        \* Ignore since we are on higher term
        \/  /\  msg.term < nodes[msg.to].term
            /\  messages' = messages \cup {[type |-> "RequestVoteResponse", to |-> msg.from, from |-> msg.to, voteGranted |-> "FALSE", term |-> nodes[msg.to].term]}
            /\  UNCHANGED <<nodes, leaderHistory>>

        \*  Become follower again
        \/  /\ msg.term > nodes[msg.to].term
            /\ BecomeFollower(msg.to, msg.term, msg.from)
            /\ messages' = messages \cup {[type |-> "RequestVoteResponse", to |-> msg.from, from |-> msg.to, voteGranted |-> "TRUE", term |-> msg.term]}
            /\ UNCHANGED <<leaderHistory>>

        \* Grant voted if hasnt voted yet
        \/  
            /\ msg.term = nodes[msg.to].term
            /\ nodes' = [nodes EXCEPT ![msg.to] = [nodes[msg.to] EXCEPT !.votedFor = IF nodes[msg.to].votedFor = -1 THEN msg.from ELSE nodes[msg.to].votedFor]]
            /\ messages' = messages \cup {[type |-> "RequestVoteResponse", to |-> msg.from, from |-> msg.to, voteGranted |-> IF nodes[msg.to].votedFor = -1 THEN "TRUE" ELSE "FALSE", term |-> msg.term]}
            /\ UNCHANGED <<leaderHistory>>

HandleRequestVoteResponse(msg) ==
    /\  msg.type = "RequestVoteResponse"
    /\ UNCHANGED <<reboots>>
    /\ 
        \/ /\ msg.term > nodes[msg.to].term
           /\ BecomeFollower(msg.to, msg.term, -1)
           /\ UNCHANGED <<messages>>

        \/ /\ msg.term < nodes[msg.to].term
           /\ UNCHANGED <<nodes, messages, leaderHistory>>

        \/ /\ msg.term = nodes[msg.to].term
           /\ nodes' = [nodes EXCEPT ![msg.to] = [nodes[msg.to] EXCEPT !.receivedVotes = IF msg.voteGranted = "TRUE" THEN nodes[msg.to].receivedVotes \cup {msg.from} ELSE nodes[msg.to].receivedVotes]]
           /\ UNCHANGED <<messages, leaderHistory>>

RequestVotes(candidate, otherNode) ==
    /\ nodes[candidate].state = "CANDIDATE"
    /\ messages' = messages \cup {[from |-> candidate, to |-> otherNode, type |-> "RequestVoteRequest", term |-> nodes[candidate].term, candidateId |-> nodes[candidate].id]}
    /\ UNCHANGED <<nodes, leaderHistory, reboots>>


BecomeLeader(n) ==
    /\ nodes[n].state = "CANDIDATE"
    /\ Cardinality(nodes[n].receivedVotes) > NrNodes \div 2
    /\ nodes' = [nodes EXCEPT ![n].state = "LEADER"]
    /\ leaderHistory' = leaderHistory \cup {[nodeId |-> nodes[n].id, term |-> nodes[n].term ]}
    /\ UNCHANGED <<messages, reboots>>

AppendEntries(leader, otherNode) ==
    /\ nodes[leader].state = "LEADER"
    /\ messages' = messages \cup {[type |-> "AppendEntriesRequest", from|-> leader, to|->otherNode, term|-> nodes[leader].term, leaderId |-> leader]}
    /\ UNCHANGED <<nodes, leaderHistory, reboots>>

\* Dropping and duplicating messages is implicitly happening
\* We pick a message at random, which allows for one to never be received
\* And at the same time, we allow for the same to be picked up 
\* more than once
Next == 
    \/  \E node \in NodeIds : Reboot(node)
    \/  \E node \in NodeIds : BecomeCandidate(node)
    \/  \E msg \in messages :
        \/  HandleAppendEntriesRequest(msg)
        \/  HandleAppendEntriesResponse(msg)
        \/  HandleRequestVoteRequest(msg)
        \/  HandleRequestVoteResponse(msg)
    \/  \E candidate, otherNode \in NodeIds: RequestVotes(candidate, otherNode)
    \/  \E leader, otherNode \in NodeIds: AppendEntries(leader, otherNode)
    \/  \E node \in NodeIds: BecomeLeader(node)

Spec == Init /\ [][Next]_<<nodes,messages,leaderHistory>>
--------------------------------------------------------------
==============================================================