----------------------------- MODULE Processing -----------------------------
CONSTANT
    Messages    \* Messages pushed in the queue.

VARIABLE
    Channel,    \* Channel for tasks to communicate with each other.
    Queue,      \* Message queue
    Complete    \* Place for messages that have completed processing.
vars == <<Channel, Queue, Complete>>

TypeOK ==
    /\ Channel \in {"PROCESS", "WAIT"}
    /\ Queue \subseteq Messages
    /\ Complete \subseteq Messages

Invariants ==
    (***********************************************************************)
    (* If the queue is not empty, the channel must be in the PROCESS state.*)
    (***********************************************************************)
    /\ Queue /= {} => Channel = "PROCESS"
    (***********************************************************************)
    (* If the queue is empty, the channel will eventually be in the WAIT   *)
    (* state.                                                              *)
    (***********************************************************************)
    \* /\ Queue = {} => []<>(Channel = "WAIT")

PushMessage ==
    (***********************************************************************)
    (* Push a message into the queue.                                      *)
    (***********************************************************************)
    \E m \in Messages \ (Queue \cup Complete):
        /\ Queue' = Queue \cup {m}
        /\ UNCHANGED <<Channel, Complete>>

ProcessMessage ==
    (***********************************************************************)
    (* Process a message from the queue.                                   *)
    (***********************************************************************)
    /\ Channel = "PROCESS"
    /\ Queue /= {}
    /\ \E m \in Queue:
        /\ Queue' = Queue \ {m}
        /\ Complete' = Complete \cup {m}
    /\ UNCHANGED <<Channel>>

NotifyForProcessing ==
    (***********************************************************************)
    (* Notify the channel that there are messages to process.              *)
    (***********************************************************************)
    /\ Channel = "WAIT"
    /\ Queue /= {}
    /\ Channel' = "PROCESS"
    /\ UNCHANGED <<Queue, Complete>>

WaitForMessage ==
    (***********************************************************************)
    (* Represents that the message processors must wait for a message.     *)
    (***********************************************************************)
    /\ Queue = {}
    /\ Channel' = "WAIT"
    /\ UNCHANGED <<Queue, Complete>>

Init ==
    /\ Channel = "PROCESS"
    /\ Queue \in SUBSET(Messages)
    /\ Complete = {}

Next ==
    \/ PushMessage
    \/ ProcessMessage
    \/ NotifyForProcessing
    \/ WaitForMessage

FullyProcessed ==
    (***********************************************************************)
    (* Represents the state where all messages have completed processing.  *)
    (***********************************************************************)
    /\ Queue = {}
    /\ Channel = "WAIT"
    /\ Complete = Messages

Spec == Init /\ [][Next]_vars /\ []<>FullyProcessed
=============================================================================
\* Modification History
\* Last modified Tue Apr 18 12:19:12 KST 2023 by hcs
\* Created Mon Apr 17 22:38:51 KST 2023 by hcs
