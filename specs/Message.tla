------------------------------ MODULE Message ------------------------------
EXTENDS FiniteSets, Integers

CONSTANTS Payloads   \* Represents the set of message payloads.
        , IDs        \* The set of unique identifiers.

VARIABLES Arrived   \* The set of messages that arrived at destination
        , Ready     \* The queue of messages ready for process
        , Success   \* The set of messages marked successful
        , Failed    \* The set of messages marked as failed
        , Deleted   \* The set of deleted messages
        , Processing\* The queue of messages being processed
vars == <<Arrived, Ready, Success, Failed, Deleted, Processing>>

Messages == IDs \X Payloads

AllMessages == Ready \cup Success \cup Failed \cup Deleted \cup Processing
    (***********************************************************************)
    (* This is the set of all messages that are in the system.             *)
    (***********************************************************************)

TypeOK == /\ Arrived \subseteq Messages
          /\ Ready \subseteq Messages
          /\ Success \subseteq Messages
          /\ Failed \subseteq Messages
          /\ Deleted \subseteq Messages
          /\ Processing \subseteq Messages

GetIDs(messages) == {m[1] : m \in messages}
    (***********************************************************************)
    (* Returns the set of IDs from a set of messages.                      *)
    (***********************************************************************)

GetPayloads(messages) == {m[2] : m \in messages}
    (***********************************************************************)
    (* Returns the set of payloads from a set of messages.                 *)
    (***********************************************************************)

Invariants ==
    /\ Arrived \subseteq Success \cup Failed \cup Deleted \cup Processing
    \* Messages we are trying to or have failed to send may or may not have
    \* arrived at the destination.
    /\ \A m \in Ready: m \notin Arrived
    \* But if a message is in Ready, it has definitely not arrived.
    /\ Success \subseteq Arrived
    \* Every successful messages will have arrived at the destination.
    /\ Cardinality(GetIDs(AllMessages)) = Cardinality(AllMessages)
    \* We do not give a message an ID that is in use.
-----------------------------------------------------------------------------
ReceiveMessage ==
    (***********************************************************************)
    (* Receives an incoming message and pushes it into the message queue.  *)
    (***********************************************************************)
    /\ \E m \in Messages:
        /\ m[1] \notin GetIDs(AllMessages)
        /\ Ready' = Ready \cup {m}
        /\ UNCHANGED <<Arrived, Success, Failed, Deleted, Processing>>

ProcessMessage ==
    (***********************************************************************)
    (* Processes a message from the queue and marks it as successful.      *)
    (***********************************************************************)
    /\ \E m \in Ready:
        /\ Ready' = Ready \ {m}
        /\ Processing' = Processing \cup {m}
        /\ UNCHANGED <<Arrived, Success, Failed, Deleted>>

ArriveSuccessfulMessage ==
    (***********************************************************************)
    (* Represents an operation where a message arrives at the destination  *)
    (* and the message queue is aware of that.                             *)
    (***********************************************************************)
    /\ \E m \in Processing:
        /\ Processing' = Processing \ {m}
        /\ Success' = Success \cup {m}
        /\ Arrived' = Arrived \cup {m}
        /\ UNCHANGED <<Ready, Failed, Deleted>>

ArriveFailedMessage ==
    (***********************************************************************)
    (* A message arrives at the destination, after which the message queue *)
    (* fails.                                                              *)
    (***********************************************************************)
    /\ \E m \in Processing:
        /\ Processing' = Processing \ {m}
        /\ Failed' = Failed \cup {m}
        /\ Arrived' = Arrived \cup {m}
        /\ UNCHANGED <<Ready, Success, Deleted>>

ArriveMessage ==
    (***********************************************************************)
    (* Represents an operation where a message arrives at the destination, *)
    (* but the message queue may or may not be aware of that.              *)
    (***********************************************************************)
    \/ ArriveSuccessfulMessage
    \/ ArriveFailedMessage

FailMessage ==
    (***********************************************************************)
    (* The attempt to send the message failed and the message did not reach*)
    (* the destination.                                                    *)
    (***********************************************************************)
    /\ \E m \in Processing:
        /\ Processing' = Processing \ {m}
        /\ Failed' = Failed \cup {m}
        /\ UNCHANGED <<Arrived, Ready, Success, Deleted>>

DeleteMessage ==
    (***********************************************************************)
    (* Deletes a message from the queue.                                   *)
    (***********************************************************************)
    /\ \E m \in Ready \cup Failed \cup Processing:
        /\ Ready' = Ready \ {m}
        /\ Failed' = Failed \ {m}
        /\ Processing' = Processing \ {m}
        /\ Deleted' = Deleted \cup {m}
        /\ UNCHANGED <<Arrived, Success>>
-----------------------------------------------------------------------------
Init == /\ Arrived = {}
        /\ Ready = {}
        /\ Success = {}
        /\ Failed = {}
        /\ Deleted = {}
        /\ Processing = {}

Next == \/ ReceiveMessage
        \/ ProcessMessage
        \/ ArriveMessage
        \/ FailMessage
        \/ DeleteMessage
        \/ UNCHANGED vars

Spec == Init /\ [][Next]_vars
=============================================================================
\* Modification History
\* Last modified Wed Apr 12 18:53:10 KST 2023 by hcs
\* Created Wed Apr 12 09:43:11 KST 2023 by hcs
