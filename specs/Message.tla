------------------------------ MODULE Message ------------------------------
EXTENDS FiniteSets, Integers

CONSTANTS Messages  \* The set of unique messages.  They are unique by the hash
                    \* of their contents plus the time of arrival.

VARIABLES Delivered \* The set of delivered messages.
        , Ready     \* The queue of messages ready for process
        , Success   \* The set of messages marked successful
        , Failed    \* The set of messages marked as failed
        , Deleted   \* The set of deleted messages
        , Processing\* The message that is being processed
vars == <<Delivered, Ready, Success, Failed, Deleted, Processing>>

AllMessages == Ready \cup Success \cup Failed \cup Deleted \cup Processing
    (***********************************************************************)
    (* This is the set of all messages that are in the system.             *)
    (***********************************************************************)

TypeOK == /\ Delivered \subseteq Messages
          /\ Ready \subseteq Messages
          /\ Success \subseteq Messages
          /\ Failed \subseteq Messages
          /\ Deleted \subseteq Messages
          /\ Processing \subseteq Messages

Invariants ==
    /\ Delivered \subseteq Success \cup Failed \cup Deleted \cup Processing
    (***********************************************************************)
    (* Messages we are trying to or have failed to send may or may not have*)
    (* arrived at the destination.                                         *)
    (***********************************************************************)
    /\ \A m \in Ready: m \notin Delivered
    (***********************************************************************)
    (* But if a message is in Ready, it has definitely not arrived.        *)
    (***********************************************************************)
    /\ Success \subseteq Delivered
    (***********************************************************************)
    (* Every successful messages will have arrived at the destination.     *)
    (***********************************************************************)
    /\ Cardinality(Processing) <= 1
    (***********************************************************************)
    (* Processes one message at a time.                                    *)
    (***********************************************************************)
-----------------------------------------------------------------------------
ReceiveMessage ==
    (***********************************************************************)
    (* Receives an incoming message and pushes it into the message queue.  *)
    (***********************************************************************)
    /\ \E m \in Messages:
        /\ m \notin AllMessages
        /\ Ready' = Ready \cup {m}
        /\ UNCHANGED <<Delivered, Success, Failed, Deleted, Processing>>

ProcessMessage ==
    (***********************************************************************)
    (* Processes a message from the queue and marks it as successful.      *)
    (***********************************************************************)
    /\ Processing = {}   \* Processes one message at a time.
    /\ \E m \in Ready:
        /\ Ready' = Ready \ {m}
        /\ Processing' = Processing \cup {m}
        /\ UNCHANGED <<Delivered, Success, Failed, Deleted>>

MessageDeliveredWithSuccess ==
    (***********************************************************************)
    (* Represents an operation where a message arrives at the destination  *)
    (* and the message queue is aware of that.                             *)
    (***********************************************************************)
    /\ \E m \in Processing:
        /\ Processing' = Processing \ {m}
        /\ Success' = Success \cup {m}
        /\ Delivered' = Delivered \cup {m}
        /\ UNCHANGED <<Ready, Failed, Deleted>>

MessageDeliveredWithFailure ==
    (***********************************************************************)
    (* A message arrives at the destination, after which the message queue *)
    (* fails.                                                              *)
    (***********************************************************************)
    /\ \E m \in Processing:
        /\ Processing' = Processing \ {m}
        /\ Failed' = Failed \cup {m}
        /\ Delivered' = Delivered \cup {m}
        /\ UNCHANGED <<Ready, Success, Deleted>>

MessageDelivered ==
    (***********************************************************************)
    (* Represents an operation where a message arrives at the destination, *)
    (* but the message queue may or may not be aware of that.              *)
    (***********************************************************************)
    \/ MessageDeliveredWithSuccess
    \/ MessageDeliveredWithFailure

FailMessage ==
    (***********************************************************************)
    (* The attempt to send the message failed and the message did not reach*)
    (* the destination.                                                    *)
    (***********************************************************************)
    /\ \E m \in Processing:
        /\ Processing' = Processing \ {m}
        /\ Failed' = Failed \cup {m}
        /\ UNCHANGED <<Delivered, Ready, Success, Deleted>>

DeleteMessage ==
    (***********************************************************************)
    (* Deletes a message from the queue.                                   *)
    (***********************************************************************)
    /\ \E m \in Ready \cup Failed \cup Processing:
        /\ Ready' = Ready \ {m}
        /\ Failed' = Failed \ {m}
        /\ Processing' = Processing \ {m}
        /\ Deleted' = Deleted \cup {m}
        /\ UNCHANGED <<Delivered, Success>>
-----------------------------------------------------------------------------
Init == /\ Delivered = {}
        /\ Ready = {}
        /\ Success = {}
        /\ Failed = {}
        /\ Deleted = {}
        /\ Processing = {}

Next == \/ ReceiveMessage
        \/ ProcessMessage
        \/ MessageDelivered
        \/ FailMessage
        \/ DeleteMessage
        \/ UNCHANGED vars

Spec == Init /\ [][Next]_vars
=============================================================================
\* Modification History
\* Last modified Fri Apr 14 11:14:06 KST 2023 by hcs
\* Created Wed Apr 12 09:43:11 KST 2023 by hcs
