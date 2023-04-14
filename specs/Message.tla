------------------------------ MODULE Message ------------------------------
EXTENDS FiniteSets, Integers

CONSTANTS Messages  \* The set of unique messages.  They are unique by the hash
                    \* of their contents plus the time of arrival.

VARIABLES Delivered \* The set of delivered messages.
        , Queued    \* The queue of messages ready for delivery.
        , Archived  \* The set of messages succeeded and archived.
        , Failed    \* The set of messages marked as given up.
        , Deleted   \* The set of deleted messages
        , Processing\* The message that is being processed
vars == <<Delivered, Queued, Archived, Failed, Deleted, Processing>>

AllMessages == Queued \cup Archived \cup Failed \cup Deleted \cup Processing
    (***********************************************************************)
    (* This is the set of all messages that are in the system.             *)
    (***********************************************************************)

TypeOK == /\ Delivered \subseteq Messages
          /\ Queued \subseteq Messages
          /\ Archived \subseteq Messages
          /\ Failed \subseteq Messages
          /\ Deleted \subseteq Messages
          /\ Processing \subseteq Messages

Invariants ==
    /\ Delivered \subseteq Archived \cup Failed \cup Deleted \cup Processing
    (***********************************************************************)
    (* Messages we are trying to or have failed to send may or may not have*)
    (* arrived at the destination.                                         *)
    (***********************************************************************)
    /\ \A m \in Queued: m \notin Delivered
    (***********************************************************************)
    (* But if a message is in Ready, it has definitely not arrived.        *)
    (***********************************************************************)
    /\ Archived \subseteq Delivered
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
        /\ Queued' = Queued \cup {m}
        /\ UNCHANGED <<Delivered, Archived, Failed, Deleted, Processing>>

ProcessMessage ==
    (***********************************************************************)
    (* The queue controller marks a message as Processing because it is    *)
    (* processing it now. Processing a message involves shifting it to the *)
    (* Processing status. The queue controller then sends it to the        *)
    (* destination and waits for the response. The Processing status of a  *)
    (* message ends when the response arrives.                             *)
    (***********************************************************************)
    /\ Processing = {}   \* Processes one message at a time.
    /\ \E m \in Queued:
        /\ Queued' = Queued \ {m}
        /\ Processing' = Processing \cup {m}
        /\ UNCHANGED <<Delivered, Archived, Failed, Deleted>>

MessageDeliveredWithSuccess ==
    (***********************************************************************)
    (* Represents an operation where a message arrives at the destination  *)
    (* and the message queue is aware of that.                             *)
    (***********************************************************************)
    /\ \E m \in Processing:
        /\ Processing' = Processing \ {m}
        /\ Archived' = Archived \cup {m}
        /\ Delivered' = Delivered \cup {m}
        /\ UNCHANGED <<Queued, Failed, Deleted>>

MessageDeliveredWithFailure ==
    (***********************************************************************)
    (* A message arrives at the destination, after which the message queue *)
    (* fails.                                                              *)
    (***********************************************************************)
    /\ \E m \in Processing:
        /\ Processing' = Processing \ {m}
        /\ Failed' = Failed \cup {m}
        /\ Delivered' = Delivered \cup {m}
        /\ UNCHANGED <<Queued, Archived, Deleted>>

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
        /\ UNCHANGED <<Delivered, Queued, Archived, Deleted>>

CancelMessage ==
    (***********************************************************************)
    (* Cancels a message in the queue.                                     *)
    (***********************************************************************)
    /\ \E m \in Queued:
        /\ Queued' = Queued \ {m}
        /\ Deleted' = Deleted \cup {m}
        /\ UNCHANGED <<Delivered, Archived, Failed, Processing>>
-----------------------------------------------------------------------------
Init == /\ Delivered = {}
        /\ Queued = {}
        /\ Archived = {}
        /\ Failed = {}
        /\ Deleted = {}
        /\ Processing = {}

Next == \/ ReceiveMessage
        \/ ProcessMessage
        \/ MessageDelivered
        \/ FailMessage
        \/ CancelMessage
        \/ UNCHANGED vars

Spec == Init /\ [][Next]_vars
=============================================================================
\* Modification History
\* Last modified Fri Apr 14 11:29:54 KST 2023 by hcs
\* Created Wed Apr 12 09:43:11 KST 2023 by hcs
