------------------------------ MODULE Message ------------------------------
(**************************************************************************)
(* Persistent Message Queue Service                                       *)
(* Copyright (C) 2023  Hee Shin                                           *)
(*                                                                        *)
(* This program is free software: you can redistribute it and/or modify   *)
(* it under the terms of the GNU General Public License as published by   *)
(* the Free Software Foundation, either version 3 of the License, or      *)
(* (at your option) any later version.                                    *)
(*                                                                        *)
(* This program is distributed in the hope that it will be useful,        *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of         *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the          *)
(* GNU General Public License for more details.                           *)
(*                                                                        *)
(* You should have received a copy of the GNU General Public License      *)
(* along with this program.  If not, see <https://www.gnu.org/licenses/>. *)
(**************************************************************************)
EXTENDS FiniteSets, Integers

CONSTANTS Messages  \* The set of unique messages.  They are unique by the hash
                    \* of their contents plus the time of arrival.

VARIABLES Delivered,    \* The set of delivered messages.
          Queued,       \* The queue of messages ready for delivery.
          Archived,     \* The set of messages succeeded and archived.
          Abandoned,    \* The set of messages marked as given up.
          Cancelled,    \* The set of cancelled messages
          Processing    \* The message that is being processed
vars == <<Delivered, Queued, Archived, Abandoned, Cancelled, Processing>>

AllMessages == Queued \cup Archived \cup Abandoned \cup Cancelled \cup Processing
    (***********************************************************************)
    (* This is the set of all messages that are in the system.             *)
    (***********************************************************************)

TypeOK == /\ Delivered \subseteq Messages
          /\ Queued \subseteq Messages
          /\ Archived \subseteq Messages
          /\ Abandoned \subseteq Messages
          /\ Cancelled \subseteq Messages
          /\ Processing \subseteq Messages

Invariants ==
    /\ Delivered \subseteq AllMessages
    (***********************************************************************)
    (* Messages we are trying to or have failed to send may or may not have*)
    (* arrived at the destination.                                         *)
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
        /\ UNCHANGED <<Delivered, Archived, Abandoned, Cancelled, Processing>>

ProcessMessage ==
    (***********************************************************************)
    (* The queue controller marks a message as Processing because it is    *)
    (* processing it now. Processing a message involves shifting it to the *)
    (* Processing status. The queue controller then sends it to the        *)
    (* destination and waits for the response. The Processing status of a  *)
    (* message ends when the response arrives, or the queue controller     *)
    (* times out the message.                                              *)
    (***********************************************************************)
    /\ Processing = {}   \* Processes one message at a time.
    /\ \E m \in Queued:
        /\ Queued' = Queued \ {m}
        /\ Processing' = Processing \cup {m}
        /\ UNCHANGED <<Delivered, Archived, Abandoned, Cancelled>>

DeliverMessage ==
    (***********************************************************************)
    (* Delivery of the message was successful.                             *)
    (***********************************************************************)
    /\ \E m \in Processing:
        /\ Processing' = Processing \ {m}
        /\ Archived' = Archived \cup {m}
        /\ Delivered' = Delivered \cup {m}
    /\ UNCHANGED <<Queued, Abandoned, Cancelled>>

FailSendingMessage ==
    (***********************************************************************)
    (* Failed to send the message.                                         *)
    (***********************************************************************)
    /\ \E m \in Processing:
        /\ Processing' = Processing \ {m}
        /\ Queued' = Queued \cup {m}
    /\ UNCHANGED <<Delivered, Abandoned, Archived, Cancelled>>

FailReceivingResponse ==
    (***********************************************************************)
    (* A message arrives at the destination, but the response doesn't      *)
    (* arrive.                                                             *)
    (***********************************************************************)
    /\ \E m \in Processing:
        /\ Processing' = Processing \ {m}
        /\ Queued' = Queued \cup {m}
        /\ Delivered' = Delivered \cup {m}
    /\ UNCHANGED <<Archived, Abandoned, Cancelled>>

GiveUpMessage ==
    (***********************************************************************)
    (* The queue controller gives up on the message because it keeps on    *)
    (* failing.                                                            *)
    (***********************************************************************)
    /\ \E m \in Processing:
        /\ Processing' = Processing \ {m}
        /\ Abandoned' = Abandoned \cup {m}
    /\ UNCHANGED <<Delivered, Queued, Archived, Cancelled>>

FailMessage ==
    (***********************************************************************)
    (* The attempt to send the queued message failed. There will be a few  *)
    (* cases to cover. If the message keeps failing, the queue controller  *)
    (* shifts its status to Abandoned. Abandoned messages usually need     *)
    (* manual inspection of engineers.                                     *)
    (***********************************************************************)
    \/ FailSendingMessage
    \/ FailReceivingResponse
    \/ GiveUpMessage

CancelMessage ==
    (***********************************************************************)
    (* Cancels a message in the queue.                                     *)
    (***********************************************************************)
    /\ \E m \in Queued:
        /\ Queued' = Queued \ {m}
        /\ Cancelled' = Cancelled \cup {m}
        /\ UNCHANGED <<Delivered, Archived, Abandoned, Processing>>
-----------------------------------------------------------------------------
Init == /\ Delivered = {}
        /\ Queued = {}
        /\ Archived = {}
        /\ Abandoned = {}
        /\ Cancelled = {}
        /\ Processing = {}

Next == \/ ReceiveMessage
        \/ ProcessMessage
        \/ DeliverMessage
        \/ FailMessage
        \/ CancelMessage
        \/ UNCHANGED vars

Spec == Init /\ [][Next]_vars
=============================================================================
\* Modification History
\* Last modified Wed May 10 13:26:17 KST 2023 by hcs
\* Created Wed Apr 12 09:43:11 KST 2023 by hcs
