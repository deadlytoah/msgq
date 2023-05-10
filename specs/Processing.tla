----------------------------- MODULE Processing -----------------------------
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
(***************************************************************************)
(* The specification describes two asynchronous tasks working together.    *)
(* The first task is a message queue that accepts messages and pushes them *)
(* into a queue. The second task is a message processor that processes the *)
(* messages in the queue. The message processor must wait for a message    *)
(* in the queue before it can process it.                                  *)
(*                                                                         *)
(* The specification shows the operations in WaitForMessage must be atomic.*)
(* WaitForMessage first checks if the queue is empty in the database. If   *)
(* the queue is empty, it shifts the message processor into WAIT status.   *)
(***************************************************************************)

CONSTANT
    Messages    \* Messages pushed in the queue.

VARIABLE
    Channel,    \* Channel for tasks to communicate with each other.
    Queue,      \* Message queue sits in the DBMS.
    Complete,   \* Place for messages that have completed processing.
    DoNotify    \* Flag to indicate that a notification should be sent.
vars == <<Channel, Queue, Complete, DoNotify>>

TypeOK ==
    /\ Channel \in {"PROCESS", "WAIT"}
    /\ Queue \subseteq Messages
    /\ Complete \subseteq Messages
    /\ DoNotify \in BOOLEAN

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
    /\ DoNotify = FALSE     \* Not reentrant
    /\ \E m \in Messages \ (Queue \cup Complete):
        /\ DoNotify' = TRUE
        /\ Queue' = Queue \cup {m}
        /\ UNCHANGED <<Channel, Complete>>

NotifyForProcessing ==
    (***********************************************************************)
    (* Notify the channel that there are messages to process.              *)
    (***********************************************************************)
    /\ DoNotify = TRUE
    /\ Channel' = "PROCESS"
    /\ DoNotify' = FALSE
    /\ UNCHANGED <<Queue, Complete>>

ProcessMessage ==
    (***********************************************************************)
    (* Process a message from the queue.                                   *)
    (***********************************************************************)
    /\ Channel = "PROCESS"
    /\ \E m \in Queue:
        /\ Queue' = Queue \ {m}
        /\ Complete' = Complete \cup {m}
    /\ UNCHANGED <<Channel, DoNotify>>

WaitForMessage ==
    (***********************************************************************)
    (* Represents that the message processors must wait for a message.     *)
    (***********************************************************************)
    /\ Queue = {}
    /\ Channel' = "WAIT"
    /\ UNCHANGED <<Queue, Complete, DoNotify>>

MessageQueueNext == PushMessage \/ NotifyForProcessing
MessageProcessorNext == ProcessMessage \/ WaitForMessage

Init ==
    /\ Channel = "PROCESS"
    /\ Queue \in SUBSET(Messages)
    /\ Complete = {}
    /\ DoNotify = FALSE

Next ==
    \/ MessageQueueNext
    \/ MessageProcessorNext

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
\* Last modified Wed Apr 19 00:01:55 KST 2023 by hcs
\* Created Mon Apr 17 22:38:51 KST 2023 by hcs
