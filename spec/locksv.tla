------------------------------ MODULE locksv ------------------------------

EXTENDS Naturals, Sequences, TLC, FiniteSets

CONSTANT Clients, Server


(* PlusCal options (-label) *)

(*-- //algorithm locksv {
  variables network = [id \in NodeSet |-> <<>>]; hasLock = [id \in NodeSet |-> FALSE];
  define{
    ServerID == 0
    ServerSet == {ServerID}
    ClientSet == (1) .. (NumClients)
    NodeSet == (ServerSet) \union (ClientSet)
    LockMsg == 1
    UnlockMsg == 2
    GrantMsg == 3
  }
  
  fair process (Server \in ServerSet)
    variables msg = [from |-> ServerID, type |-> LockMsg]; queue = <<>>;
  {
    serverReceive:
        await (Len((network)[self])) > (0);
        msg := Head((network)[self]);
        network := [network EXCEPT ![self] = Tail((network)[self])];
    serverRespond:
        if (((msg).type) = (LockMsg)) {
            if ((queue) = (<<>>)) {
                network := [network EXCEPT ![(msg).from] = Append((network)[(msg).from], GrantMsg)];
                queue := Append(queue, (msg).from);
            } else {
                queue := Append(queue, (msg).from);
            };
        } else {
            if (((msg).type) = (UnlockMsg)) {
                queue := Tail(queue);
                if ((queue) # (<<>>)) {
                    network := [network EXCEPT ![Head(queue)] = Append((network)[Head(queue)], GrantMsg)];
                } ;
            };
        };
        goto serverReceive;
  }
  
  fair process (client \in ClientSet)
  variable resp = LockMsg;
  {
    acquireLock:
        network := [network EXCEPT ![ServerID] = Append((network)[ServerID], [from |-> self, type |-> LockMsg])];
    criticalSection:
        await (Len((network)[self])) > (0);
        resp := Head((network)[self]);
        network := [network EXCEPT ![self] = Tail((network)[self])];
        assert (resp) = (GrantMsg);
        hasLock := [hasLock EXCEPT ![self] = TRUE];
    unlock:
        hasLock := [hasLock EXCEPT ![self] = FALSE];
        network := [network EXCEPT ![ServerID] = Append((network)[ServerID], [from |-> self, type |-> UnlockMsg])];
  }
}

*)
\* BEGIN TRANSLATION (chksum(pcal) = "c79d554b" /\ chksum(tla) = "466b1242")
VARIABLES network, hasLock

(* define statement *)
ServerSet == {Server}
ClientSet == Clients
NodeSet == (ServerSet) \union (ClientSet)
LockMsg == 1
UnlockMsg == 2
GrantMsg == 3

VARIABLES serverState, clientState, msg, queue, resp

vars == << serverState, clientState, network, hasLock, msg, queue, resp >>

ProcSet == (ServerSet) \cup (ClientSet)

LOCKsvInit == (* Global variables *)
        /\ network = [id \in NodeSet |-> <<>>]
        /\ hasLock = [id \in NodeSet |-> FALSE]
        (* Process Server *)
        /\ msg = [self \in ServerSet |-> [from |-> "s", type |-> LockMsg]]
        /\ queue = [self \in ServerSet |-> <<>>]
        (* Process client *)
        /\ resp = [self \in ClientSet |-> LockMsg]
        /\ serverState = [s \in ServerSet |-> "waiting"]
        /\ clientState = [c \in ClientSet |-> "acquireLock"]

serverReceive(self) == /\ serverState[self] = "waiting"
                       /\ (Len(network[self])) > (0)
                       /\ msg' = [msg EXCEPT ![self] = Head(network[self])]
                       /\ network' = [network EXCEPT ![self] = Tail(network[self])]
                       /\ serverState' = [serverState EXCEPT ![self] = "sendingResponse"]
                       /\ UNCHANGED << clientState, hasLock, queue, resp >>

serverRespond(self) == /\ serverState[self] = "sendingResponse"
                       /\ IF (msg[self].type) = (LockMsg)
                             THEN /\ IF (queue[self]) = (<<>>)
                                        THEN /\ network' = [network EXCEPT ![msg[self].from] = Append(network[msg[self].from], GrantMsg)]
                                             /\ queue' = [queue EXCEPT ![self] = Append(queue[self], msg[self].from)]
                                        ELSE /\ queue' = [queue EXCEPT ![self] = Append(queue[self], msg[self].from)]
                                             /\ UNCHANGED network
                             ELSE /\ IF (msg[self].type) = (UnlockMsg)
                                        THEN /\ queue' = [queue EXCEPT ![self] = Tail(queue[self])]
                                             /\ IF (queue'[self]) # (<<>>)
                                                   THEN /\ network' = [network EXCEPT ![Head(queue'[self])] = Append(network[Head(queue'[self])], GrantMsg)]
                                                   ELSE /\ TRUE
                                                        /\ UNCHANGED network
                                        ELSE /\ TRUE
                                             /\ UNCHANGED << network, queue >>
                       /\ serverState' = [serverState EXCEPT ![self] = "waiting"]
                       /\ UNCHANGED << clientState, hasLock, msg, resp >>

server(self) == serverReceive(self) \/ serverRespond(self)

acquireLock(self) == /\ clientState[self] = "acquireLock"
                     /\ network' = [network EXCEPT ![Server] = Append(network[Server], [from |-> self, type |-> LockMsg])]
                     /\ clientState' = [clientState EXCEPT ![self] = "criticalSection"]
                     /\ UNCHANGED << serverState, hasLock, msg, queue, resp >>

criticalSection(self) == /\ clientState[self] = "criticalSection"
                         /\ (Len(network[self])) > (0)
                         /\ resp' = [resp EXCEPT ![self] = Head(network[self])]
                         /\ network' = [network EXCEPT ![self] = Tail(network[self])]
                         /\ Assert((resp'[self]) = (GrantMsg), "Unexpected message")
                         /\ hasLock' = [hasLock EXCEPT ![self] = TRUE]
                         /\ clientState' = [clientState EXCEPT ![self] = "unlock"]
                         /\ UNCHANGED << serverState, msg, queue >>

unlock(self) == /\ clientState[self] = "unlock"
                /\ hasLock' = [hasLock EXCEPT ![self] = FALSE]
                /\ network' = [network EXCEPT ![Server] = Append(network[Server], [from |-> self, type |-> UnlockMsg])]
                /\ clientState' = [clientState EXCEPT ![self] = "Done"]
                /\ UNCHANGED << serverState, msg, queue, resp >>

client(self) == acquireLock(self) \/ criticalSection(self) \/ unlock(self)

LOCKsvNext == (\E self \in ServerSet: server(self))
                \/ (\E self \in ClientSet: client(self))

LOCKsvSpec == /\ LOCKsvInit /\ [][LOCKsvNext]_vars
              /\ \A self \in ServerSet : WF_vars(server(self))
              /\ \A self \in ClientSet : WF_vars(client(self))

\* END TRANSLATION 
=============================================================================
