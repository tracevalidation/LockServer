--------------------------- MODULE locksvTrace ---------------------------
(***************************************************************************)
(* Trace spec that refines locksv *)
(***************************************************************************)

EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags, Json, IOUtils, locksv, TVOperators, TraceSpec

(* Override CONSTANTS *)

(* Replace Nil constant *)
TraceNil == "null"

(* Replace constants *)
TraceClients ==
    ToSet(Config[1].Clients)
TraceServer ==
    Config[2].ServerID

(* Can be extracted from init *)

LOCKsvUpdateVariables(t) ==
    /\
        IF "network" \in DOMAIN t
        THEN network' = UpdateVariable(network, "network", t)
        ELSE TRUE
    /\
        IF "hasLock" \in DOMAIN t
        THEN hasLock' = UpdateVariable(hasLock, "hasLock", t)
        ELSE TRUE
    /\
        IF "serverState" \in DOMAIN t
        THEN serverState' = UpdateVariable(serverState, "serverState", t)
        ELSE TRUE
    /\
        IF "clientState" \in DOMAIN t
        THEN clientState' = UpdateVariable(clientState, "clientState", t)
        ELSE TRUE
    /\
        IF "msg" \in DOMAIN t
        THEN msg' = UpdateVariable(msg, "msg", t)
        ELSE TRUE
    /\
        IF "queue" \in DOMAIN t
        THEN queue' = UpdateVariable(queue, "queue", t)
        ELSE TRUE
    /\
        IF "resp" \in DOMAIN t
        THEN resp' = UpdateVariable(resp, "resp", t)
        ELSE TRUE

(* Predicate actions *)
ISserverReceive ==
    /\ IsEvent("serverReceive")
    /\
        IF "event_args" \in DOMAIN logline /\ Len(logline.event_args) >= 1 THEN
            serverReceive(logline.event_args[1])
        ELSE
            serverReceive(TraceServer)

ISserverRespond ==
    /\ IsEvent("serverRespond")
    /\
        IF "event_args" \in DOMAIN logline /\ Len(logline.event_args) >= 1 THEN
            serverRespond(logline.event_args[1])
        ELSE
            serverRespond(TraceServer)

ISacquireLock ==
    /\ IsEvent("acquireLock")
    /\
        IF "event_args" \in DOMAIN logline /\ Len(logline.event_args) >= 1 THEN
            acquireLock(logline.event_args[1])
        ELSE
            \E r \in TraceClients : acquireLock(r)

IScriticalSection ==
    /\ IsEvent("criticalSection")
    /\
        IF "event_args" \in DOMAIN logline /\ Len(logline.event_args) >= 1 THEN
            criticalSection(logline.event_args[1])
        ELSE
            \E r \in TraceClients : criticalSection(r)

ISunlock ==
    /\ IsEvent("unlock")
    /\
        IF "event_args" \in DOMAIN logline /\ Len(logline.event_args) >= 1 THEN
            unlock(logline.event_args[1])
        ELSE
            \E r \in TraceClients : unlock(r)

LOCKsvTraceNext ==
        \/ ISserverReceive
        \/ ISserverRespond
        \/ ISacquireLock
        \/ IScriticalSection
        \/ ISunlock

(* Eventually composed actions *)
ComposedNext == FALSE

BaseSpec == LOCKsvInit /\ [][LOCKsvNext \/ ComposedNext]_vars
-----------------------------------------------------------------------------
=============================================================================