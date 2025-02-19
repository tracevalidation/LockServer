package org.lbee.protocol;

import java.io.IOException;

import org.lbee.helpers.Helper;
import org.lbee.instrumentation.trace.TLATracer;
import org.lbee.instrumentation.trace.VirtualField;
import org.lbee.network.NetworkManager;
import org.lbee.network.TimeOutException;

public class Client extends Agent {

    // possible values for the state of the client
    // private static final String ACQUIRE_LOCK = "acquireLock";
    private static final String CRITICAL_SECTION = "criticalSection";
    private static final String UNLOCK = "unlock";
    private static final String DONE = "Done";

    // possible client actions
    private static final String DO_ACQUIRE_LOCK = "acquireLock";
    private static final String DO_CRITICAL_SECTION = "criticalSection";
    private static final String DO_UNLOCK = "unlock";

    // private final static int PROBABILITY_TO_ABORT = 100;
    private static final int MAX_TASK_DURATION = 10;
    // Abort if no message from SERVER for ABORT_TIMEOUT
    private final static int ABORT_TIMEOUT = 2000; //200

    // Server (to send message to)
    private final String serverName;
    // Duration of underlying task
    private final int taskDuration;

    // Tracing variables
    private final VirtualField traceState;
    // private final VirtualField traceMessage;
    // private final VirtualField traceQueue;
    // private final VirtualField traceNetwork;

    /**
     * Construct a resource manager
     *
     * @param NetworkManager Network support (for send/receive messages)
     * @param name Resource manager name
     * @param transactionManagerName Attached transaction manager name
     * @param taskDuration Duration of underlying task
     * @param tracer Trace instrumentation
     */
    public Client(NetworkManager networkManager, String name, String serverName,
            int taskDuration, TLATracer tracer) {
        super(name, networkManager, tracer);
        this.serverName = serverName;
        if (taskDuration == -1) {
            this.taskDuration = Helper.next(MAX_TASK_DURATION);
        } else {
            this.taskDuration = taskDuration;
        }
        // prepare tracing
        this.traceState = tracer.getVariableTracer("clientState").getField(this.name);
        // this.traceMessages = tracer.getVariableTracer("msgs");

        System.out.println("Client " + name + " INITIALIZED");
    }

    @Override
    public void run() throws IOException {
        boolean done = false;
        long startTime = System.currentTimeMillis();
        // Simulate a crash of the Client
        // int possibleAbort = Helper.next(PROBABILITY_TO_ABORT);
        // if (possibleAbort == 1) {
        //     System.out.println("Client " + this.name + " ABORT ");
        //     return;
        // }
        // work
        working();
        // send request for lock
        this.sendRequest();
        // block on receiving message until timeout, abort if wait too long
        Message message = null;
        while (!done) {
            if (System.currentTimeMillis() - startTime > ABORT_TIMEOUT) {
                System.out.println("-- Client " + this.name + " aborted (timeout)");
                // should send an unlock here
                return;
            }
            try {
                message = this.receiveMessage();
                done = true;
            } catch (TimeOutException e) {
                System.out.println("Client " + this.name + " received TIMEOUT ");
            } catch (IOException e) {
                System.out.println("Client " + this.name + " received IOEXCEPTION ");
            }
        }
        this.handleMessage(message);
        this.sendUnlock();
        System.out.println("-- Client " + this.name + " shutdown");
    }

    private void working() {
        // Simulates working
        try {
            Thread.sleep(this.taskDuration);
        } catch (InterruptedException ex) {
        }
    }

    private void sendRequest() throws IOException {
        // trace the state change
        traceState.update(CRITICAL_SECTION);
        tracer.log(DO_ACQUIRE_LOCK, new Object[]{this.name});

        this.networkManager.send(new Message(
                this.name, this.serverName, ClientServerMessage.LockMsg.toString(), 0));

        System.out.println("Client " + this.name + " sent " + ClientServerMessage.LockMsg.toString());
    }

    private Message receiveMessage() throws TimeOutException, IOException {
        Message message = networkManager.receive(this.name, this.taskDuration * 2);
        return message;
    }

    private void handleMessage(Message message) throws IOException {
        if (message.getContent().equals(ClientServerMessage.GrantMsg.toString())) {
            // trace the state change
            traceState.update(UNLOCK);
            tracer.log(DO_CRITICAL_SECTION, new Object[]{this.name});
            System.out.println("Client " + this.name + " received " + ClientServerMessage.GrantMsg.toString());
            this.working();
        } else {
            throw new IOException("Unexpected message: " + message.getContent());
        }
        System.out.println("Client " + this.name + " finished working ");
    }

    private void sendUnlock() throws IOException {
        // trace the state change
        traceState.update(DONE);
        tracer.log(DO_UNLOCK, new Object[]{this.name});
        this.networkManager.send(new Message(
                this.name, this.serverName, ClientServerMessage.UnlockMsg.toString(), 0));
        System.out.println("Client " + this.name + " sent " + ClientServerMessage.UnlockMsg.toString());
    }
}
