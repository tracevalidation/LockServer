package org.lbee.protocol;

import java.io.IOException;
import java.util.ArrayList;
import java.util.List;

import org.lbee.helpers.Helper;
import org.lbee.instrumentation.trace.TLATracer;
import org.lbee.instrumentation.trace.VirtualField;
import org.lbee.network.NetworkManager;
import org.lbee.network.TimeOutException;
import org.lbee.tla.FromMessageTLA;

public class Server extends Agent {

    // possible values for the state of the server
    private static final String SENDING_RESPONSE = "sendingResponse";
    private static final String WAITING = "waiting";
    //possible server actions
    private static final String DO_SERVER_RECEIVE = "serverReceive";
    private static final String DO_SERVER_RESPOND = "serverRespond";

    // Timeout for receiving messages
    private final static int RECEIVE_TIMEOUT = 100;
    // Abort if not all RMs sent before ABORT_TIMEOUT
    private final static int ABORT_TIMEOUT = 400; // 100
    // maximum duration of the initialisation phase
    private static final int MAX_INIT_DURATION = 10; // 100

    // Clients waiting for a lock
    private final List<String> clients;
    // Duration of the initialisation phase
    private final int initDuration;

    // Tracing variables
    private final VirtualField traceState;
    private final VirtualField traceMessage;
    // private final VirtualField traceQueue;
    // private final VirtualField traceNetwork;

    public Server(NetworkManager networkManager, String name, int initDuration, TLATracer tracer) {
        super(name, networkManager, tracer);
        this.clients = new ArrayList<>();
        if (initDuration == -1) {
            this.initDuration = Helper.next(MAX_INIT_DURATION);
        } else {
            this.initDuration = initDuration;
        }
        this.traceState = tracer.getVariableTracer("serverState").getField(this.name);
        this.traceMessage = tracer.getVariableTracer("msg").getField(this.name);
        // this.traceQueue = tracer.getVariableTracer("queue").getField(this.name);
        // this.traceNetwork = tracer.getVariableTracer("network").getField(this.name);
    }

    private void initialising() {
        // Simulate initialisation phase
        try {
            Thread.sleep(this.initDuration);
        } catch (InterruptedException ex) {
        }
    }

    @Override
    public void run() throws IOException {
        boolean done = false;
        long startTime = System.currentTimeMillis();
        // initialising phase
        this.initialising();
        // keep receiving messages 
        while (!done) {
            // block on receiving message until timeout, retry if timeout
            boolean messageReceived = false;
            do {
                // Abort if no messages for too long (not in the spec)
                if (System.currentTimeMillis() - startTime > ABORT_TIMEOUT) {
                    done = true;
                    System.out.println("-- SERVER  aborted (timeout)");
                    break;
                }
                Message message;
                try {
                    message = receiveMessage();
                    startTime = System.currentTimeMillis();
                    messageReceived = true;
                } catch (TimeOutException e) {
                    System.out.println("SERVER TIMEOUT (on waiting message)");
                    continue;
                } catch (IOException e) {
                    System.out.println("SERVER IO Exception");
                    continue;
                }
                this.handleMessage(message);
            } while (!messageReceived);
        }
        System.out.println("-- SERVER  shutdown");
    }

    /**
     * Receive a message from a client.
     */
    private Message receiveMessage() throws TimeOutException, IOException {
        Message message = networkManager.receive(this.name, RECEIVE_TIMEOUT);
        // trace the state change
        traceState.update(SENDING_RESPONSE);
        // since "from" and "type" fields have different types, we can't use a Map like JSON serialization 
        traceMessage.update(new FromMessageTLA(message.getFrom(), message.getContent()));
        tracer.log(DO_SERVER_RECEIVE, new Object[]{this.name});
        return message;
    }

    /**
     * Handle message from a client.
     */
    private void handleMessage(Message message) throws IOException {
        if (message.getContent().equals(ClientServerMessage.LockMsg.toString())) {
            if (clients.isEmpty()) {
                this.networkManager.send(new Message(this.name, message.getFrom(), ClientServerMessage.GrantMsg.toString(), 0));
            }
            this.clients.add(message.getFrom());
            // trace the state change
            traceState.update(WAITING);
            tracer.log(DO_SERVER_RESPOND, new Object[]{this.name});
        } else {
            if (message.getContent().equals(ClientServerMessage.UnlockMsg.toString())) {
                this.clients.remove(message.getFrom());
                if (!clients.isEmpty()) {
                    this.networkManager.send(new Message(this.name, clients.get(0), ClientServerMessage.GrantMsg.toString(), 0));
                }
                // trace the state change
                traceState.update(WAITING);
                tracer.log(DO_SERVER_RESPOND, new Object[]{this.name});
            } else {
                System.out.println("Unxpected message: " + message);
            }
        }
        System.out.println("SERVER received " + message.getContent() + " from " + message.getFrom());
    }

}
