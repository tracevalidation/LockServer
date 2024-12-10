package org.lbee;

import java.io.IOException;
import java.net.Socket;
import java.net.UnknownHostException;

import org.lbee.instrumentation.clock.ClockException;
import org.lbee.instrumentation.clock.ClockFactory;
import org.lbee.instrumentation.trace.TLATracer;
import org.lbee.network.NetworkManager;
import org.lbee.protocol.Agent;
import org.lbee.protocol.Client;
import org.lbee.protocol.Server;

/**
 * Client manager (transaction manager or resource manager)
 */
public class StartAgent {

    public static void main(String[] args) throws IOException, ClockException {

        if (args.length < 5) {
            System.out.println("Missing arguments. hostname, port, clientName, serverName, duration expected.");
            return;
        }
        // Get hostname, port and type of manager
        final String hostname = args[0];
        final int port = Integer.parseInt(args[1]);
        final String clientName = args[2];
        final String serverName = args[3];
        final int duration = Integer.parseInt(args[4]);

        try (Socket socket = new Socket(hostname, port)) {
            final Agent manager;
            NetworkManager networkManager = new NetworkManager(socket);
            TLATracer spec = TLATracer.getTracer((clientName.equals("NONE") ? "" : clientName) + (clientName.equals("NONE") ? serverName : "") + ".ndjson",
                    ClockFactory.getClock(ClockFactory.FILE,"locksv.clock"));
                    // ClockFactory.getClock(ClockFactory.SERVER, "localhost", "6666"));
            if (clientName.equals("NONE")) {
                System.out.println("Server " + serverName + ".ndjson" + " INITIALIZED");
                manager = new Server(networkManager, serverName, duration, spec);
            } else {
                System.out.println("Client " + clientName + ".ndjson" + " INITIALIZED");
                manager = new Client(networkManager, clientName, serverName, duration, spec);
            }
            manager.run();
            // Send bye to server (kill the server thread)
            networkManager.sendRaw("bye");
        } catch (UnknownHostException ex) {
            System.out.println("Server not found: " + ex.getMessage());
        } catch (IOException ex) {
            System.out.println("I/O error: " + ex.getMessage());
        }
    }

}