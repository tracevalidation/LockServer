package org.lbee.protocol;

import java.io.IOException;

import org.lbee.instrumentation.trace.TLATracer;
import org.lbee.network.NetworkManager;

public abstract class Agent {
    final String name;
    final NetworkManager networkManager;
    final TLATracer tracer;

    public Agent(String name, NetworkManager networkManager, TLATracer tracer) {
        this.name = name;
        this.networkManager = networkManager;

        this.tracer = tracer;
    }

    public abstract void run() throws IOException;
}
