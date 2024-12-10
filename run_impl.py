import os
import argparse
import ndjson
import time
import signal
from subprocess import Popen

jar_name = "locksv-1.1-noabort-demo-jar-with-dependencies.jar"

def read_json(filename):
    with open(filename) as f:
        return ndjson.load(f)

def run(clients, server):
    print("--- Run server ---")
    network_process = Popen([
        "java",
        "-cp",
        f"target/{jar_name}",
        "org.lbee.network.Server",
        "6869", "unordered"])

    print("--- Run server ---")
    clock_process = Popen([
        "java",
        "-cp",
        f"target/{jar_name}",
        "org.lbee.instrumentation.clock.ServerClock",
        "6666"])

    # Wait the server to run, if not some manager might start 
    # running before the server, leading to an error
    # This behavior might be interesting for trace validation
    time.sleep(2)

    print("--- Run Server client ---")
    duration = 1
    args = [
        "java",
        "-cp",
        f"target/{jar_name}",
        "org.lbee.StartAgent",
        "localhost", "6869", "NONE", f"{server}",f"{duration}"]
    server_process = Popen(args)

    print("--- Run Client clients ---")
    client_processes = []
    duration = 1
    for client in clients:
        args = [
            "java",
            "-cp",
            f"target/{jar_name}",
            "org.lbee.StartAgent",
            "localhost", "6869", f"{client}", f"{server}", f"{duration}"]
        client_process = Popen(args)
        client_processes.append(client_process)

    # Wait for all clients to be finished
    server_process.wait()
    for client_process in client_processes:
        client_process.wait()
    # terminate
    network_process.terminate()
    server_process.terminate()
    for client_process in client_processes:
        client_process.terminate()
    # Kill server
    os.kill(network_process.pid, signal.SIGINT)
    os.kill(clock_process.pid, signal.SIGINT)

if __name__ == "__main__":
    # Read program args
    parser = argparse.ArgumentParser(description="")
    parser.add_argument('--config', type=str, required=False,
                        default="conf.ndjson", help="Config file")
    args = parser.parse_args()
    # Read config and run
    config = read_json(args.config)
    clients = config[0]["Clients"]
    server = config[1]["ServerID"]
    print(f"Server: {server}")
    print(f"Clients: {clients}")
    run(clients, server)
