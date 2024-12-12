package org.lbee.tla;

import org.lbee.instrumentation.helper.NDJsonSerializer;
import org.lbee.instrumentation.helper.TLASerializer;

import com.google.gson.JsonElement;
import com.google.gson.JsonObject;

/**
 * Class to serialize a message from a client to a server in the format expected by the TLA+ model.
 * The message is serialized as a JSON object with the following fields:
 * - from: the name of the client sending the message
 * - type: the type of the message (1 for LockMsg, 2 for UnlockMsg, 3 for GrantMsg)
 */
public class FromMessageTLA  implements TLASerializer {
    private final String from;
    private final int type;

    public FromMessageTLA(String from, String type) {
        this.from = from;
        switch (type) {
            case "LockMsg":
                this.type = 1;
                break;
            case "UnlockMsg":
                this.type = 2;
                break;
            case "GrantMsg":
                this.type = 3;
                break;
            default:
                this.type = -1;
        }
    }

    @Override
    public JsonElement tlaSerialize() throws IllegalAccessException {
        final JsonObject jsonObject = new JsonObject();
        jsonObject.add("from", NDJsonSerializer.serializeValue(this.from));
        jsonObject.add("type", NDJsonSerializer.serializeValue(this.type));
        return jsonObject;
    }
}
