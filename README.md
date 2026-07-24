Oracle Forms Test Scripts
=========================

Tools to test Oracle Forms based applications.

OracleFormsTester
-----------------

The `OracleFormsTester/` directory contains a Burp Suite extension that performs decryption, Message parsing and Scanner insertion point selection (Eclipse project).

To use these programs include `frmall.jar` archive provided by Oracle Forms  in your classpath. New Burp versions seem to have changed how Java libraries are being loaded (see #9). The folder with the fmrall.jar must be added to the JAVA Environment in the BurpSuite Extender Options. 

The following files outside the extension directory are simple utility programs that can help further develop the extension:

* MessageTester.java - Message parsers that allows easy debugging of the deserialization process.
* OracleFormsBruteForce.java - Primitive brute-forcer for encrypted protocol messages.
* OracleFormsSyncingBruteForce.java - Primitive brute-forcer that demonstrates the attack against an out-of-sync cipher stream. 

Further information can be found in my [GWAPT Gold Paper: Automated Security Testing of Oracle Forms Applications](https://www.sans.org/reading-room/whitepapers/testing/automated-security-testing-oracle-forms-applications-35970).

OracleFormsSerializer
---------------------

**You probably want to use this**

This is a new implementation that moves encryption state away from the client and Burp. Instead of juggling with state saving and restore for every possible message we simply kill encryption from the client (so Burp can work with plaintext messages) and reimplement it in a [mitmproxy](https://github.com/mitmproxy/mitmproxy) script.

Eliminating cryptography from the client is done by corrupting the handshake (huge thanks to [neonbunny](https://twitter.com/%40neonbunny9) for figuring this out!). The mitmproxy script takes care of the handshake and provides appropriately encrypted byte stream to the Oracle Forms server.

(Originally the tools worked with a patched version of the `frmall.jar` client library. If for any reason the current method stops working, the original approach can be followed as described [here](JARPATCH.md).)

Install dependencies and start mitmproxy with the provided script:
```
pip install -r requirements.txt
mitmdump -s mitmproxy_oracleforms.py -p 8081 
```

Configure Burp to use the upstream proxy 127.0.0.1:8081 and load the OracleFormsSerializer extension! New Burp versions seem to have changed how Java libraries are being loaded (see #9). The folder with the fmrall.jar must be added to the JAVA Environment in the BurpSuite Extender Options. 

Now you can start your Oracle Forms application, configured to use Burp as its proxy. The mitmproxy script will corrupt the handshake, so the client won't encrypt its messages. The OracleFormSerializer extension will then do message serialization for you. Messages will be translated to standard HTTP GET requests in the OracleForms request editor tab with String parameters provided in a query string in the Message body. If you edit these parameters the extension will automatically update the original binary Forms message appropriately (e.g. in Repeater). The extension will also register new insertion points for the Scanner so you can use that too (keep in mind that insertion points provided by Burp will probably break stuff though!).

### Editing Forms messages

Every Forms request and response can be edited, not just viewed:

* **Requests** — the **Oracle Forms** editor tab shows the message as editable `string_…`, `int_…` and `bool_…` parameters (one per line), including values nested inside other messages (e.g. `string_49_3_2`). Edit a value and the extension re-serializes the binary message for you (e.g. in Repeater or on Proxy intercept).
* **Responses** — responses are editable too. Because `frmall.jar` is the *client* library and can't re-emit server-only constructs, response edits are applied by patching the changed string literal directly into the original bytes, so only String values can be edited on responses.
* **Raw byte override** — the tab also shows the whole body as a `bytestream=<hex>` field; edit that to replace the message body verbatim (no serialization, no field logic) for arbitrary byte manipulation.
* **Tree view** — the **Oracle Forms Tree** tab renders the message as a filterable tree (messages → properties → nested messages) with a right-click "show raw hex". On editable surfaces you can edit String/Integer/Boolean leaves in place (double-click or *Edit value…*).

Response editing is only available where Burp gives you an editable editor (e.g. Proxy intercept).

### Automatic match/replace and policies

The **Oracle Forms M/R** suite tab applies transforms to live Forms traffic automatically:

* **Match/replace rules** — a persisted table of String (regex) and Integer (exact) rules, each scoped to requests, responses, or both. Requests are re-serialized with the rules applied; responses are byte-patched (string rules only).
* **Boolean policy** — a single *Booleans in requests* dropdown to flip all, set all true, or set all false for every boolean in a request.
* **Scope** — limit the above to all Forms traffic (default), Burp Target scope only, or a custom URL regex, so rules don't fire on unrelated hosts.

A single master switch enables or disables the whole engine (rules **and** the boolean policy), and everything persists across restarts.

### Recon aids

* **FRM/ORA error highlighting** — responses carrying `FRM-####`/`ORA-####` codes (e.g. authorization errors like `FRM-41084`, or `ORA-` SQL errors) are flagged with a red Proxy-history highlight, a comment listing the codes, and an alert. This stays on for all Forms responses regardless of the scope setting.
* **Debug output toggle** — verbose logging is off by default; enable it from the M/R tab when you need to trace what the extension is doing.

### Forms-aware search

Forms message bodies are serialized binary, so Burp's own search can't see the plaintext values inside them. The **Oracle Forms Search** suite tab deserializes the Forms messages already captured in your proxy history (and, optionally, the site map) and matches a literal or regex query against their String and Integer values. Results list where each hit occurred (message/property path), and selecting one shows the full HTTP request and response inline — including the extension's own decrypted Forms tabs — so you can inspect the match without leaving the tab. Right-click a result to send the request to Repeater or highlight it in history, or right-click selected text anywhere in Burp and choose *Search Forms history for selection* to run the same search.

Searching is fast even on large histories: for a plain-text query a cheap raw-byte prefilter skips the expensive deserialization of any message that can't contain it, and the scan runs in the background with a progress bar and a Cancel button. (The prefilter is bypassed for regex, non-ASCII, and all-digit queries, so results are always complete.)

### Building the Extension

Download the `frmall.jar` archive from your target and copy it under `OracleFormsSerializer/lib`. Inside `OracleFormsSerializer/` start an Gradle build:

```
$ ./gradlew shadowJar
```

You should find `OracleFormsSerializer-<SOMEVERSION>-all.jar` under `build/libs/`.

### Options

#### Response timeout

The mitmproxy script now handles "wait" error codes ([ifError:11](https://community.oracle.com/docs/DOC-893120)) that instruct the client to wait before it can retrieve the results from the server. The maximum wait time can be configured in the command line (value given in milliseconds):

```
mitmdump -s mitmproxy_oracleforms.py --set max_wait=10000 -p 8081 # Wait at most 10s
```

By default the wait time is unlimited. After a limit is reached the error codes are passed back to the client that should handle them appropriately. Handling these errors in the proxy allows downstream scripts to make detections based on the RTT of a single request instead of parsing multiple messages.

#### Handshake corruption

See [JARPATCH.md](JARPATCH.md)

### mitmproxy support

The script was upgraded to support mitmproxy 12 (tested with 12.1.1).

Scanner Configuration
---------------------

An exported Burp 2.x Scanner configuration is added to the repo. Main properties:
* Limited to relevant tests
* Virtually unlimited error thresholds (see #15)
* Limited insertion points

*Important:* In order to keep the stream ciphers in sync, you have to configure a single threaded resource pool for your scan!

It is very likely that automated input will render the UI unusable and you have to restart the application! Use [Logger++](https://portswigger.net/bappstore/470b7057b86f41c396a97903377f3d81) to keep track of responses and any server-side errors (or interesting behavior)!

Tutorials
---------

* [Corrupting Ancient Spirits - Hacktivity'17 presentation](https://www.youtube.com/watch?v=hEoeDPk4TOE)
* [Setting up OracleFormsSerializer](https://vimeo.com/482011043)

Common Errors
-------------

* FRM-92095: Older versions of Oracle Forms won't start until you convince it that Java is still owned by Sun Microsystems... Create a system wide environment variable (as described [here](https://blogs.oracle.com/ptian/solution-for-error-frm-92095:-oracle-jnitiator-version-too-low)): `JAVA_TOOL_OPTIONS='-Djava.vendor="Sun Microsystems Inc."'`
* FRM-92101: `frmall.jar` is cached by the browser so if serve a patched version and then remove the mitmproxy script for some reason (e.g. live demo at a conference...) the browser will then send an `If-Modified-Since` header to the original server so it won't serve the new (unpatched) JAR. As a result the server-side decryption won't work. You can resolve this by removing the mentioned header from the HTTP request (Burp Proxy has a built-in replace rule to do this). The cause can be of course any other problem resulting in invalid streams being decrypted by the server. 
* `ifError: 11/xxx` on server responses: These messages [instruct the client](https://community.oracle.com/docs/DOC-893120) to wait xxx milliseconds and try to retrieve the request by sending an empty request again. This should be properly handled by the mitmproxy script now.

Pro Tips
--------

* If something goes wrong you'll probably want to restart mitmproxy so the objects will be reinitialized to a clean state
* Scan only with a single thread
* Disable default Scanner insertion points
