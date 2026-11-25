# W1 (`phase7-s2-core-merge`): the trusted text it changes

Branch `phase7-s2-core-merge/2026-11-26`, off `phase7-s2a/2026-11-25` (`435a8c3af3`). Plan:
`notes/phase7-endstate.md` §4 (W1 row), S2 §5. **Not built yet** (VM hold): every Lean claim below is
unchecked until the build.

## 1. What W1 brings that is not trusted

- `origin/phase7-s2-core` (`f361625701`) merged: the client attempt's translations and proofs (the frame
  writers, `headerListTooLarge`, the six variables, `createHeaderFields` and its helpers, `grpcutil`,
  `internal/metadata`, `metadata.fromOutgoingContextRaw`, `credentials.NewContextWithRequestInfo`,
  `time.Until`, `binary.BigEndian.AppendUint32`, base64's `RawStdEncoding`). `lean`'s `InvGrpcWire.lean`
  kept (the plan's decision). `outRawIs_of_outMD` (core's last commit, never built) is re-checked by the
  first build.
- `internal`'s package fact: `lean`'s write-only hook cells (phase7-inits) plus core's own invariant for
  `FromOutgoingContextRaw` (`fromOutRawInv`), which grpc's initializer reads; `metadata`'s fact says its
  `init` stored `fromOutgoingContextRaw` there (`metadataInit`).
- grpc's package fact (`grpcInit`, one batch, so that the 7700-module rebuild happens once): beside
  `EnableTracing`, the cells `metadataFromOutgoingContextRaw` (holds `metadata.fromOutgoingContextRaw`:
  `grpc.outRawFn.law`, which `createHeaderFields` takes, is now proved, `outRawFn_law_holds`),
  `globalServerOptions` (nil) and `defaultServerOptions` (its literal, `grpcDefaultSrvOpts`), each
  persistent. Proved by grpc's generated `Init`. Package facts are proved, not trusted.
- Translated with their bodies, for step 3: `NewServer`, the chain builders, `defaultServerOptions` (was
  a goose skip), `RegisterService`/`register`/`printf`/`wrapUnaryHandler`, `CustomCodec`,
  `newCodecV0Bridge`, `grpcsync.NewEvent`, `internal/stats.NewCombinedHandler` (a new package, fact
  `True`).
- `origin/grpc-neutral-narrow/2026-11-26` (`dac450d58b`) merged: the narrowed `.neutral` (its own review,
  `notes/axiom-review/grpc-neutral-narrow.md`).

## 2. Trusted text, old → new

### 2.1 `grpc.CustomCodec.wp_proof`: axiom → theorem (−1 axiom)

Old: `axiom grpc.CustomCodec.wp_proof : grpc.CustomCodec.spec`. New: a theorem over the model's body
(`Proof/google_golang_org/grpc/CustomCodec.lean`). The closure stores `newCodecV0Bridge(c)` in `codec` and
nothing else, so it meets the narrowed `.neutral`: `srvOptsSameBut` by structure eta, and `srvCodecOk`'s
second disjunct from the premise `grpcProtoCodec c`. The spec's text is unchanged.

### 2.2 The grpc model (`models/grpc`): the core branch's three commits

- `f73cbd1a8b` (**F1**): no header block over the receiver's 16 MiB limit is written. grpc-go v1.84's
  client fails such a stream with `codes.Internal` before writing; the model used to frame a block of 4 GiB
  or more wrongly. Evidence: `models/internal/grpcdifftest/headerlimit_test.go`, which runs against
  grpc-go and the model.
- `1c27627667`: `model_wire.go`'s frame writers split into the helpers that are translated. Only the
  code's structure changes.
- `774c820b34` (`MODEL:`): `createHeaderFields`' audience uses a backwards byte loop instead of
  `strings.LastIndex`, which Perennial has no spec for. Its difftest is `TestPerRPCCredsAudience`. This is
  a proof-driven workaround (rule 14). It is reverted once Perennial proves `strings.LastIndex` (S2 §3).

`models/README.md`'s grpc row claims the limit: "with no header block written over the receiver's 16 MiB
limit (`model_wire.go`, `headerListTooLarge`, 2026-11-23)". The evidence column adds
`headerlimit_test.go`.

The exact diff of `models/grpc` (merge base `af67426be3` → `f361625701`; this branch has it unchanged):

```diff
diff --git a/models/grpc/model_transport.go b/models/grpc/model_transport.go
index 7051741e9b..1b503b411b 100644
--- a/models/grpc/model_transport.go
+++ b/models/grpc/model_transport.go
@@ -258,6 +258,21 @@ func newClientTransportStream(ctx context.Context, cc *ClientConn, conn net.Conn
 		conn.Close()
 		return nil, &newStreamError{Err: ErrClientConnClosing, AllowTransparentRetry: false}
 	}
+	if headerListTooLarge(fields) {
+		// MODEL: a head over the server's limit (model_wire.go, F1) is not written, and the stream
+		// ends as grpc-go's does when its server refuses the list: a FRAME_SIZE_ERROR reset (a list
+		// truncated in its last frame) or the end of the connection (the server's connection error,
+		// measured for a field over the limit), the model's choice; never retried (in grpc-go the
+		// server has read the head).
+		var st *status.Status
+		if modelChoose() {
+			st = status.New(codes.Internal, "stream terminated by RST_STREAM with error code: FRAME_SIZE_ERROR")
+		} else {
+			st = transportFailure("error reading from server: EOF")
+		}
+		s.closeStream(st.Err(), false, st, nil)
+		return s, nil
+	}
 	b := appendHeaderBlock(nil, frameHead, fields)
 	s.wmu.Lock()
 	n, werr := conn.Write(b)
@@ -280,7 +295,15 @@ func createHeaderFields(ctx context.Context, cc *ClientConn, authInfo credential
 	if len(perRPCCreds) != 0 || callHdr.Creds != nil {
 		// createAudience: omit port if it is the default one.
 		host := strings.TrimSuffix(callHdr.Host, ":443")
-		pos := strings.LastIndex(callHdr.Method, "/")
+		// MODEL: strings.LastIndex(callHdr.Method, "/"), as a backwards byte loop (Perennial has no
+		// model of LastIndex; for a one-byte separator the same index, -1 if absent)
+		pos := -1
+		for i := len(callHdr.Method) - 1; i >= 0; i-- {
+			if callHdr.Method[i] == '/' {
+				pos = i
+				break
+			}
+		}
 		if pos == -1 {
 			pos = len(callHdr.Method)
 		}
@@ -426,6 +449,10 @@ func (s *clientTransportStream) reader() {
 		switch kind {
 		case frameHeader, frameTrailer:
 			fields, err := readHeaderBlock(s.conn)
+			if err == errHeaderListTooLarge {
+				s.headerListTooLarge()
+				return
+			}
 			if err != nil {
 				s.readFailed(err)
 				return
@@ -484,6 +511,23 @@ func (s *clientTransportStream) handleRSTStream(errCode uint32) {
 	s.closeStream(st.Err(), false, st, nil)
 }
 
+// headerListTooLarge ends the stream on a server's header block over the client's limit
+// (model_wire.go, F1), as grpc-go's client does, by the way the list goes over it: a field over the
+// limit (the hpack decoder's COMPRESSION_ERROR, a connection error; measured), a list over it in its
+// last frame (operateHeaders on a truncated frame: Internal, and a RST_STREAM), or a list continued
+// after it (a PROTOCOL_ERROR connection error). MODEL: the way is the model's choice.
+func (s *clientTransportStream) headerListTooLarge() {
+	switch modelChooseN(3) {
+	case 0:
+		s.readFailed(errHeaderListTooLarge)
+	case 1:
+		st := status.New(codes.Internal, "peer header list size exceeded limit")
+		s.closeStream(st.Err(), true, st, nil)
+	default:
+		s.readFailed(errors.New("connection error: PROTOCOL_ERROR"))
+	}
+}
+
 // readFailed ends the stream after its connection failed (http2Client.Close on a reader error).
 func (s *clientTransportStream) readFailed(err error) {
 	st := transportFailure(fmt.Sprintf("error reading from server: %v", err))
@@ -1090,7 +1134,17 @@ func (t *serverTransport) writeEarlyAbort(contentSubtype string, stat *status.St
 			hf = append(hf, headerField{Name: grpcStatusDetailsBinHeader, Value: encodeBinHeader(stBytes)})
 		}
 	}
-	t.write(appendHeaderBlock(nil, frameTrailer, hf))
+	t.writeHeaderBlock(frameTrailer, hf)
+}
+
+// writeHeaderBlock writes a header or trailer block, or its over-limit marker if its list is over
+// the client's limit. MODEL: (model_wire.go, F1) grpc-go's server sends such a list, which its
+// client refuses; the model's reader refuses the marker in the same ways (headerListTooLarge).
+func (t *serverTransport) writeHeaderBlock(kind byte, fields []headerField) error {
+	if headerListTooLarge(fields) {
+		return t.write(appendOversizedBlock(nil, kind))
+	}
+	return t.write(appendHeaderBlock(nil, kind, fields))
 }
 
 // serverTransportStream is a dispatched server stream (transport.ServerStream).
@@ -1282,7 +1336,7 @@ func (s *serverTransportStream) writeHeaderLocked() error {
 		headerFields = append(headerFields, headerField{Name: "grpc-encoding", Value: s.sendCompress})
 	}
 	headerFields = appendHeaderFieldsFromMD(headerFields, s.header)
-	if err := s.st.write(appendHeaderBlock(nil, frameHeader, headerFields)); err != nil {
+	if err := s.st.writeHeaderBlock(frameHeader, headerFields); err != nil {
 		s.closeStream(err)
 		return err
 	}
@@ -1334,7 +1388,7 @@ func (s *serverTransportStream) WriteStatus(st *status.Status) error {
 
 	// Attach the trailer metadata.
 	headerFields = appendHeaderFieldsFromMD(headerFields, s.trailer)
-	err := s.st.write(appendHeaderBlock(nil, frameTrailer, headerFields))
+	err := s.st.writeHeaderBlock(frameTrailer, headerFields)
 	s.closeStream(contextErr(context.Canceled))
 	if err == nil && s.st.stats != nil {
 		// Note: The trailer fields are compressed with hpack after this call returns.
diff --git a/models/grpc/model_wire.go b/models/grpc/model_wire.go
index ea9c95e714..b16de5425b 100644
--- a/models/grpc/model_wire.go
+++ b/models/grpc/model_wire.go
@@ -21,6 +21,8 @@ package grpc
 //
 //	frame   = kind:u8 body
 //	head, header, trailer: length:u32be fields     (a header block; length bounded before reading)
+//	header, trailer:       length:u32be            (a length over maxHeaderBlock, no fields: a block
+//	                                                the server did not send, over the client's limit)
 //	fields  = count:u32be (nameLen:u32be name valueLen:u32be value)*
 //	data:    flag:u8 length:u32be message           (one gRPC length-prefixed message, as on HTTP/2)
 //	reset:   code:u32be                             (an HTTP/2 error code)
@@ -74,6 +76,10 @@ type headerField struct {
 
 var errMalformedFrame = errors.New("grpc: malformed frame")
 
+// errHeaderListTooLarge is a header block over the reader's limit (http2.ConnectionError's message
+// for the hpack decoder's string length limit, which a field over the limit hits first).
+var errHeaderListTooLarge = errors.New("connection error: COMPRESSION_ERROR")
+
 // readFull reads exactly len(b) bytes from c (io.ReadFull's contract: io.ErrUnexpectedEOF if the
 // connection ends inside them, io.EOF if before any).
 func readFull(c net.Conn, b []byte) error {
@@ -103,7 +109,47 @@ func readFrameKind(c net.Conn) (byte, error) {
 	return k[0], nil
 }
 
-// appendHeaderBlock appends a head, header or trailer frame carrying fields.
+// MODEL: a header list's size bounds what is sent (finding F1, notes/phase7-plan.md, section 0a:
+// appendHeaderBlock writes lengths as uint32s, so a block of 4 GiB or more would be misframed). A
+// receiver of grpc-go v1.84.0 refuses a header list over its limit (defaultClientMaxHeaderListSize,
+// defaultServerMaxHeaderListSize: 16 MiB) as x/net/http2 counts it (hpack.HeaderField.Size: name,
+// value and 32 per field; Framer.readMetaFrame): such a list never reaches the receiving program,
+// whichever way it fails (a FRAME_SIZE_ERROR reset of a truncated list, a COMPRESSION_ERROR or
+// PROTOCOL_ERROR connection error of a field or a continuation over it; measured,
+// internal/grpcdifftest/headerlimit_test.go). So the model's writers check the list's size before
+// writing: the client ends its stream unsent (newClientTransportStream), the server writes the
+// over-limit marker instead (appendOversizedBlock), on which the client's reader fails the stream as
+// grpc-go's does. A peer's smaller limit (the MaxHeaderListSize options) is not modelled: the options
+// are ignored, as before.
+
+// headerListTooLarge reports whether fields' header list is over the receiver's limit (its size
+// counted as HTTP/2 does, stopping once over the limit: each addition is of one length to a sum
+// within the limit, so the sum cannot overflow).
+func headerListTooLarge(fields []headerField) bool {
+	var sz uint64
+	for _, f := range fields {
+		sz += 32 + uint64(len(f.Name))
+		if sz > maxHeaderBlock {
+			return true
+		}
+		sz += uint64(len(f.Value))
+		if sz > maxHeaderBlock {
+			return true
+		}
+	}
+	return false
+}
+
+// appendOversizedBlock appends the marker of a header or trailer block over the receiver's limit,
+// which is not sent: its kind and a length over maxHeaderBlock, which the reader refuses before
+// reading any field.
+func appendOversizedBlock(b []byte, kind byte) []byte {
+	b = append(b, kind)
+	return binary.BigEndian.AppendUint32(b, maxHeaderBlock+1)
+}
+
+// appendHeaderBlock appends a head, header or trailer frame carrying fields, whose list is not over
+// the limit (every caller checks headerListTooLarge first), so that every length fits its uint32.
 func appendHeaderBlock(b []byte, kind byte, fields []headerField) []byte {
 	n := 4
 	for _, f := range fields {
@@ -129,7 +175,10 @@ func readHeaderBlock(c net.Conn) ([]headerField, error) {
 		return nil, err
 	}
 	n := binary.BigEndian.Uint32(lb[:])
-	if n < 4 || n > maxHeaderBlock {
+	if n > maxHeaderBlock {
+		return nil, errHeaderListTooLarge
+	}
+	if n < 4 {
 		return nil, errMalformedFrame
 	}
 	p := make([]byte, n)
```

### 2.3 `srvOptFnOk`'s kinds narrowed

This is `grpc-neutral-narrow`'s change, reviewed in its own note. It enters the post of the one remaining
trusted producer of a server option, `grpc.StatsHandler.wp_proof`: its `.stats h` now also fixes every
non-whitelisted field. That is true of the model, whose closure sets only `statsHandlers` or, for a nil
`h`, nothing.

## 3. Step 3 (`grpcSrvNew` defined; `NewServer`, `RegisterService` proved): status and design

**Not done on this branch yet.** The groundwork is in place: the translations, `grpcInit`'s two cells,
the narrowed `.neutral`, and `CustomCodec`. `grpcSrvNew` is still the axiom; `NewServer` and
`RegisterService` are still axioms.

### 3.1 The definition

`grpcSrvNew gs ics sics svcs regs sregs` would hold all of the following, owned exclusively:

- `gs ↦ srv`;
- `srv.opts`:
  - `chainUnaryInts ↦* ics` and `chainStreamInts ↦* sics`, with their capacities;
  - `statsHandlers ↦*□ hs` with `∀ h ∈ hs, grpcStatsHandlerOk h` (the `.stats` kind must carry the
    property, see 3.2);
  - `unaryInt`: `nil` if `ics = []`, `ics[0]` if `[i]`, else `chainUnaryInterceptors`' closure over a
    cell holding the chain's slice; `streamInt` likewise;
  - `creds`, `cp`, `dc`, `unknownStreamDesc` and `streamWrapper` are nil;
  - `codec` is nil or a protobuf codec's bridge (`srvCodecOk`'s form);
- `srv.statsHandler` = `NewCombinedHandler(hs)`'s value;
- `srv.mu`: `isMutex` at `True`, unlocked. Exclusive `ownMutex` lets a later proof of `Serve` encode its
  own lock invariant;
- `lis`, `conns` empty maps; `serve`, `drain` false; `events` nil; `cv` a `sync.Cond` on `mu`; `quit`,
  `done` fresh `Event`s; the wait groups zero;
- `services ↦$ M`, with `dom M = svcs`. For each service, its `*serviceInfo` holds the service value and
  a `streams` map:
  - each stream name maps to its `&sd.Streams[i]`, read-only through `grpcDescIs`;
  - each method name maps to a `&StreamDesc{name, Handler: wrapUnaryHandler(&sd.Methods[i]), false, false}`;
  - each `regs`/`sregs` entry is read off this map.

**Open question (needs a decision before the proofs).** How the definition names the method handlers'
closure `wrapUnaryHandler(md)`. In GooseLang it is a `func.mk` value capturing two fresh cells (`s`,
`md`). Three options:

- **(a) The exact closure value.** A Lean definition rebuilt from the generated `Server.wrapUnaryHandler`
  body, with the two cells substituted. Exact, but it is coupled to the generated text.
- **(b) A persistent WP spec of the closure.** New trusted text: what a run of the handler does, which the
  `Serve` axiom then assumes.
- **(c) Leave the handler existential.** Rejected: `Serve`'s axiom would then be false on states with
  other handlers. Its truth would rest on Go's visibility rules, which the semantics does not have.

I recommend (a), proved by `rfl` after `wp_func_lits`, once a build can check that the generated term
reduces.

### 3.2 Trusted statements that gain content when `grpcSrvNew` is defined (old text unchanged; meaning changes)

| statement | where `grpcSrvNew` is | effect | why it stays true |
|---|---|---|---|
| `grpc.Server.Serve.wp_proof` (via `grpcServeTok`'s first disjunct) | precondition | the claim gets weaker (fewer states) | none needed |
| `etcd_noRefusal`, `etcd_noOtherRefusal` | premise of the entailment | weaker | none needed |
| `grpc_health_v1.RegisterHealthServer.wp_proof` | pre and **post** | the post claims the definition's content for health's registration | the generated `RegisterHealthServer` is `s.RegisterService(&Health_ServiceDesc, srv)`, and `RegisterService` is proved over the same definition. Retirable by translating `grpc_health_v1`'s registration with its body. |
| `grpc_prometheus.ServerMetrics.InitializeMetrics.wp_proof` | pre and **post** (unchanged arguments) | the post claims the state is unchanged | `InitializeMetrics` only reads `server.GetServiceInfo()` (`services`, read-only) and registers its metrics. |
| `grpc.StatsHandler.wp_proof` | its post `grpcSrvOpt v (.stats h)`, if `.stats h` carries `⌜grpcStatsHandlerOk h⌝` (needed for the definition's stats-handler clause) | the post claims its own premise | trivially true |

## 4. Files SW2 also edits

None of `InvGrpcBase`, `InvGrpc`, `InvGrpcRun`, the handler specs or the adapters is edited here.
`createHeaderFields`' proof imports `InvGrpc` (for `perRPCCredsOk`/`credKeysOk`). If SW2 changes those
names, the merge touches `Proof/google_golang_org/grpc/{InvHeader,createHeaderFields}.lean`.
