# net/http's interim axioms for net/rpc over HTTP (rpc-driver), reviewed

**Axioms.** `net.http.Handle.wp_proof` (`Net/Proof/net/http/Handle.lean`, over `Net/Spec/net/http/Handle.lean`),
`net.http.Serve.wp_proof_rpc` (`Net/Proof/net/http/Serve.lean`), and `net.http.wp_init_first`
(`Net/Proof/net/http/InitFirst.lean`), over `Net/Proof/net/http/MuxDefs.lean` (`litPattern`, `muxOwn`,
`muxRoute`, `muxRpc`). All interim: retired by phase 7's S5 (`Handle`, `Serve`) and L2 step 6 (the
initializer).

**2026-11-25: `Handle.wp_proof` and `Serve.wp_proof_rpc` are theorems** (S5). `Handle.wp_proof` over the real
`ServeMux` (`MuxServe.lean`'s `wp_Handle_lit`); `Serve.wp_proof_rpc` from `Serve.specHandler` with the `nil`
handler (`ServeRpc.lean`'s `srvAddrH_nil_rpc`: `DefaultServeMux`'s routed `CONNECT` dispatch,
`wp_ServeMux_ServeHTTP_connect`, to the `rpcHjHandler` that `muxRpc` names; the address's protocols, head law
and `400` from `rpcLisP`), linked as `net.http.Serve.wp_rpc` over the two interim context axioms
(`context.WithValue.wp_proofPtr`, `context.WithCancel.wp_proofValBg`,
`notes/axiom-review/context-interim-hypotheses.md`). Neither spec's statement changed. Only `wp_init_first`
(restated, reviewed: `/shared/tmp/ps2/revinit/review.md`, #24 7150317814, 7153375148) stays an axiom here.

**2026-11-24: review by zeldovich-proving-2 (S5's owner) (#24 issuecomment-7135914632; Go test programs
under `/shared/tmp/ps2/s5/muxtest/`), against Go 1.27.3. Two statements found false, one premise missing.**

1. **`litPattern` admitted patterns Go does not treat as literal paths** (`Handle.spec`, `Serve.spec_rpc`).
   It was an exclusion list (`/`-initial, no `{`, `}`, `%`, space). `http.Handle("/a\tb", h)` panics:
   `parsePattern` splits a method off at a space *or tab*. And with `/a?b` registered, a `CONNECT
   /a?b` request is routed to `/a` (the query is not part of the path) and gets a 404, which the
   rpc handler contract (`respProto`) does not allow. **Fix:** `litPattern p := p.head? = some '/' ∧
   ∀ b ∈ p, pathByte b = true`, where `pathByte` is the model's `modelPathByte`
   (`models/net/http/textproto_model.go`): letters, digits and `- _ . ~ $ & + , / : ; = @`. No
   method, host, wildcard, escape or query. `litPattern_rpc` and `litPattern_debug` still hold
   (`decide`).
2. **`Handle.spec` admitted a nil `HandlerFunc`.** `http.Handle("/x", http.HandlerFunc(nil))` panics
   "http: nil handler" (the review's test program).
   **Fix:** the premise `h ≠ interface.mkOk net.http.HandlerFunc.ty #func.nil`. `Server.HandleHTTP`'s two
   calls discharge it: their handlers are a `*Server` and a `debugHTTP`.
   **2026-11-25: still false over the model** (S5, proving `register`; coordinator-E, #24 7152572897): a
   `HandlerFunc` interface holding a value `v` that is not a function value (`mkOk HandlerFunc.ty v`, `v ≠ #fv`)
   meets the premise, but `registerErr`'s `f == nil` (`GoOp GoEquals` on a function type) is stuck on it, so the
   axiom asserted a WP of a stuck program (adequacy: `False`). **Fix:** the premise `∀ v, h = mkOk HandlerFunc.ty
   v → ∃ fv : GoFunc, v = #fv ∧ fv ≠ func.nil` (ledger, 2026-11-25). The callers' handlers are pointer-typed, so
   it is vacuous for them.
3. **`wp_init_first` needs the thread bound of the mux's `RWMutex` reader-slot pools**
   (`threadBound_le_actualMaxReaders`). **Fix:** the premise `⌜threadBound GF ≤ 2 ^ 30⌝`.
   rpcdriver's boot discharges it. Its statement's step bound `rpcStepBound` was lowered from
   `2 ^ 31 - 1` to `2 ^ 30 - 1` (the bridge's `threadBound = receiptBound + 1 ≤ bound + 1`). This is a
   weaker statement, recorded in its `TopLevelDefs.lean`.

Other parts of the axioms: no other finding. S5's own `Serve.spec` will imply `Serve.spec_rpc`;
`MuxDefs` will be refined there (the reader-slot pools, `use121`).

**2026-11-24: `Serve.spec_rpc` was false for a path longer than the server's read limit** (found by
zeldovich-proving-2 while naming `readRequestLimit`'s errors, S5 batch 8; agreed on #24,
issuecomment-7139755664). The server reads a request with the limit `DefaultMaxHeaderBytes + 4096`
(`1 << 20` plus `bufio` slop, `Server.initialReadLimitSize`); net/rpc's `DialHTTPPath` sends
`"CONNECT " + path + " HTTP/1.0\n\n"`, so for a path beyond the limit the server answers
`431 Request Header Fields Too Large`, which the rpc handler contract (`respProto`) does not allow.
**Fix:** the premise `path.length ≤ 2 ^ 20` (the request line is then at most `2 ^ 20 + 19` bytes,
within the limit). rpcdriver discharges it for `/_goRPC_` (`net.rpc.defaultRPCPath_short`, `decide`).

**2026-11-25: `wp_init_first` restated, reviewed sound** (`/shared/tmp/ps2/revinit/review.md`, independent,
axiom-skill method; Go probe `/shared/tmp/ps2/revinit/gocheck/`; coordinator-E #24 7153375148). Its post is now
`initFirstRes` (`Net/Proof/net/http/InitFirst.lean`): the zero `defaultServeMux` (owned), `∃ b, use121 ↦□ b`,
`maxSlice ↦□ 8`, `serveEnv`, `ctxKeys`, `∃ tm, aLongTimeAgo ↦□ tm`, `wPools`, `rPool`; no `threadBound` premise.
`readEnv` is a lemma from `isPkgInit` (`readEnv_of_init`), and `wp_init_first_mux` (proved, through `muxOwnS_init`)
gives the old `muxOwn … []` and `httpSrvEnv`. Two caveats, recorded in the docstring:
1. The owned `defaultServeMux ↦ zero` is safe only while no other trusted spec writes the mux. A future
   standard-shape `wp_initialize'` axiom for a package whose initializer registers on `DefaultServeMux` (expvar,
   net/http/pprof, x/net/trace) would contradict it; such a package needs a first-init spec that consumes the mux.
2. The pools' predicates (`wPoolP`, `rPoolP`) are chosen by the axiom. That is sound only because the pool
   variables are untranslated and allocated inside their opaque initializers, so nothing else yields their
   points-to; translating them reopens the question.

**2026-11-25: httpdriver's interim axioms, reviewed** (zeldovich-proving-2, #24 issuecomment-7144119919;
go1.27.3 tests in their review). `ServeMux.HandleFunc.wp_proof`, `ReadResponse.wp_proof_resp` and the C6
departure (`HProto.respEnd`) sound. Five findings, fixed over S5's landed vocabulary (after the merge of
`lean`, the axioms are restated over `MuxDefs`' refined `muxOwn`/`muxRoute`):
1. **`Serve.wp_proof`: more than 500 header values (counting `Host`) get a `431`, then the connection
   closes** (`server.go:2087`, `maxHeaderValueCount`), not an answer `httpRespP` allows. **Fix:** `reqOk`
   requires `R.hdr.length + 1 ≤ 500` (`WireDefs.lean`).
2. **`ServeMux.ServeHTTP.wp_proof`: Go 1.22's mux redirects with `307`** (`StatusTemporaryRedirect`,
   `server.go:2743/2759/2768`), not `301` (only `httpmuxgo121=1`'s matcher answers `301`). **Fix:** `307` in
   `muxNoRoute`, and the axiom covers Go 1.22's matcher only: its precondition has `use121 ↦□ false`. Where it
   comes from (#18's option (a)): net/http's `initFirstRes` now ties `use121` to the setting (`∃ b, use121 ↦□ b
   ∗ ⌜b = true → godebugHttpmuxgo121 = "1"⌝`, what the approved trusted `init` model does: a strengthening of
   the reviewed `wp_init_first`, to re-review), and the top-level statement takes the environment premise
   `GodebugHttpmuxgo121Not1` (`HEnv`, baseline-listed as opaque in `etc/premise-witness-baseline.txt`).
3. **`ServeMux.ServeHTTP.wp_proof`: the trailing-slash redirect** happens exactly when the path is not a
   pattern, does not end in `/`, and `path ++ "/"` is a pattern, even when a shorter subtree pattern routes it
   (`/` and `/a/` registered: `GET /a` is `307`; `/a//` registered: `GET /a/` is `404`). **Fix:** `muxRedirect Ps
   p := ¬ pathClean p ∨ (p ∉ Ps ∧ p.getLast? ≠ some '/' ∧ p ++ "/" ∈ Ps)`, checked first (`findHandler`'s
   order); then the longest pattern the path is under; then `404`.
4. **`Serve.wp_proof`: `Pragma: no-cache` makes `readRequest` add `Cache-Control: no-cache`**
   (`request.go:1176`), so the handler's header map is not `R.hdr`. **Fix:** `Pragma` in `reqKeysOut`.
5. **`ServeMux.ServeHTTP.wp_proof` called directly: the fields the mux reads and writes were not in the
   precondition.** **Fix:** `srvReq` pins `RequestURI` (the path: never `"*"`), `Host`, `URL` (the URL of the
   path alone: no `Host`, no `RawPath`), the protocol (`HTTP/1.1`), and `servePre` the method (`methOk`: not
   `CONNECT`) and the owned `Pattern`, `pat`, `matches` (`reqMuxFields`).
Also, from the merge: `muxSh` no longer holds `DefaultServeMux ↦□ m` (which made `muxOwn m` unsatisfiable
for a mux of the program's own); `http.Handle`'s lemma takes it, and `muxOwn` carries `serveEnv` for it
(proofs only, no trusted text). `ServeMux.HandleFunc.wp_proof` stays an axiom for this review; it is provable
like `wp_Handle_lit` (`wp_register_lit`, `wp_mux121_handle`) and will be proved in the proof stage.

**2026-11-25: re-review of `f7b2807d4a`** (zeldovich-proving-2, #24 issuecomment-7155892191; go1.27.3 tests
on tundra, `/shared/tmp/ps2/revhttp2/`). The five findings above: fixed, each rerun against Go. `Serve` (user
handler), `HandleFunc`, `ReadResponse`, `wp_init_first`'s `use121` clause and the proof-only edits: sound;
`ServeMux.ServeHTTP` matched Go on 24,000 random cases outside the case below. One new finding, fixed:
- **N1, `ServeMux.ServeHTTP.wp_proof`: an empty segment of a literal pattern acts as a wildcard**
  (`routing_tree.go:69-72` keys it like a single wildcard: with `//` registered, `GET /a/` runs its handler and
  `GET /ab` gets a `307`; with `/a//b`, `GET /a/zzz/b` gets a `200`). **Fix:** the axiom takes
  `∀ ph ∈ L, litPattern ph.1 ∧ pathClean ph.1` (a premise only; `litPattern`, `Handle.spec`,
  `Serve.spec_rpc` unchanged). The driver's patterns `/echo`, `/status` are clean.
- **M1, wording:** `godebugHttpmuxgo121` is one constant, so `GodebugHttpmuxgo121Not1` is about every
  machine of a deployment: said so in its docstring and the statement's description.
With N1 fixed: `done: OK` from zeldovich-proving-2 (no further round).

**2026-11-25: proof stage, a gap the client proof hits (httpdriver proof agent; proposed, not applied).** The
client wraps each connection in `bufio.NewReader`, whose spec asks the stream's law `□ ∀ r, S r -∗
⌜r.length + 2 ^ 12 < 2 ^ 62⌝`; the stream's bytes are what `httpRespP` lets the server write, and nothing there
bounds an answer's head: `hdrView hs hc` only pins `hc` at the keys outside `srvKeys`, so `hc` may hold any
number of other keys with empty values, and the `srvKeys` values have no length bound; and `muxNoRoute` makes a
protocol accept the mux's `404`/`307` for every `hs`, so the driver's `P` cannot bound `hs` either. Related:
`ReadResponse.wp_proof_resp` reads a head of any size (the model's `modelReadMIMEHeader(r, math.MaxInt64)`)
through `bufio` over a `readerStreamNE` whose `Read` is specified only below `2 ^ 62` bytes, yet its
precondition has no length law: over a reader that fails past `2 ^ 62` bytes (it meets `readerStreamNE`) and a
stream the precondition allows (a head of `2 ^ 62` bytes is `respOk`), the asserted WP is false. Proposed
(each trusted text): (1) `ReadResponse.spec_resp` takes `(□ ∀ r, S r -∗ ⌜r.length + 2 ^ 12 < 2 ^ 62⌝)`, as
`bufio.NewReader` does; (2) `hdrsOk hs` (`WireDefs.lean`) adds `(hs.flatMap hdrLineWire).length ≤ 2 ^ 21` (a
handler's committed header block; the mux's own `307` carries a `Location` of a path of at most `2 ^ 20`
bytes); (3) `respFacts` (`ProtoDefs.lean`) adds, for `.ans ρ`, `(respHeadWire ρ.st ρ.reason ρ.hc).length ≤
2 ^ 22`, and the same for `.chunked st reason hc` (Go's server writes the status line, at most 46 bytes, the
handler's lines, and its own `Date`, `Content-Type`, `Content-Length`, `Connection`, `Transfer-Encoding`
lines, under 512 bytes). And one driver change, not trust: the client's loop leaves a connection after a
`400` (`resp.StatusCode == http.StatusBadRequest`, the server closes it), not only after its junk request:
after a close-delimited answer whose body ended early (a cut connection), the reader's bytes are a prefix of
the `400` answer that no further `ReadResponse` precondition covers.
