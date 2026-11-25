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
