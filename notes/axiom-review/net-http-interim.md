# net/http's interim axioms for net/rpc over HTTP (rpc-driver), reviewed

**Axioms.** `net.http.Handle.wp_proof` (`Net/Proof/net/http/Handle.lean`, over `Net/Spec/net/http/Handle.lean`),
`net.http.Serve.wp_proof_rpc` (`Net/Proof/net/http/Serve.lean`), and `net.http.wp_init_first`
(`Net/Proof/net/http/InitFirst.lean`), over `Net/Proof/net/http/MuxDefs.lean` (`litPattern`, `muxOwn`,
`muxRoute`, `muxRpc`). All interim: retired by phase 7's S5 (`Handle`, `Serve`) and L2 step 6 (the
initializer).

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
3. **`wp_init_first` needs the thread bound of the mux's `RWMutex` reader-slot pools**
   (`threadBound_le_actualMaxReaders`). **Fix:** the premise `⌜threadBound GF ≤ 2 ^ 30⌝`.
   rpcdriver's boot discharges it. Its statement's step bound `rpcStepBound` was lowered from
   `2 ^ 31 - 1` to `2 ^ 30 - 1` (the bridge's `threadBound = receiptBound + 1 ≤ bound + 1`). This is a
   weaker statement, recorded in its `TopLevelDefs.lean`.

Other parts of the axioms: no other finding. S5's own `Serve.spec` will imply `Serve.spec_rpc`;
`MuxDefs` will be refined there (the reader-slot pools, `use121`).
