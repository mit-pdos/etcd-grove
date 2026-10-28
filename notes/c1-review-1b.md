# Review: C1 phase-1 statements (auth-e3zc, b6bc7e2a56)

Reviewed read-only at /shared/etcd-grove-e3zc (b6bc7e2a56), against `.claude/skills/spec/PRINCIPLES.md`,
`examples/put.md`/`range.md`, `notes/c1-plan.md`, the Go sources in /shared/etcd-grove/.lake/go-src/etcd,
and grpc-go from memory (no checkout; marked where uncertain). I did not reopen the phase-0 decisions
(the faithful chain, the refresh path in scope, the anonymous client out of scope), gate (A), or the
credentials axioms (1).

No new Go bug found. The relevant existing issue is `issues/etcd-auth-token-md-empty.md`; finding F2
contradicts the claim that issue relies on ("grpc's transports never put a key with no value").

---

## A. False statements: false of Go/grpc, or not provable as stated

### F1. The `Authenticate` handler writes its request, but `pbAuthenticateRequest` makes it read-only. `etcd_kv_auth_served_onA` cannot be proved
- **Where**: `Proof/go_etcd_io/etcd/client/v3/InvClientAuth.lean:62-72` (`pbAuthenticateRequest`: `recv` gives
  `Name ↦□`, `Password ↦□`, and there is no `recvOwn`). This model is used by `AuthnServedOn.lean:69`
  (`etcd_kv_auth_served_onA`, `isGrpcRpc addr authnMethod (etcdAuthenticateSpec γa)`).
- **Evidence**: `server/etcdserver/v3_server.go:845-849`: `defer func() { if r != nil { r.Password = "" } }()`
  (the CVE-2021-28235 fix). The handler writes the decoded request's `Password`, and a write needs an
  exclusive points-to. `ProtoMsg.recvOwn` exists for exactly this case: `InvGrpc.lean:80-83`, with the
  precedent `AuthUserAddRequest` at `InvAuthConn.lean:84`.
- **Who it breaks**: the phase-2 proof of `etcd_kv_auth_served_onA`, and with it `authTokReg_of`'s
  premise, and so C1's source.
- **Fix**: `recv r m := ⌜r ≠ null⌝ ∗ Name ↦□ m.1`, and
  `recvOwn r m := structFieldRef AuthenticateRequest "Password" r ↦ m.2`. `CheckPassword` reads the
  password before the deferred write, from the owned points-to. `send` does not change.

### F2. `grpcAttemptMd` is false when the outgoing metadata has a key with no values
- **Where**: `Proof/google_golang_org/grpc/InvGrpc.lean:888-890` (with `mdMergeAt`, `:865-869`).
- **Evidence**: grpc-go's `createHeaderFields` writes one header field per value
  (`for _, v := range vv`). A key whose value list is empty produces no header field, so the server's
  `operateHeaders` never creates the key. The model's `mdMergeAt cm out k` with `cm` silent at `k` and
  `out k = some []` says the handler sees `some []`.
- **Scenario**: the context carries `metadata.NewOutgoingContext(ctx, MD{"token": {}, "authorization": {"Bearer X"}})`
  and the bundle holds `""`.
  - Real handler: `token` is absent, so `AuthInfoFromCtx` reads `authorization` and gets `X`.
  - Model: `mdGet md "token" = some []`, so `auth.mdTokenOf md = none` (`KVServiceOn.lean:43`).
  - The real `md` therefore does not satisfy `grpcAttemptMd`. `grpcInvokerOk` (and so the
    `ClientConn.Invoke` axiom) gives the handler's `Spec` only at metadata that does, so the axiom is
    false for this context.
  - `outgoingOf` is opaque, so nothing excludes such a context.
- **Fix**: compare value lists and state that grpc never delivers an empty list:
  `∀ k, ¬reserved k → mdVals md k = mdVals cm k ++ mdVals (outgoingOf ctx) k`, plus
  `∀ k, mdGet md k ≠ some []`. The second conjunct is also what `issues/etcd-auth-token-md-empty.md`
  says of real transports. `mdMergeAt` and its three-way match then go away.
  `clientAttempt_tok` (`ClientUser.lean:83`) re-proves with the non-emptiness conjunct.

### F3. grpc lowercases the credentials' keys; `credsMapIs` does not
- **Where**: `InvGrpc.lean:953-956` (`credsMapIs`), `:960-968` (`perRPCCredsOk`), `:977-981`
  (`connCredsOk`). The `NewClient` axiom ties them together: `Spec/google_golang_org/grpc/NewClient.lean:34-45`.
- **Evidence**: grpc-go `http2Client.getTrAuthData` does `k = strings.ToLower(k); authData[k] = v` for
  every credentials' pair before writing the header fields. `credsMapIs` takes the map's keys raw.
- **Scenario**: credentials whose `GetRequestMetadata` returns `{"Token": "x"}`, with
  `Q cm := ⌜mdGet cm "token" = none⌝`.
  - `Q` holds of the raw map, and `perRPCCredsOk pc Q` is provable.
  - `connCredsOk` then gives `credsYield conn cm → Q cm`, and `grpcAttemptMd` says the handler's
    `token` values are only the context's.
  - grpc actually sends `token: x` first.

  This is harmless for etcd's credentials (key `rpctypes.TokenFieldNameGRPC = "token"`), but the
  axiom is generic.
- **Fix**: add `⌜∀ k v, m !! k = some v → metadata.lowerKey k⌝` to `credsMapIs`'s map case. It is
  trivially true of etcd's `{"token": t}`, and the `GetRequestMetadata` axiom's post already pins the key.

### F4. `NewClient` calls `pc.RequireTransportSecurity()`, which `perRPCCredsOk` says nothing about
- **Where**: `NewClient.lean:40` (premise `perRPCCredsOk pc Q` only); `InvGrpc.lean:960`.
- **Evidence** (grpc-go, from memory, high confidence): `ClientConn.validateTransportCredentials`
  iterates `dopts.copts.PerRPCCredentials` and calls `cd.RequireTransportSecurity()` when the transport
  credentials are insecure. This is etcd's case with no TLS (`dialSetupOpts` uses
  `insecure.NewCredentials()`, `client.go:244`). `newHTTP2Client` calls it again for each transport.
- **Scenario**: a `pc` whose `GetRequestMetadata` meets `Q` but whose `RequireTransportSecurity`
  panics or diverges satisfies the premise, yet grpc's `NewClient` panics. The axiom's triple is false
  for it.
- **Fix**: add to `perRPCCredsOk` a persistent `{{True}} pc.RequireTransportSecurity() {{ b, RET #b; True }}`.
  etcd's is `return false` (`credentials.go:66`). Translate it: add
  `"perRPCCredential.RequireTransportSecurity"` to `Code/go_etcd_io/etcd/client/v3/credentials.toml`'s
  `translate`; it takes no lock. That avoids a third axiom.

### F5. The interceptor's contract is false on the refresh path for a context whose `Err()` is not a client error (finding 3; the `getToken` axiom it replaces was false too)
- **Where**: `Spec/.../Client__unaryClientInterceptor.lean` (post `etcdInterceptorOkG`, which unfolds
  to `etcdInterceptorOk`, `InvKVConn.lean:815-829`: pre `ctxOk` only, error post `clientErr err`). The
  hole is at `Proof/.../Client__unaryClientInterceptor.lean:405`.
- **Evidence**: the refresh path's error is returned as is.
  - `retry_interceptor.go:107-117`: `gtErr := c.refreshToken(ctx); … return gtErr`.
  - `getToken` returns `Authenticate`'s error (`client.go:297-303`).
  - `authClient.Authenticate` returns `ContextError(ctx, err)` (`auth.go:138`).
  - On a status `Canceled`/`DeadlineExceeded` with `ctx.Err() != nil`, that returns `ctx.Err()`
    (`client.go:615-624`).
  - Perennial's `isContext` lets `Err()` return any non-nil typed error
    (`.lake/packages/perennial/Perennial/Proof/context/Base.lean:492-512`, `"#HErr"`/`"#HErrDone"`).
  - So a context in the model whose `Err()` is, for example, a wrapping error (not
    `errors.isLeafError`) makes the post's `clientErr err` false. The scenario: the server answers
    `ErrInvalidAuthToken`, the refresh's `Authenticate` runs while the caller's context is cancelled,
    and the call returns that context's own error.
  - The old `getToken` axiom (pre `ctxOk`, post `clientErrOk`) was false in the same way.
- **Fix**: the plan's option. Add `ctxErrClient ctx cd` to `etcdInterceptorOk`'s pre; the retry
  clients' callers (`kv.Put`, …) already hold it, and `withVersion` keeps it. For `newClient`'s own
  timeout context (hole at `newClient.lean:313`), `clientCfgOk` already fixes `cfg.Context = nil`
  (`InvClientNew.lean:208`). So the context is `WithTimeout(WithCancel(TODO))`, whose `Err()` is
  `Canceled`/`DeadlineExceeded`. Derive it from Perennial's `WithCancel`/`WithTimeout` specs if they
  say so; otherwise add a pure premise.
- **Stale docstring**: `InvGrpc.lean:828-833` (`ctxOk`) still says `getToken`/`refreshToken` are
  stated for `ctxOk`; they now take `ctxErrClient`.

---

## B. Quality (the statements are true or are scope choices; these are cost or abstraction issues)

### Q1. `New`'s post states the mechanism (per-RPC credentials) rather than C1 at `P`. Abstraction principle: "the spec of an API, not of an implementation"
- **Where**: `InvClientAuth.lean:341-345` (`clientTokAt` contains `connTokOk conn P`, `:296`, which
  unfolds to grpc's `credsYield` and the credentials' `tokMdOk`), in the posts of
  `Spec/.../New.lean` and `newClient.lean`.
- **Why**: a client that adds the token through an interceptor or the outgoing context, instead of
  per-RPC credentials, would satisfy C1 but not `connTokOk`. The caller (`Work`) also has to go
  through `clientAttempt_tok` (`ClientUser.lean:80`) to reach the attempt-level fact. `New`'s post
  couples to two other packages' internals (grpc's `credsYield`, the credentials' key name `token`).
- **Fix**: `clientTokAt cl eps P := ∃ api conn, cl.KV ↦□ … ∗ kvObjAtC api conn eps ∗ attemptTokOk conn P`, where

  ```
  attemptTokOk conn P := □ ∀ ctx md, ⌜clientAttemptMd conn ctx md⌝ -∗
    (∃ t, ⌜auth.mdTokenOf md = some t'⌝ ∗ □ P t) ∨ ⌜auth.mdTokenOf md = auth.mdTokenOf (outgoingOf ctx)⌝
  ```

  (`t'` is `t`, or its trimmed form, see Q2). `connTokOk` and `clientAttempt_tok` then become
  `newClient`'s internals, and `userClientAt conn γa u` is `attemptTokOk conn (tokIssued γa · u)` by
  definition. `userClientAt_of`/`clientTokAt_user` reduce to an instantiation.

### Q2. C1 carries `strings.trimPrefix t "Bearer "`: it does not say the handler sees the issued token
- **Where**: `ClientUser.lean:69-74` (`userClientAt`).
- **Why**: `Work` needs the grant at `mdTokenOf md` to be about a token issued to `u`. As stated it is
  about `trimPrefix t`, so `Work` needs a fact that the plan defers ("An obligation for Work").
- **What Go guarantees**: neither etcd provider can produce a token starting with `"Bearer "`.
  - Simple tokens are 16 random ASCII letters, then `.<index>`, so there is no space.
  - JWTs are base64url segments joined by dots, with no space.
- **Fix**: export from auth a law `auth.tokIssued γa t u ⊢ ⌜strings.trimPrefix t "Bearer " = t⌝`, by
  constraining `tokShape`'s prefix (no space). Then state C1 as `mdTokenOf md = some t`.

### Q3. `kubernetes.New` takes `P` only in its precondition
- **Where**: `Spec/go_etcd_io/etcd/client/v3/kubernetes/New.lean`. `P` and `clientAuthPre cfg eps P`
  are in the pre; the post drops `clientTokAt`.
- **Why**: "a parameter that appears only in a precondition, chosen by the caller per call,
  constrains nothing." Also, "prefer the stronger spec": `kubernetes.New` is `clientv3.New` wrapped,
  so its user client could have C1 too.
- **Fix**: add `clientTokAt cl eps P` to the post (one more conjunct from `New`'s post). Otherwise
  quantify `∃ P` inside the premise.

### Q4. Missing laws: callers unfold other packages' definitions
- `clientAuthPre` is unfolded at `examples/common/NewClients.lean:55` and
  `examples/k8setcd3/Main.lean:196` (`iunfold clientAuthPre; ileft; …`). Add
  `clientAuthPre_anon : cfg.Username' = "" ∨ cfg.Password' = "" → ⊢ clientAuthPre cfg eps P`.
- `tokenBundleInv` is unfolded at `Proof/.../Client__dial.lean:95`, because
  `perRPCCredentialBundle.PerRPCCredentials.spec` takes the bundle's fields (`b.rc ↦□ rc ∗ credTokInv rc P`)
  rather than the package's predicate. Fix: pre
  `tokenBundleInv (interface.mkOk (ptr perRPCCredentialBundle) #b) P`. Then `credTokInv` and the
  `authToken` field stay inside the credentials package.
- `credsOfDial` and `kaOpts` are unfolded at `Client__dial.lean:168-171`. Add `credsOfDial_append`
  and per-descriptor `credsOf` simp lemmas, as `unaryIcsOf_*` has (`InvDial.lean:100-110`).

### Q5. Stale or dead vocabulary ("after a change, drop what existed only for what it changed")
- `tokenBundleAt` and `tokenBundleInv_at` (`credentials/Defs.lean:38`, `:85`) are no longer used by
  any spec or proof.
- `NewPerRPCCredentialBundle.spec`'s docstring still says "a token bundle (`tokenBundleAt`)".
- The `credsYield` docstring refers to a lemma `credsYield_ok` that does not exist (`InvGrpc.lean:879`).
- `grpcReservedKey` (`InvGrpc.lean:870-875`) says every `grpc-` key is "set by grpc itself". grpc's
  `isReservedHeader` lists only some `grpc-*` keys, and others are forwarded. The broader predicate is
  sound (it states less), but the docstring should give that as the reason, and say what grpc
  actually delivers at those keys (the margin).

### Q6. The thread bound the `GetRequestMetadata` axiom assumes could be a premise rather than a hidden assumption
- **Where**: `Proof/.../credentials/perRPCCredential__GetRequestMetadata.lean` ("true of Go below
  RWMutex's 2^30 concurrent readers").
- **Why**: within decision (1), the assumption can be stated rather than buried. Readers are
  goroutines: grpc calls it in the attempt's goroutine. The repository bounds goroutines with
  `threadBound GF`, but `New`'s premise is `threadBound GF ≤ 2^31`, which does not imply fewer than
  2^30 readers.
- **Fix**: give the axiom (and `PerRPCCredentials.spec`) a pure premise `⌜threadBound GF < 2^30⌝`. It
  fits `perRPCCredsOk`'s `{{True}}` because it is pure and closed over before the triple, and is
  discharged from a tightened `New` premise. The axiom then rests on nothing unstated.

### Q7. `P` is a caller-chosen predicate parameter (TaDa vs HoCAP); acceptable, but say so
- `tokenBundleInv atb P`, `credTokInv rc P`, `clientAuthPre cfg eps P` and `clientTokAt cl eps P`
  thread `P` through about 10 specs.
- I think it is justified: the client does not know the server's ghost names, and `P` is fixed once
  per bundle at creation. A TaDa alternative (a ghost set of stored tokens) would still need the
  client's invariant "every stored token is issued to `u`", established at insertion, so it is no
  simpler.
- Record it as a knowing departure in `notes/c1-plan.md` or the file header.

### Q8. Minor redundancy and leftovers
- `getToken.spec` and `refreshToken.spec` take both `retryClientOk c` and `clientReady c conn eps`.
  `clientAuthAt` repeats the `Token` and `authTokenBundle` points-tos of `retryClientOk`.
  `Client.dial.spec` likewise repeats `authTokenBundle ↦□`. Agreement makes this harmless, but it is
  size. `clientAuthAt` could absorb `retryClientOk`'s `tok ≠ "" → atb ≠ nil` and replace it in these two
  specs (both internal).
- `connCredsOk`'s `_ => True` for two or more credentials is documented, and fine.
- `clientTokAt` repeats `cl.KV ↦□`, which `isNewClient` also holds. The plan wanted `isNewClient` to
  carry the fact. Keeping it separate is fine, since `kvObjAtC_agree` exists (`InvKVConn.lean:1062`).

### Q9. A user client needs an auth-on member (a mode split, temporary)
- `etcdAuthenticateSpec` and `etcd_kv_auth_served_onA` exist only for `E.authMode = .on γa`, beside
  the unchanged `etcd_kv_auth_served_on`. The header says this is temporary.
- Consequence: `New` with a user name needs `authTokReg`, which only an auth-on member provides. A
  user client of an auth-off member cannot be built, although Go handles that case
  (`ErrAuthNotEnabled` makes `UpdateAuthToken("")`).
- Fix: when the handler is proved, give one registration for every mode. With auth off, no reply is
  ever a token, so `Spec m Φ := True` meets `authTokReg` at any `P`.

### Q10. The watch path's `getToken` is outside the gate (uncertain; noted, not a defect of these statements)
- `streamClientInterceptor` calls `c.getToken(ctx)` on every stream (`retry_interceptor.go:139-146`).
  Its effect lives in the `ClientConn.NewStream` axiom, which assumes the stream interceptor is etcd's,
  and that axiom requires neither readiness nor the `Authenticate` registration.
- It is consistent with `credTokInv`: whatever a real `getToken` stores is an `Authenticate` reply,
  which `authTokReg` makes meet `P`. But the axiom's truth now silently relies on the gate's
  precondition (`c.Auth` set). Say so in that axiom's docstring.
- Also uncertain, low: grpc-go transports once copied the deprecated `resolver.Address.Metadata` into
  every stream's headers (`t.md`). etcd's resolver sets none, and `NewClient` only accepts etcd's
  resolver (`grpcResolverAt`), so `grpcAttemptMd` is unaffected. Check this in phase 2 with the grpc
  source.

---

## C. Checked and found fine

- **`grpcAttemptMd`'s main claim, apart from F2 and F3**: the credentials' values first, then the
  context's outgoing ones, at every non-reserved key. This is `createHeaderFields`'s order
  (`authData`, then `callAuthData`, then `FromOutgoingContext`); the server appends header values in
  order. There are no per-call credentials (`grpcOptOk` admits only scalar and peer options), and
  `GetRequestMetadata` is called per attempt (per transport stream).
- **The over-approximation**: `credsYield conn cm` is any yield on the connection rather than this
  attempt's. Since `grpcInvokerOk` quantifies `∀ md`, this is sound.
- **`connCredsOk []`**: with no credentials, grpc's `getTrAuthData` returns `nil`.
- **`WithPerRPCCredentials.spec`, `.perRPCCreds pc`, `credsOfDial`**: true, and `dialOk_perRPCCreds`
  and `unaryIcsOf_perRPCCreds` adjust correctly.
- **`tokMdOk`**: the right shape of etcd's map (`credentials.go:67-75`).
- **The `GetRequestMetadata` and `UpdateAuthToken` axioms' content**: true of the Go code, given F3's
  key and Q6's bound. `nil, nil` is returned for `""`, and `UpdateAuthToken` is one store under the
  write lock. The bundle's `UpdateAuthToken.spec` is also fine: post `True`, and the `rc == nil` branch
  is harmless.
- **`NewPerRPCCredentialBundle.spec` at any `P`**: the token starts at `""`.
- **`getToken.spec`, apart from F5**: every Go branch is covered.
  - `c.Token != ""` uses `retryClientOk`'s `tok ≠ "" → atb ≠ nil` together with `clientAuthAt`'s
    `□ P tok`.
  - The `Username`/`Password` empty case is right: `client.Username` is set only when both are
    non-empty (`client.go:409-413`).
  - On `ErrAuthNotEnabled`, `UpdateAuthToken("")` needs `atb ≠ nil`, which `clientAuthAt`'s third
    conjunct gives.
  - The reply token keeps the invariant through `authTokReg`'s persistent `□ ▷ Spec (u,pw) (□ P ·)`.
    It is persistent, so retries and repeated refreshes do not spend it (the once-only principle).
- **`refreshToken.spec`**: correct, including `nil` with no bundle.
- **The readiness gate (A), as realized**:
  - `clientReady` hides `P` existentially, so the interceptor's contract does not mention `P`.
  - `etcdInterceptorOkG` and `isEtcdConnG` are consistent, with `isEtcdConnG_ready` giving the
    ungated form.
  - `getToken`'s `▷ isEtcdConn` fits the Löb proof.
  - It is faithful to Go: no RPC is made between the dial and `client.Auth = NewAuth(client)`
    (`client.go:448-461`). `isEtcdConn` and its users are unchanged.
- **The structural constructors**: `NewKV`, `NewAuth`, `NewLease` and `NewLeaseFromLeaseClient` with
  `clientKVAtS`/`kvObjS`/`authObjS`/`lessorAtS` and the `*_of` laws are true. Their only caller is
  `newClient` (I checked with grep). Optional: add a `clientKVAt_split` (⊣⊢) like `authObjAt_split`.
- **`dialSetupOpts`, `dial`, `dialWithBalancer`**: true. `connTokOk` follows from `connCredsOk` in
  both cases (`connTokOk_none`, `connTokOk_one`), and the glue in `Client__dial.lean` is about one
  step per call.
- **The three `Authenticate` specs** (`authClient`, `retryAuthClient`, the generated stub): true.
  - `(*AuthenticateResponse)(resp)` is the same pointer.
  - `ContextError`'s results are client errors given `ctxErrClient`; an `EtcdError` is admitted by
    `clientErr`.
  - `resp = nil` on error.
  - The persistent `□ ▷ Spec` is needed: the retry interceptor may make several attempts.
- **`etcdAuthenticateSpec`'s content (apart from F1)**: true of `EtcdServer.Authenticate`
  (`v3_server.go:837-887`).
  - The internal request carries `Name: r.Name`, and the apply's `authStore.Authenticate` assigns the
    token to that name.
  - The stale-revision loop returns the last token, which is also issued to `r.Name`.
  - A wrong password, a deleted user or auth off are all errors.
  - `authTokReg_of` is right.
- **`userClientAt` and `clientAttempt_tok`'s logic (apart from F2 and Q2)**: the credentials' token
  comes first, so the server's `ts[0]` is the bundle's when it holds one; otherwise the token is the
  context's own. `withVersion`'s `client-api-version` key does not interfere.
- **The disjunction is not vacuous**: its weak side is false whenever the context carries no token,
  which `Work` assumes.
- **Fit with the consumer**: `ResultsOn.lean`'s `∃ md, ⌜clientAttemptMd conn ci md⌝ ∗ …` matches
  `userClientAt`'s `∀`, and `clientTokAt` gives the `kvObjAtC api conn eps` that `client_*_on` take.
- **The callers adapt**: `NewClients.lean` and `k8setcd3/Main.lean` change by about 3 lines each
  (apart from Q4's unfold).

---

## D. Targets ranked by need of revision

1. **grpc trust boundary** (`InvGrpc.lean`'s `grpcAttemptMd`/`mdMergeAt`/`credsMapIs`/`perRPCCredsOk`;
   `NewClient.lean`). F2, F3 and F4 are three ways the generic axiom is false. The fixes are local:
   value lists with non-emptiness, lowercase keys, and `RequireTransportSecurity` in the contract.
2. **`Authenticate`'s request model and `etcd_kv_auth_served_onA`** (`InvClientAuth.lean:62`,
   `AuthnServedOn.lean`). F1 blocks the phase-2 proof. Q9 (one registration for every mode) is later.
3. **The retry interceptor's contract and `newClient`'s token fetch** (`Client__unaryClientInterceptor`,
   `etcdInterceptorOk`). F5 needs `ctxErrClient` in the contract; also fix the stale `ctxOk` docstring.
4. **`New`, `newClient`, `kubernetes.New` posts and premises** (`clientTokAt`, `clientAuthPre`). Q1
   (state C1 at `P`, not `connTokOk`), Q3 (`P` only in the pre), and Q4's `clientAuthPre_anon`.
5. **`ClientUser.lean`'s `userClientAt`**. Q2 (the `"Bearer "` trim; needs an auth law).
6. **The credentials package** (`Defs.lean`, `PerRPCCredentials.spec`, the two axioms). Q4 (take
   `tokenBundleInv`), Q5 (dead `tokenBundleAt`), Q6 (the reader bound as a premise).
7. **`getToken`, `refreshToken`, `dial*`, the structural constructors, and the three `Authenticate`
   specs**. Fine apart from F5 and Q8's redundancy.
