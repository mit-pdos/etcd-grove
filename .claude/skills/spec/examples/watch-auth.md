# `watcher.Watch` with auth on (G2, 2026-10-29 to 10-30)

The client's `w.Watch(ctx, key, opts...)` (`client/v3/watch.go`): a proved spec, written before auth
existed, that had to learn that each response with events was authorized by the server's check of
the watch's create. The fact comes only from trust-boundary axioms (grpc's stream metadata, the
watch's stream key, the stream's context), so the question was where those axioms go. The full
approved design is `notes/g2-watch-auth.md`; the rounds, `notes/authkv-main-plan.md`, "G2".

## The first version

```lean
abbrev watcher.Watch.spec : Prop :=
  ∀ (w : Loc) (γ : KVNames) (ctx : GoInterfaceOk) (ctx_desc : context.ContextDesc (IProp GF))
    (key : GoString) (opts_sl : GoSlice) (opts : List (OpFull → OpFull)) (rev : w64)
    (Q : KVState → IProp GF) (A : WAuth GF) (n : Nat),        -- the watcher's auth, a bound
  {{ isPkgInit … ∗ isKvWatcherA w γ A ∗ context.isContext ctx ctx_desc ∗ optsAt opts_sl opts ∗
      ⌜(opWatchModel key opts).isRangeWatch rev = true ∧ …⌝ ∗ A.pubLb n ∗ □ (AU …) }}
    w.Watch ctx key opts_sl
  {{ (ch : Loc) (γw : EtcdWatchNames), RET #ch;
      isSpsc γw.spsc ch (watchStateElemA γw (opWatchModel key opts) Q
        (watchAuthedC A ctx n (opWatchModel key opts))) (fun _ => True) ∗ … }}
```

`watchAuthedC` said the stream's metadata was the watch's own context's, with a new server-side
`watchAuthed` beside the existing one.

## The review rounds and the user's choices

1. **Round 1** (reviewer): the stream a watch joins was opened by *another* context with the same
   stream key, so its metadata is that context's (`streamKeyFromCtx`, which collides:
   `issues/etcd-watch-stream-key-collision.md`); the attempt relation must include the client's
   interceptor; the bound must travel per create; an auth fact already existed (A4's
   `watchAuthed`), so strengthen it rather than add one. **The user**: the full design (keep the
   refused watch); from-key ranges through a general Perennial lemma, not a scope cut; a
   single-member gate rather than a multi-member design.
2. **Round 2** (reviewer): a strengthened axiom was false as written (the interceptor's
   `withVersion` adds a header); the stream's context `WithCancel(&valCtx{inctx})` was unrelated to
   the watch's; the stream key's model did not typecheck, and its axiom claimed a return at a nil
   context (a bug in the trust base: `notes/audit.md`); the gate's environment had no source; the
   token binding needed the mode gate. **The user** (the decisive one): **strengthen the axioms in
   place, under their names**, though they sit under the proved `Watch` and so under every watch
   collection. The `WithTimeoutBackgroundMd` split (a separate trust-boundary spec) is not
   available: it needs a second proof of `Watch`, which one spec per function forbids. And the
   stream context's law as a strengthening of the existing local axiom, with the general fix
   proposed to Perennial.
3. **Round 3** (reviewer): the server's stream-interceptor contract let the handler see another
   context; `dialOk` admitted a dial with no stream interceptor, where the strengthened `NewStream`
   is false. **The user** approved both repairs (two more in-place strengthenings), then the table.

## The approved spec

```lean
abbrev watcher.Watch.spec : Prop :=
  ∀ (w : Loc) (V : WEnv GF) (γ : KVNames) (ctx : GoInterfaceOk)
    (ctx_desc : context.ContextDesc (IProp GF)) (key : GoString) (opts_sl : GoSlice)
    (opts : List (OpFull → OpFull)) (rev : w64) (Q : KVState → IProp GF) (n : Nat),
  {{ isPkgInit … ∗ isClientWatcher V w ∗ ⌜V.kst = γ.st⌝ ∗
      context.isContext ctx ctx_desc ∗ optsAt opts_sl opts ∗
      ⌜(opWatchModel key opts).isRangeWatch rev = true ∧ ¬ opWatchPanics key opts ∧
        1 ≤ sint.Z rev⌝ ∗
      □ (⌜V.nm = 1 ∧ 0 < n⌝ → authPubLbM (V.mem 0).2.E.authMode n) ∗
      □ (AU <{ ∃∃ σ, etcdKV γ σ }> @ (⊤ \ ↑srvRaftN) \ ↑kvN, ∅ <{ etcdKV γ σ, COMM □ Q σ }>) }}
    w.Watch ctx key opts_sl
  {{ (ch : Loc) (γw : EtcdWatchNames), RET #ch;
      isSpsc γw.spsc ch (watchStateElem γw (opWatchModel key opts) Q
        (□ (⌜V.nm = 1⌝ → watchCheckOk (V.mem 0).2.γ (V.mem 0).2.s V.conn
          (GoInterface.ok ctx) n (opWatchModel key opts).key (opWatchModel key opts).rangeEnd)))
        (fun _ => True) ∗
      spscConsumer γw.spsc [] ∗ monoListIdxOwn γw.cur 0 (rev - W64 1) }}

def watchCheckOk (γ : mvcc.WsNames) (s conn : Loc) (ctx : GoInterface) (n : Nat)
    (key rangeEnd : List w8) : IProp GF :=
  iprop(∃ (m md : GrpcMd),
    ⌜streamKeyOf m = streamKeyOf (metadata.outgoingOf ctx) ∧ clientAttemptMdOf conn m md⌝ ∗
    v3rpc.watchAuthed γ s (auth.mdTokenOf md) n key rangeEnd)
```

The trusted table it rests on lists six axioms, each strengthened in place and each with its
collections. They are `NewStream`, `NewClient`'s `dialOk`, `serveStream`, the stream interceptors'
contract, `streamKeyFromCtx` with two laws, and `WithCancelValCtx`.

## What it teaches

- When a proved spec needs a fact only an axiom gives and the spec has one proof, the
  trust-boundary split cannot apply. Strengthen in place, list the collections that now rest on the
  stronger axiom, and put it to the user (PRINCIPLES, "One spec per function").
- A gate is written in the triple, over an environment the caller names (`V`), never behind a
  predicate that hides it (`isKvWatcher`).
- An auth fact is stated over the token, with the binding gated on the mode; the transport's
  metadata is mapped to a token at the boundary, as the unary specs do.
- Before strengthening an axiom, check what it admits beyond the code's own uses: here `dialOk`
  admitted a dial with no interceptor, and the strengthened claim was false there.
