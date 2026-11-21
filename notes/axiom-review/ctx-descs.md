# ContextReadErrs.descs and other cross-world entailments (2026-11-17)

Reviewed on branch `axiom/ctx-descs` (off `lean` `3cd4b72599`), by the ctx-descs agent of
etcd-grove-03. Lean file: `Proof/github_com/mit_pdos/etcd_grove/examples/axiomcx/ctxdescs/CrossWorld.lean`
(checked with `etc/lean-check.py -a`, no errors; not on `lean`).

## Targets

- `EtcdGrove.ContextReadErrs.descs` (premise class field,
  `Proof/go_etcd_io/etcd/server/v3/etcdserver/read/Init.lean:82`):
  `isPkgInit context ⊢ (∃ e, Canceled ↦□ e ∗ ⌜errDesc e = "context canceled"⌝) ∗ (∃ d,
  DeadlineExceeded ↦□ d ∗ ⌜errDesc d = "context deadline exceeded"⌝)`.
- The claim to check: `descs` with the trust base proves `False`, by (1) carrying `descs` to every
  location, (2) mvcc's `ErrFutureRev` and the axiom `v3rpc.toGRPCErrorMap_init`, which gives it the
  mvcc description, (3) the contradiction.
- The family: every entailment, persistent law, instance field or premise that concludes a pure
  fact about an opaque function of a pointer value from persistent points-tos.

## Verdict

- **The claim as stated (`False`) is refuted: step 2 breaks.** Step 1 holds (it is the same transfer
  as the theorem below, over a larger world). But the mvcc fact is not an entailment. It is the
  postcondition of a triple about `toGRPCErrorMap.init`, which is an uninterpreted
  `axiom … : val` (`Code/…/v3rpc.lean:281`). A postcondition becomes a Lean fact only through an
  execution that returns, and no semantics defines how `toGRPCErrorMap.init` executes. A model in
  which it diverges satisfies every triple about it. So `ContextReadErrs` and the trust base are
  consistent as far as this argument goes. What follows instead is formal, and just as bad
  (below): under `descs`, v3rpc's initializer never returns.
- **`descs`'s `Canceled` half is unsound as a premise** (confirmed in meaning, step 1 argued). Read
  over all resources, it says that every `*errors.errorString`, at every location, has the
  description `"context canceled"` (`CanceledDescConst`). With the trust-base axiom
  `toGRPCErrorMap_init`, the call that v3rpc's `initialize'` makes then has postcondition `False`
  (theorem `toGRPCErrorMap_init_diverges`, proved). So every closed theorem that takes `Hctx` says
  nothing about an execution that gets past v3rpc's initialization. It "proves" any behaviour
  after that point, a panic included. The `DeadlineExceeded` half is sound: its value is
  `deadlineExceededError{}`, the same in every world.
- **New: the trust-base axiom `EtcdGrove.incomingOf_cancelCtx` is refuted in meaning, formally.**
  It has the same flaw, with a one-cell antecedent, and the transfer is proved in Lean
  (`incomingOf_const`): every two interface values have the same `metadata.incomingOf`. grpc
  disagrees. `v3rpc.incomingOf_cancellableContext` has the same shape and flaw (not formalized).
  This is the soundness finding of this review.

## The transfer (formal)

`crossWorld` (proved, axioms: Lean's three only). Take any `HeapGS hG`, an address `l` with
`0 < l.addr < maxAddr` and a value `v`. If for every ghost name `γ` the persistent heap points-to
`l ↦□ v` under `withHeapName hG γ` entails `⌜φ⌝`, then `φ` holds. Proof: `iOwn_alloc` of the one
fragment `Frag l discard (RSt 0, ag v)` at a fresh name (`frag_valid_iff`, `naHeapCmra_valid`).
`withHeapName` replaces only the non-atomic heap's name. Then `bupd_soundness` and
`pure_soundness`. A trust-base entailment is quantified over all `hG`, so it applies at
`withHeapName hG γ`.

So an entailment `(persistent points-tos) ⊢ ⌜f p = c⌝`, with `f` an opaque Lean function and `p` a
pointer, holds in every heap that has those cells, not only in the heap one execution builds. The
docstrings of `descs` and `incomingOf_cancelCtx` both argue per execution ("a location's
persistent field value is fixed within an execution"). The Lean statement is not per execution.

### `incomingOf_cancelCtx` ⟹ `incomingOf` is constant

```lean
theorem incomingOf_const [hG : HeapGS hlc GF] (c : Loc)
    (hc : 0 < (context.ctxField c).addr ∧ (context.ctxField c).addr < maxAddr)
    (p1 p2 : GoInterfaceOk) :
    metadata.incomingOf (GoInterface.ok p1) = metadata.incomingOf (GoInterface.ok p2)
```

```
'…incomingOf_const' depends on axioms: [propext, Classical.choice, Quot.sound,
 Perennial.EtcdGrove.incomingOf_cancelCtx]
```

Apply the axiom in the world `ctxField c ↦□ p1` and in the world `ctxField c ↦□ p2`: both equate
with `*cancelCtx c`'s metadata. The premise `hc` holds of every `*cancelCtx` an execution allocates,
since `heapPointsto` carries the range. So inside any run that holds a `ctxField c ↦□ _`,
`incomingOf` is constant on interfaces. This is not `False` in Lean: no pure fact tells two
`incomingOf` values apart. But per-run posts do: `FromIncomingContext.spec` returns
`incomingOf ctx`, and `context.WithValue.spec`/`Tracer.Start.spec` have `incomingOf` posts. In a run
that makes two contexts with different metadata, the specs and `incomingOf_const` give `False`.

The counterexample shape (not built: needs a goose project and the incoming specs) is a Go program
that makes a `*cancelCtx` and two incoming contexts with different metadata, then panics when
`FromIncomingContext` tells them apart. Go panics; its no-panic triple follows. Results that rest
on the axiom: the 22 collections that list it (`grep -l incomingOf_cancelCtx
etc/tcb-collections/*.txt`), auth, putget, lease, watch, txnlin, k8s etcd3 among them.

### `descs` ⟹ `CanceledDescConst` (step 1, argued, not formalized)

Read over all resources, `descs` holds at every resource satisfying `isPkgInit context`. That
predicate is satisfiable by a standalone resource for every location `x` of the `Canceled` cell's
`*errorString`:

- the deps (`errors`, `sync`, `sync/atomic`, `internal/race`, `internal/synctest`) are `True`;
  `time`'s is `startNano ↦□ v`;
- `context.isInit` (Perennial `Proof/context/Base.lean:237-251`) is persistent points-tos of
  `closedchan`, `Canceled`, `DeadlineExceeded`, `startNano`, `x.s` and the channel's `cap`/`mu`, two
  `inv`s (`goroutines`, `closedchanN`) and `isChan`'s `isLock`.

The construction is `crossWorld` with several cells (`na_heap_init` at `∅`, then `na_heap_alloc` and
`naHeapPointsto_persist` per cell). The invariants need a fresh wsat invariant name with
`ownI` fragments (`own_inv_to_inv`): an `inv` holds of its fragment whatever its content. It also
needs the global cells' addresses distinct and in range: `globalAddr` is abstract, so this is a
hypothesis about the context, true of real globals. Estimated 1–2 days. It was not done: the claim
it served (`False`) fails at step 2 anyway, and the transfer itself is proved above.

### Under `CanceledDescConst`, `toGRPCErrorMap.init` never returns (formal)

```lean
theorem toGRPCErrorMap_init_diverges (Hc : CanceledDescConst) (m : GoString) :
    {{ errVarCell mvcc.ErrFutureRev m }}
      (App (Val v3rpc.toGRPCErrorMap.init) (Val #()))
    {{ RET #(); False }}
```

```
'…toGRPCErrorMap_init_diverges' depends on axioms: [propext, Classical.choice, Quot.sound,
 Perennial.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.toGRPCErrorMap_init,
 Perennial.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.toGRPCErrorMap.init]
```

`errVarCell` is what mvcc's initializer establishes (`mvcc/Init.lean:340`). v3rpc's `initialize'`
makes this call after mvcc's initializer (`v3rpc/Init.lean:282`). The axiom's `ErrFutureRev ↦□ kf`
agrees with the cell's `*errorString` pointer, `grpcErrMapOk` gives it the mvcc description, and
`Hc` gives it `"context canceled"`.

## Results that take `ContextReadErrs`

157 files mention it. 50 are `Results`/`Adequacy` files (the audit counted 49; the 50th is
`partition/AdequacyWatch.lean`), every closed etcd theorem: putget, putget3, putgetN, auth,
auth3, authN, lease, leaseN, leasegrant, leaseexpiry(N), leasecatchup, watch, compacted,
compactwatch, cache, partition (+Watch), restart, restart1, restartN, txnlin, txnlinfaultsN,
k8s compactor, k8s etcd3, and `cache/v3/Results`. All take it as `Hctx : ∀ hG, ContextReadErrs
(heapAt hG lctx)`. All initialize v3rpc, so under `Hctx` each is vacuous past initialization (via
step 1).

## The family

| fact | shape | verdict |
|---|---|---|
| `ContextReadErrs.descs`, `Canceled` half | `isPkgInit context ⊢ ⌜errDesc (*errorString x) = …⌝` | **same flaw** (above) |
| `ContextReadErrs.descs`, `DeadlineExceeded` half | same, at `deadlineExceededError{}` | sound: one value in every world; better stated pure |
| `v3rpc.ctxErrDescs` (`v3rpc/Base.lean:230`, in `v3rpcInit`) | package fact restating `descs` | inherits it (proved from `descs` at `v3rpc/Init.lean:296`) |
| `ContextReadErrs.errs`, `errs_strong`; `ContextErrsClient.errs` | `isPkgInit context ⊢` type facts (`errLeafW`, method sets of `e.ty`) | not the flaw: the type is `*errorString` in every world (`HCanceledCell`), method sets are functions of the type |
| `incomingOf_cancelCtx` (axiom, `grpc/metadata/Incoming.lean:61`) | `ctxField c ↦□ p ⊢ ⌜incomingOf (*cancelCtx c) = incomingOf p⌝` | **same flaw**, formal (`incomingOf_const`) |
| `v3rpc.incomingOf_cancellableContext` (axiom, `v3rpc/WrapperMd.lean:76`) | `ccField l ↦□ c ⊢ ⌜incomingOf (ccCtx l) = incomingOf c⌝` | **same flaw** (same proof as `incomingOf_const`; not written) |
| `toGRPCErrorMap_init` (axiom) and the `status.FromError.spec` wand `errorMsgIs e m -∗ ⌜errDesc err = m⌝` | triple posts (per execution) | not transferable by `crossWorld`: a post needs a returning execution. Their per-execution reading is the repository's accepted one (`FromError.lean`'s docstring); across executions they say different things about one location, but no Lean theorem joins two executions |
| `rpctypes.errDesc_etcdError` (axiom) | pure, of a struct value | sound: the value carries `desc` |
| `ErrorStringLeaf`, `ErrorStringNoGRPCStatus`, `ErrorStringNotWriter`, `RpctypesEtcdErrorMethods`, `PeerPausable`, `NewModel`, `ApiDeps` | pure facts about types / method sets / function bodies | not the flaw |
| bbolt `optsAt_*`, `txLive_nonnull`, `rtxStats_excl`, `ownWTxG_*`, grpc `*_agree`, `clockLb_*`, `madeCancelCtx_of_isCancelCtx`, `v3rpc.ctxCauseOk_cancellable`, `etcdResolver_grpc` | entailments whose antecedent is an opaque predicate (or conclusion an `IProp`) | not this flaw: an opaque predicate is not satisfiable standalone by a heap fragment; no pure equation of an opaque function on a pointer |
| decisions.md "Follow-up" (~33623): `errDesc (*errorString x) = msg` given `x`'s cell | proposed, not stated | **must not be an entailment**: `crossWorld` at `x.s ↦□ "a"` and `↦□ "b"` gives `False` outright (only a range premise on `x.s`). State it per execution (a triple post or `FromError`'s wand) |

## Proposed fix (not applied)

1. `descs`: delete the `Canceled` half (audit option a). Restate the `DeadlineExceeded` half as a
   pure premise, `errDesc (interface.mkOk deadlineExceededError.ty #zero) = "context deadline
   exceeded"` (location-free, like `errDesc_etcdError`). Consumers:
   - `v3rpc/Init.lean:296` and `ctxErrDescs` / `ServerKVOn.lean:802-820`, which need only
     `notReadDesc` of the context errors. That comes per run from `toGRPCErrorMap_init`'s own
     conjuncts (no key has a read description; each `grpcErrKeyGlobals` variable is a key), and
     `context.Canceled` and `DeadlineExceeded` are in `grpcErrKeyGlobals` (`v3rpc/Base.lean:118-119`).
   - `ErrorsNewOk.lean:254`, `ChanCtx.lean:166`: client side. `FromError.spec`'s
     `errorMsgIs e m -∗ ⌜errDesc err = m⌝` where the client converts the error
     (`clientErr_statusErrOk_of_leaf`), with `errorMsgIs` of `*errorString` from `x.s ↦□ m`.

   Estimate: 1–2 days, 4 sites plus the 50 results' `Hctx`. Unchanged statement shape: the class
   loses a field.
2. `incomingOf_cancelCtx`, `incomingOf_cancellableContext`: restate per execution, e.g. as a
   persistent law inside the post of the spec that makes the context (`WithCancel`'s,
   `newCancellableContext`'s), or index `incomingOf` by a ghost name (an `IProp` agreement instead
   of a Lean function). Needs the user's decision (trust-base change); estimate after a Scope.
3. Review rule (proposed for `axiom/SKILL.md`): an entailment whose conclusion is a pure fact about
   an opaque Lean function, and whose antecedent is satisfiable standalone (persistent points-tos,
   `isPkgInit` of fragments), is checked by `crossWorld`. It must be true for every heap that has
   those cells, not only the one an execution builds.

## The per-execution reading retired (errdesc, 2026-11-20)

The table's row "`toGRPCErrorMap_init` (axiom) and the `status.FromError.spec` wand … triple posts (per
execution)" and the same reading of `metadata.outgoingOf` relied on posts being "claims about one
execution's heap" while the functions they constrain (`errDesc`, `statusCode`, `outgoingOf`) are the same
in every execution. That reading does not hold of the Lean statements: a fresh allocation may be any
location, so a post that fixes a pure function at a value the call allocates cannot be met by any
implementation (etcd-refimpl `README.md`, "Findings": `status.Error`, `FromError`,
`AppendToOutgoingContext`). The fix (`notes/errdesc-ghost-plan.md`, Part II of `notes/perheap-scope.md`)
makes these per-run relations instead of functions:

- **Stage 1 (outgoing metadata, landed with branch `prove-errdesc/2026-11-20`):** `metadata.outgoingOf`
  and the opaque `Prop` `metadata.builtRawMD` are gone; `metadata.outMD ctx md` (Perennial's chain at
  grpc's key, over the opaque `IProp` leaf `metadata.builtRawMDRaw v f`, no law) replaces them. The
  posts that equated `outgoingOf` of an allocated context now give `outMD` of it, at metadata the
  precondition fixed (`notes/decisions.md`, "Outgoing metadata as a per-run relation").
- **Stage 2 (errors):** `errDesc`, `statusCode`, `grpcStatusROP` (pending at this writing).
