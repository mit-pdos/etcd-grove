# `EtcdServer.Range` (2026-10-27)

The server's `s.Range(ctx, r)` (`v3_server.go`): a linearizable read waits for the read index, a
serializable one reads the member's applied state. Written in `Put`'s vocabulary (`put.md`), then
reviewed by the user over three candidates; the user's critiques are all applied in the last.

## The first version (the repository's spec at the time)

```lean
abbrev EtcdServer.Range.spec : Prop :=
  ∀ (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (c : w64)
    (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (r : Loc) (o : OpFull)
    (ot : Option Loc) (te : Bool) (Q : List EntryModel → IProp GF) (F : mvcc.Log),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      isServerReq s E ρ ∗ isServerRead s E γr ∗ srvRdCall s E γr c ∗ context.isContext ctx cd ∗
      traceutil.ctxTraceIs ctx ot ∗ traceutil.ownTraceOpt ot te ∗ txn.rangeRequestIs r o ∗
      ⌜txn.validSortTarget o⌝ ∗ kvDep γr.kv Q ∗ mvcc.idxCert E.γ.idx F }}
    (App (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"Range"))
      (Val #(GoInterface.ok ctx))) (Val #r))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); srvRdCall s E γr c ∗
      ((⌜err = GoInterface.nil ∧ resp ≠ null⌝ ∗ (∃ info, apply.rangeClass E.authMode info o) ∗
          rangeReadOk E γr c F o resp Q) ∨
       (⌜resp = null ∧ err ≠ GoInterface.nil⌝ ∗ applyErrIs err)) }}
```

(and `specOn` for auth enabled.)

## The critiques, in order

1. **Candidate 1** took, like the client's `kv.Get`, `□ (⌜Q = True⌝ ∨ (⌜linearizable⌝ ∗ AU …))`: a
   serializable read took no update and its success gave `kvWas γ σ`, "the KV was in state `σ` at
   some point". The user: "what's the point of kvWas? The Q predicate can maintain whatever facts
   are important." A serializable read can fire the update too, at the current state `σ`, and answer
   from a past state `σr` of it.
2. **Candidate 2** did so, but kept the disjunct `⌜Q = True⌝ ∨`, which had existed only for
   serializable reads. The user: "What's the point of having Q = true in the precondition for the
   Range spec?" and "A spec that always requires the AU is a stronger spec, because the True ∨ AU
   spec can be proven as a layer on top by putting kvState in an invariant. In general, we should
   avoid specs that are really the disjunction of two alternate specifications, especially if one of
   those specs is strictly stronger than the others."
3. **Candidate 3**, below.

## The spec after the critiques (candidate 3)

`KVState.PastOf σ σ'`: the same history up to `σ`, then later revisions
(`σ.compacted = σ'.compacted ∧ σ.base = σ'.base ∧ σ.changes <+: σ'.changes`).

```lean
abbrev EtcdServer.Range.spec : Prop :=
  ∀ (s : Loc) (γ : KVName) (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF))
    (ot : Option Loc) (te : Bool) (r : Loc) (o : OpFull) (Q : KVState → IProp GF),
  {{ isKVServer s γ ∗ threadTok ∗ context.isContext ctx cd ∗
      traceutil.ctxTraceIs ctx ot ∗ traceutil.ownTraceOpt ot te ∗
      txn.rangeRequestIs r o ∗ ⌜txn.validSortTarget o⌝ ∗
      □ AU <{ ∃∃ (σ : KVState), kvState γ σ }> @ ⊤ \ ↑kvN, ∅
          <{ kvState γ σ, COMM □ Q σ }> }}
    (App (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"Range"))
      (Val #(GoInterface.ok ctx))) (Val #r))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); threadTok ∗
      ((⌜err = GoInterface.nil⌝ ∗ ∃ (σ σr : KVState) (kvs : List EtcdKv) (more : Bool),
          □ Q σ ∗
          ⌜σr.PastOf σ ∧ (o.base.serializable = false → σr = σ) ∧
            sint.Z o.base.rev ≤ (σr.rev : Int) ∧ σr.compacted ≤ σr.readRev o.base.rev ∧
            txn.srvRangeOk o (σr.at (σr.readRev o.base.rev)).kvs kvs more⌝ ∗
          txn.rangeResponseIs resp (W64 (σr.rev : Int)) kvs more
            (txn.srvCount o (σr.at (σr.readRev o.base.rev)).kvs true) ∗
          txn.respHdrOwn (structFieldRef etcdserverpb.RangeResponse go!"Header" resp)) ∨
       (⌜resp = null ∧ err ≠ GoInterface.nil⌝ ∗ applyErrIs err)) }}
```

Open: auth (as `Put`), and the `□` on the update, a need of a replicated implementation (a single
server could take a one-shot update, a stronger spec).
