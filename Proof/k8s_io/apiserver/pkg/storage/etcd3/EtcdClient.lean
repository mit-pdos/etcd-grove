/-
Lean-first (no Rocq counterpart).

# The k8s library's etcd client, as an interface (k8s-dist plan, stage K5: `notes/k8s-dist-lean-plan.md` §4.1)

The k8s storage library (`etcd3.store`, its watch and compactor) talks to etcd through a
`*clientv3.Client` `cl` (and the `kubernetes.Client` over it). Its proofs see that client only through
`k8sClient K cl`: the client's data `K : K8sEtcd GF` and the triples of the calls the library makes
(`K8sEtcd.Laws`), over the client's handle `K.handle cl`.

- `K.kvs`: the KV ghosts a request may linearize at; every update the triples take is given at each of
  them (`[∧list] γ ∈ K.kvs`). In-process (`inProcEtcd`, `EtcdClientInProc.lean`), one per member; a
  client of one cluster view has one.
- `K.live`: the premise under which a range error is sound (in-process: no member refuses connections).
- `K.eps`: the client's endpoints.
- `K.handle cl` (persistent): what the triples need of `cl`; in-process `isNewClient` of the members
  with `clientWriteOnce` and the members' registrations.
- `K.kvAt api` (C2): what the `Get` of the client's `*kv` `api` needs; in-process its `kvObjAt` and the
  members' registrations. (The client's `Watcher` is already abstract in the library's proofs:
  `clientWatchOk`, over a watch environment of the KV state.)
- `K.txnAt tp ci cd b` (C3): what the methods of a transaction the client's `KV.Txn` made need, holding
  `b`; in-process its `txnObjAt`, sending a write at most once. (The compactor's `Compact` and its
  `Get` of the key go through the client's KV handle, `clientKvOk`, as its `Watch` through
  `clientWatchOk`: both are per cluster already.)

Each triple is the in-process spec of the call (`Spec/go_etcd_io/etcd/client/v3/kubernetes/`) with the
handle in place of `isNewClient … ∗ clientWriteOnce … ∗ [∗list] x ∈ ms, kvRegsAt x`, `[∧list] γ ∈ K.kvs`
in place of `[∧list] x ∈ ms, … x.γr.kv …`, and `K.live` in place of `∀ x ∈ ms, noRefusalAt x.addr`.
-/
module

public import Spec.go_etcd_io.etcd.client.v3.kubernetes.Client__Get
public import Spec.go_etcd_io.etcd.client.v3.kubernetes.Client__List
public import Spec.go_etcd_io.etcd.client.v3.kubernetes.Client__OptimisticPut
public import Spec.go_etcd_io.etcd.client.v3.kubernetes.Client__OptimisticDelete
public import Proof.go_etcd_io.etcd.client.v3.InvOp
public import Proof.go_etcd_io.etcd.client.v3.InvKVConn
public import Proof.go_etcd_io.etcd.client.v3.kubernetes.GetLatest
public import Proof.go_etcd_io.etcd.client.v3.InvTxnBuilder
public import Proof.go_etcd_io.etcd.client.v3.KVService
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.txnwork.Client
public import Proof.k8s_io.apiserver.pkg.storage.etcd3.CompactorDefs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver EtcdGrove.kubernetes

/-- **The k8s library's etcd client**: its data (see the file header). -/
structure K8sEtcd (GF : BundledGFunctors) [GooseExts] where
  kvs : List KVNames
  live : Prop
  eps : List GoString
  handle : Loc → IProp GF
  /-- what the `Get` of the client's `*kv` `api` needs (C2); in-process its `kvObjAt` and the members'
  registrations -/
  kvAt : Loc → IProp GF
  /-- what the methods of a transaction `tp` the client's `KV.Txn` made need, with its context and
  what it holds (`TxnBuild`) (C3); in-process its `txnObjAt` over the endpoints, sending a write at
  most once, and the members' registrations -/
  txnAt : Loc → GoInterfaceOk → context.ContextDesc (IProp GF) → TxnBuild → IProp GF

/-- The compactor's round transaction (`Compact`), as the client's builder holds it. -/
abbrev casClientTxn (ev rev : w64) : TxnModel :=
  etcd_txnlin.clientTxn [.ver compactRevKey ev] [.put compactRevKey (fmtInt rev (W64 10))]
    [.get compactRevKey]

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **The client calls the library makes** (C1: the store's `kubernetes.Client` methods; C2: the client's `KV.Get`, for the watch; C3: the
compactor's endpoints and round transaction), on any
`kubernetes.Client` `kc` over a client whose handle holds (see the file header). -/
structure K8sEtcd.Laws (K : K8sEtcd GF) : Prop where
  get : ∀ [go_etcd_io.etcd.client.v3.kubernetes.Assumptions] [go_etcd_io.etcd.cache.v3.Assumptions]
    [go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
    (kc : go_etcd_io.etcd.client.v3.kubernetes.Client) (ci : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) (key : GoString)
    (opts : go_etcd_io.etcd.client.v3.kubernetes.GetOptions) (Q : w64 → w64 → KVState → IProp GF),
    0 ≤ sint.Z opts.Revision' → key.length ≤ opKeyMax →
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.kubernetes ∗ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ levelTok 0 ∗ (K.handle kc.Client' ∗
        ctxOk ci cd ∗ ctxErrClient ci cd ∗
        (∀ R m, |==> □ [∧list] γ ∈ K.kvs, ⌜Q R m = fun _ => iprop(True)⌝ ∨ kvReadAu γ (Q R m))) }}
      (App (App (App (Val (kc @!! go_etcd_io.etcd.client.v3.kubernetes.Client.ty @!! go!"Get"))
        (Val #(GoInterface.ok ci))) (Val #key)) (Val #opts))
    {{ (resp : go_etcd_io.etcd.client.v3.kubernetes.GetResponse) (err : GoInterface),
        RET (PairV #resp #err); levelTok 0 ∗ ((⌜err = GoInterface.nil⌝ ∗ ∃ σ : KVState,
          □ Q (W64 (σ.rev : Int)) (modAtRev key σ opts.Revision') σ ∗
          ⌜resp.Revision' = W64 (σ.rev : Int) ∧ σ.readRev opts.Revision' ≤ σ.rev ∧ kvRevFits σ.rev ∧
            ∀ v ∈ σ.kvs, v.value.length ≤ etcdKeyMax⌝ ∗
          kvOut resp.KV' (mvcc.findKey key (σ.at (σ.readRev opts.Revision')).kvs)) ∨
        ⌜err ≠ GoInterface.nil⌝ ∗ ⌜clientErr err⌝ ∗ go_etcd_io.etcd.cache.v3.statusErrOk err ∗
          go_etcd_io.etcd.cache.v3.errCellOk err ∗
          (⌜key ≠ [] ∧ K.live⌝ →
            k8s.rangeErrSound opts.Revision' (fun R σ => ∃ m, Q R m σ) err)) }}
  list : ∀ [go_etcd_io.etcd.client.v3.kubernetes.Assumptions] [go_etcd_io.etcd.cache.v3.Assumptions]
    [go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
    (kc : go_etcd_io.etcd.client.v3.kubernetes.Client)
    (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (pfx : GoString)
    (opts : go_etcd_io.etcd.client.v3.kubernetes.ListOptions) (Q : w64 → KVState → IProp GF),
    pfx.length ≤ opKeyMax → opts.Continue'.length ≤ opKeyMax →
    0 ≤ sint.Z opts.Revision' → 0 ≤ sint.Z opts.Limit' → (opts.Continue' = [] ∨ pfx <+: opts.Continue') →
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.kubernetes ∗ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ levelTok 0 ∗ (K.handle kc.Client' ∗
        ctxOk ci cd ∗ ctxErrClient ci cd ∗
        (∀ R, |==> □ [∧list] γ ∈ K.kvs, ⌜Q R = fun _ => iprop(True)⌝ ∨ kvReadAu γ (Q R))) }}
      (App (App (App (Val (kc @!! go_etcd_io.etcd.client.v3.kubernetes.Client.ty @!! go!"List"))
        (Val #(GoInterface.ok ci))) (Val #pfx)) (Val #opts))
    {{ (resp : go_etcd_io.etcd.client.v3.kubernetes.ListResponse) (err : GoInterface),
        RET (PairV #resp #err); levelTok 0 ∗ ((⌜err = GoInterface.nil⌝ ∗ ∃ σ : KVState, □ Q (W64 (σ.rev : Int)) σ ∗
          ⌜σ.readRev opts.Revision' ≤ σ.rev ∧ kvRevFits σ.rev⌝ ∗
          listRespIs resp σ pfx true opts.Revision' opts.Limit'
            (if opts.Continue' = [] then pfx else opts.Continue')) ∨
        (⌜err ≠ GoInterface.nil⌝ ∗ ⌜clientErr err⌝ ∗ go_etcd_io.etcd.cache.v3.statusErrOk err ∗
          go_etcd_io.etcd.cache.v3.errCellOk err ∗
          (⌜pfx ≠ [] ∧ K.live⌝ → rangeErrSound opts.Revision' Q err))) }}
  optimisticPut : ∀ [go_etcd_io.etcd.client.v3.kubernetes.Assumptions] [go_etcd_io.etcd.cache.v3.Assumptions]
    [go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
    (kc : go_etcd_io.etcd.client.v3.kubernetes.Client) (ci : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF))
    (key : GoString) (vsl : GoSlice) (val : GoString) (rev : w64)
    (opts : go_etcd_io.etcd.client.v3.kubernetes.PutOptions) (Q : KVState → IProp GF),
    opts.LeaseID' = W64 0 → key.length ≤ opKeyMax → val.length ≤ opValMax →
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.kubernetes ∗ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ levelTok 0 ∗ (K.handle kc.Client' ∗
        ctxOk ci cd ∗ ctxErrClient ci cd ∗ vsl ↦*□ val ∗
        ([∧list] γ ∈ K.kvs, kvOpAu1 γ (.txn (optPutTxn key val rev opts.GetOnFailure')) Q)) }}
      (App (App (App (App (App (Val (kc @!! go_etcd_io.etcd.client.v3.kubernetes.Client.ty @!!
        go!"OptimisticPut")) (Val #(GoInterface.ok ci))) (Val #key)) (Val #vsl)) (Val #rev))
        (Val #opts))
    {{ (resp : go_etcd_io.etcd.client.v3.kubernetes.PutResponse) (err : GoInterface),
        RET (PairV #resp #err); levelTok 0 ∗ ((⌜err = GoInterface.nil⌝ ∗ ∃ σ : KVState, Q σ ∗
          ⌜resp.Succeeded' = (txn.srvRunTxn (W64 ((σ.rev + 1 : Nat) : Int)) σ.kvs
              (optPutTxn key val rev opts.GetOnFailure')).1 ∧
            resp.Revision' =
              W64 ((kvOpStep (.txn (optPutTxn key val rev opts.GetOnFailure')) σ).rev : Int) ∧
            kvRevFits σ.rev ∧ ∀ v ∈ σ.kvs, v.value.length ≤ etcdKeyMax⌝ ∗
          (if opts.GetOnFailure' && !resp.Succeeded' then
            kvOut resp.KV' (single (σ.kvs.filter fun v => decide (v.key = key)))
          else iprop(⌜resp.KV' = null⌝))) ∨
        ⌜err ≠ GoInterface.nil⌝ ∗ ⌜clientErr err⌝ ∗ go_etcd_io.etcd.cache.v3.statusErrOk err ∗
          go_etcd_io.etcd.cache.v3.errCellOk err) }}
  optimisticDelete : ∀ [go_etcd_io.etcd.client.v3.kubernetes.Assumptions] [go_etcd_io.etcd.cache.v3.Assumptions]
    [go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
    (kc : go_etcd_io.etcd.client.v3.kubernetes.Client) (ci : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF))
    (key : GoString) (rev : w64)
    (opts : go_etcd_io.etcd.client.v3.kubernetes.DeleteOptions) (Q : KVState → IProp GF),
    key.length ≤ opKeyMax →
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.kubernetes ∗ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ levelTok 0 ∗ (K.handle kc.Client' ∗
        ctxOk ci cd ∗ ctxErrClient ci cd ∗
        ([∧list] γ ∈ K.kvs, kvOpAu1 γ (.txn (optDelTxn key rev opts.GetOnFailure')) Q)) }}
      (App (App (App (App (Val (kc @!! go_etcd_io.etcd.client.v3.kubernetes.Client.ty @!!
        go!"OptimisticDelete")) (Val #(GoInterface.ok ci))) (Val #key)) (Val #rev)) (Val #opts))
    {{ (resp : go_etcd_io.etcd.client.v3.kubernetes.DeleteResponse) (err : GoInterface),
        RET (PairV #resp #err); levelTok 0 ∗ ((⌜err = GoInterface.nil⌝ ∗ ∃ σ : KVState, Q σ ∗
          ⌜resp.Succeeded' = (txn.srvRunTxn (W64 ((σ.rev + 1 : Nat) : Int)) σ.kvs
              (optDelTxn key rev opts.GetOnFailure')).1 ∧
            resp.Revision' =
              W64 ((kvOpStep (.txn (optDelTxn key rev opts.GetOnFailure')) σ).rev : Int) ∧
            kvRevFits σ.rev⌝ ∗
          (if opts.GetOnFailure' && !resp.Succeeded' then
            kvOut resp.KV' (single (σ.kvs.filter fun v => decide (v.key = key)))
          else iprop(⌜resp.KV' = null⌝))) ∨
        ⌜err ≠ GoInterface.nil⌝ ∗ ⌜clientErr err⌝ ∗ go_etcd_io.etcd.cache.v3.statusErrOk err ∗
          go_etcd_io.etcd.cache.v3.errCellOk err) }}

  /-- The client's context, not nil, and the fields `CheckClient` reads (`New`). -/
  ctxFields : ∀ cl : Loc, K.handle cl ⊢
    (∃ cx : GoInterface, EtcdGrove.clientF cl go!"ctx" ↦□ cx ∗ ⌜cx ≠ GoInterface.nil⌝) ∗
      EtcdGrove.clientCheckFields cl
  /-- C2 (the watch's initial list): the client's `KV` is a `*kv`. -/
  kvField : ∀ cl : Loc, K.handle cl ⊢ ∃ api : Loc,
    EtcdGrove.clientF cl go!"KV" ↦□
      interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.v3.kv.ty) #api ∗ □ K.kvAt api
  /-- C2: the `Get` of a client's `*kv` `api` with the options `gs` (a linearizable range, unsorted), with the read update `Qr`
  at each of `K.kvs`: `nil` and the reply `m` at a state `σ` the update fired at, `m` the server's
  answer at `σ`; or a client error (`kClientErr`'s body). -/
  kvGet : ∀ [go_etcd_io.etcd.cache.v3.Assumptions]
    [go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
    (api : Loc) (ctx : GoInterfaceOk) (cdw : context.ContextDesc (IProp GF)) (pk : GoString)
    (osl : GoSlice) (gs : List (OpFull → OpFull)) (Qr : KVState → IProp GF),
    opSizeOk (opGetModel pk gs) → ¬ opGetPanics gs ∧ (opGetModel pk gs).t = W64 1 →
    (rangeWireOf (opGetModel pk gs)).base.serializable = false →
    (opGetModel pk gs).base.sortSet = false →
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ levelTok 0 ∗ (K.kvAt api ∗
        ctxOk ctx cdw ∗ ctxErrClient ctx cdw ∗ optsAt osl gs ∗ □ ([∗list] γ ∈ K.kvs, kvReadAu γ Qr)) }}
      (App (App (App (Val (api @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.kv.ty @!!
          go!"Get")) (Val #(GoInterface.ok ctx))) (Val #pk)) (Val #osl))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); levelTok 0 ∗
        ((⌜err = GoInterface.nil⌝ ∗ ∃ (m : RangeRespM) (σ : KVState), rangeRespMsgO resp m ∗ □ Qr σ ∗
          ⌜txn.srvRangeOk (rangeWireOf (opGetModel pk gs))
              (σ.at (σ.readRev (rangeWireOf (opGetModel pk gs)).base.rev)).kvs m.kvs m.more ∧
            m.hdr.revision = W64 (σ.rev : Int) ∧
            σ.readRev (rangeWireOf (opGetModel pk gs)).base.rev ≤ σ.rev ∧ kvRevFits σ.rev⌝) ∨
        (⌜err ≠ GoInterface.nil⌝ ∗ ⌜err ≠ GoInterface.nil ∧ clientErr err⌝ ∗
          go_etcd_io.etcd.cache.v3.statusErrOk err ∗ go_etcd_io.etcd.cache.v3.errCellOk err)) }}
  /-- C3 (the compactor): the client's endpoints, `K.eps`. -/
  endpoints : ∀ cl : Loc,
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ levelTok 0 ∗ K.handle cl }}
      (App (Val (cl @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.Client.ty @!! go!"Endpoints"))
        (Val #()))
    {{ (sl : GoSlice), RET #sl; levelTok 0 ∗ sl ↦* K.eps }}
  /-- C3: `Txn` of the client's `*kv` `api` (its `KV` field) starts an empty transaction. -/
  kvTxn : ∀ (cl api : Loc) (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)),
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ K.handle cl ∗
        EtcdGrove.clientF cl go!"KV" ↦□
          interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.v3.kv.ty) #api ∗
        K.kvAt api ∗ ctxOk ci cd ∗ ctxErrClient ci cd }}
      (App (Val (api @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.kv.ty @!! go!"Txn"))
        (Val #(GoInterface.ok ci)))
    {{ (t : GoInterface), RET #t; ∃ tp : Loc,
        ⌜t = interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.v3.txn.ty) #tp⌝ ∗
        K.txnAt tp ci cd TxnBuild.empty }}
  /-- C3: the transaction's `If` (`txn.If.spec` over `K.txnAt`). -/
  txnIf : ∀ (tp : Loc) (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF))
    (b : TxnBuild) (sl : GoSlice) (cs : List CmpModel),
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ K.txnAt tp ci cd b ∗
        cmpsAt sl cs ∗ ⌜b.cif = false ∧ b.cthen = false ∧ b.celse = false⌝ }}
      (App (Val (tp @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.txn.ty @!! go!"If")) (Val #sl))
    {{ RET #(interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.v3.txn.ty) #tp : GoInterface);
        K.txnAt tp ci cd { b with model := { b.model with cmps := b.model.cmps ++ cs }, cif := true } }}
  /-- C3: the transaction's `Then` at plain operations (`txn.Then.specPlain` over `K.txnAt`). -/
  txnThen : ∀ (tp : Loc) (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF))
    (b : TxnBuild) (sl : GoSlice) (os : List OpFull) (ops : List TxnOp),
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ K.txnAt tp ci cd b ∗
        opsAt sl os ∗ ⌜os.map txnOpOf = ops.map some ∧ b.cthen = false ∧ b.celse = false⌝ }}
      (App (Val (tp @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.txn.ty @!! go!"Then")) (Val #sl))
    {{ RET #(interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.v3.txn.ty) #tp : GoInterface);
        K.txnAt tp ci cd { b with model := { b.model with thenOps := b.model.thenOps ++ ops }, cthen := true } }}
  /-- C3: the transaction's `Else` at plain operations (`txn.Else.specPlain` over `K.txnAt`). -/
  txnElse : ∀ (tp : Loc) (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF))
    (b : TxnBuild) (sl : GoSlice) (os : List OpFull) (ops : List TxnOp),
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ K.txnAt tp ci cd b ∗
        opsAt sl os ∗ ⌜os.map txnOpOf = ops.map some ∧ b.celse = false⌝ }}
      (App (Val (tp @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.txn.ty @!! go!"Else")) (Val #sl))
    {{ RET #(interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.v3.txn.ty) #tp : GoInterface);
        K.txnAt tp ci cd { b with model := { b.model with elseOps := b.model.elseOps ++ ops }, celse := true } }}
  /-- C3: the compactor's round's `Commit()` (`casClientTxn ev rev`), with its update `Q` at each of
  `K.kvs` (each the KV `γk`), fired at most once: the reply's verdict and responses the server's run
  at the state `σ` the update fired at, its revision `σ`'s after it, positive and reached; or a client
  error (`kvErr`). -/
  casCommit : ∀ [go_etcd_io.etcd.cache.v3.Assumptions] (tp : Loc) (γk : KVNames),
    (∀ γ ∈ K.kvs, kvSame γ γk) →
    ∀ (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (b : TxnBuild) (ev rev : w64)
      (Q : KVState → IProp GF), b.model = casClientTxn ev rev →
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ levelTok 0 ∗
        K.txnAt tp ci cd b ∗ ([∧list] γ ∈ K.kvs, kvOpAu1 γ (.txn (casTxn ev rev)) Q) }}
      (App (Val (tp @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.txn.ty @!! go!"Commit"))
        (Val #()))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); levelTok 0 ∗
        ((⌜err = GoInterface.nil⌝ ∗ ∃ (m : TxnRespM) (σ : KVState), txnRespMsg resp m ∗ Q σ ∗
          ⌜m.succeeded = casWins ev rev σ ∧
            client.opRespsRel false ((casTxn ev rev).branch m.succeeded)
              (txn.srvRunTxn (W64 ((σ.rev + 1 : Nat) : Int)) σ.kvs (casTxn ev rev)).2.2 m.resps ∧
            0 < sint.Z m.hdr.revision⌝ ∗ kvRevLb γk m.hdr.revision) ∨
          (⌜err ≠ GoInterface.nil⌝ ∗ kvErr err)) }}

/-- **`Client.Get` at the latest revision** through the client's laws, as the store's unary paths
call it (`kubernetes.Client.Get.latest`'s statement over `K`). -/
theorem K8sEtcd.Laws.getLatest {K : K8sEtcd GF} (hK : K.Laws)
    [go_etcd_io.etcd.client.v3.kubernetes.Assumptions] [go_etcd_io.etcd.cache.v3.Assumptions]
    [go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
    (kc : go_etcd_io.etcd.client.v3.kubernetes.Client) (ci : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) (key : GoString)
    (opts : go_etcd_io.etcd.client.v3.kubernetes.GetOptions) (Q : w64 → w64 → KVState → IProp GF)
    (hrev : opts.Revision' = W64 0) (hk : key.length ≤ opKeyMax) :
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.kubernetes ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ levelTok 0 ∗
      (K.handle kc.Client' ∗ ctxOk ci cd ∗ ctxErrClient ci cd ∗
      (∀ R m, |==> □ [∧list] γ ∈ K.kvs, ⌜Q R m = fun _ => iprop(True)⌝ ∨ kvReadAu γ (Q R m))) }}
    (App (App (App (Val (kc @!! go_etcd_io.etcd.client.v3.kubernetes.Client.ty @!! go!"Get"))
      (Val #(GoInterface.ok ci))) (Val #key)) (Val #opts))
  {{ (resp : go_etcd_io.etcd.client.v3.kubernetes.GetResponse) (err : GoInterface),
      RET (PairV #resp #err); levelTok 0 ∗
      ((⌜err = GoInterface.nil⌝ ∗ ∃ σ : KVState, □ Q (W64 (σ.rev : Int)) (modAt key σ) σ ∗
        ⌜resp.Revision' = W64 (σ.rev : Int) ∧ kvRevFits σ.rev ∧
          ∀ v ∈ σ.kvs, v.value.length ≤ etcdKeyMax⌝ ∗
        kvOut resp.KV' (mvcc.findKey key σ.kvs)) ∨
      ⌜err ≠ GoInterface.nil⌝ ∗ ⌜clientErr err⌝ ∗ go_etcd_io.etcd.cache.v3.statusErrOk err ∗
        go_etcd_io.etcd.cache.v3.errCellOk err) }} := by
  have h0 : 0 ≤ sint.Z opts.Revision' := by rw [hrev]; decide
  iintro %Φ Hpre HΦ
  iapply (hK.get kc ci cd key opts Q h0 hk) $$ [Hpre]
  · iexact Hpre
  inext
  iintro %resp %err ⟨Hlt, Hout⟩
  iapply HΦ
  iframe Hlt
  icases Hout with (⟨%Herr, %σ, #HQ, %Hσ, #Hkv⟩ | ⟨%Herr, %Hce, #Hse, #Hcl, -⟩)
  · ileft
    isplitl []
    · ipureintro; exact Herr
    iexists σ
    have e1 : modAtRev key σ opts.Revision' = modAt key σ := by
      rw [hrev]; exact kubernetes.modAtRev_zero key σ
    have e2 : (σ.at (σ.readRev opts.Revision')).kvs = σ.kvs := by
      rw [hrev, kubernetes.KVState.readRev_zero]; rfl
    rw [e1, e2] at *
    obtain ⟨h1, -, h3, h4⟩ := Hσ
    iframe HQ Hkv
    ipureintro; exact ⟨h1, h3, h4⟩
  · iright
    iframe Hse Hcl
    ipureintro; exact ⟨Herr, Hce⟩

/-- **The library's etcd client `cl`** (persistent; see the file header): its laws hold, and its
handle. -/
def k8sClient (K : K8sEtcd GF) (cl : Loc) : IProp GF :=
  iprop(⌜K.Laws⌝ ∗ □ K.handle cl)

instance k8sClient_persistent (K : K8sEtcd GF) (cl : Loc) : Persistent (k8sClient K cl) := by
  unfold k8sClient; infer_instance

end laws

end k8s
end EtcdGrove
end Perennial
