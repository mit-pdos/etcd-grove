/-
**DRAFTS of N2's per-function interim contracts at the cluster view (O1, option B)**
(`notes/etcd-dist-plan.md` §18; #50, the etcd_safe lead, 2026-11-25). Lean-first (no Rocq counterpart).

STATEMENTS ONLY: definitions, no axiom, no proof, no `sorry`. **Unbuilt** (the VM was down when this
was written; no local Lean was run): expect name and instance fixes at the first build. Nothing
imports this file.

What is here:
* `DistView` (O1-B): the restart-stable names a client's statements read of the cluster, a Lean value
  chosen by the deployment's start (no publication, no countability needed);
* `etcdAddrAtV svc a Γ mid`: the address fact re-indexed by the view. The table `svc` is a parameter
  of every draft, standing for A1 (`etcdSvc`) restated at `Γ` once the coordinator picks O1-B; each
  draft's axiom would then be `X.wp_proof : X.spec etcdSvcV`;
* one `.spec` per unary clientv3 call the auth-off workloads make (§18.4 lists what each mirrors).

At adoption each draft moves to its own Spec/Proof pair (as `ClientGetDist.lean`), gets an
`axiom`-skill review, and joins the etcd_safe packet.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.S2Interim
public import Proof.go_etcd_io.etcd.client.v3.InvClientNewResult
public import Proof.go_etcd_io.etcd.client.v3.InvClientNew
public import Proof.go_etcd_io.etcd.client.v3.InvKVConn
public import Proof.go_etcd_io.etcd.client.v3.InvOp
public import Proof.go_etcd_io.etcd.client.v3.KVService
public import Proof.go_etcd_io.etcd.client.v3.InvTxnBuilder
public import Proof.go_etcd_io.etcd.client.v3.InvLease
public import Proof.go_etcd_io.etcd.client.v3.InvLeaseGrant
public import Proof.go_etcd_io.etcd.client.v3.InvLeaseRead

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial
namespace EtcdGrove
namespace etcd_dist
namespace view

open Iris Iris.BI Net client go_etcd_io.etcd.api.v3 go_etcd_io.etcd.server.v3.etcdserver

/-! ## The view (O1, option B) -/

/-- **What a client's statements read of the cluster** (O1-B, `notes/etcd-dist-plan.md` §18.3): a
Lean value the deployment's start chooses, never stored in ghost state.

* `kv`: the cluster's KV names (`ClusterNames.γk`, `clusterAllocN`'s). Every incarnation of every
  member has KV names `kvCongr` to it (a first start's are the cluster's; a restart keeps `kvCongr`,
  `restartNames`), so `kvSame` (what `isKv_intro` asks) holds at every member and every incarnation.
  The KV drafts read only `etcdKV kv` (its `st`) and `kvRevLb`/`kvRevLbZ` (its `rlog`, `c0`, `ch0`,
  `log0`, `cret`), and `kv.cmp`/`kv.lm`.
* `ls mid`: member `mid`'s lessor history name. **New**: today each incarnation's lessor name is
  `NewServer`'s choice (`mvcc.api.mvccLeases E.γ`, existential in its post). Until the Prove item P-L1
  (§18.3: `NewServer` takes it from the start's share) the lease drafts that read it cannot become
  axioms.
* `auth`: the cluster's auth mode (`SrvRaft.authOn`, restart-stable). The KV write drafts are for
  `auth = false` only (refusal-free members: a write is sent at most once). -/
structure DistView where
  kv : KVNames
  ls : w64 → GName
  auth : Bool

/-- **A member's names agree with the view** (pure; what `Serve_dist` would take in place of
`envAt γE ν ∗ ⌜ν = memberView ρ⌝` under O1-B). The lessor's tie joins it with P-L1. -/
def memberViewOk [GooseExts] (Γ : DistView) (ρ : ReqNames) : Prop :=
  kvCongr ρ.rd.kv Γ.kv

section addr
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable [GoLocalContext] [go.Semantics] [go_etcd_io.etcd.client.v3.Assumptions]
variable {GF : BundledGFunctors} [Gg : GooseGlobalGS .hasLC GF] [π : NetProtoGS]

attribute [local instance] GooseGlobalGS.gooseInvGS

/-- **The address `a` serves etcd's table `svc Γ mid`** (persistent): `etcdAddrAt` with the view `Γ`
in place of the publication name. `svc` is A1 restated at the view (a parameter here: see the file
header). -/
def etcdAddrAtV (svc : DistView → w64 → GrpcSvc GF) (a : GoString) (Γ : DistView) (mid : w64) :
    IProp GF :=
  iprop(∃ σ : NetSlotGS, grpcAddrAt (Gg := Gg) (π := π) (σ := σ) a (svc Γ mid))

instance etcdAddrAtV_persistent (svc : DistView → w64 → GrpcSvc GF) (a : GoString)
    (Γ : DistView) (mid : w64) : Persistent (etcdAddrAtV svc a Γ mid) := by
  unfold etcdAddrAtV; infer_instance

/-- **Every endpoint serves a member of the view** (persistent): what a client of several endpoints
(`etcdstart.NewClients eps`) takes. -/
def membersAtV (svc : DistView → w64 → GrpcSvc GF) (eps : List GoString) (Γ : DistView) :
    IProp GF :=
  iprop([∗list] a ∈ eps, ∃ mid : w64, etcdAddrAtV svc a Γ mid)

instance membersAtV_persistent (svc : DistView → w64 → GrpcSvc GF) (eps : List GoString)
    (Γ : DistView) : Persistent (membersAtV svc eps Γ) := by
  unfold membersAtV; infer_instance

end addr

/-! ## The KV calls (auth off; any member of the view answers) -/

section kv
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- What every KV draft takes of the client: `New`'s client `cl` of the endpoints `eps` (no proxy),
its `KV` field the `*kv` `api`, every endpoint a member of `Γ`. -/
def kvClientV (svc : DistView → w64 → GrpcSvc GF) [π : NetProtoGS] (cl api : Loc)
    (eps : List GoString) (V : WEnv GF) (Γ : DistView) : IProp GF :=
  iprop(isNewClient cl eps V ∗ clientNoProxy cl ∗
    clientF cl go!"KV" ↦□ interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.v3.kv.ty) #api ∗
    membersAtV (Gg := hG.goose_globalGS) svc eps Γ)

/-- **DRAFT `KV_Put_dist`: `(*kv).Put(ctx, key, val, opts...)` across machines** (mirrors the proved
client spec `kv.Put.spec` at `dup = false`, whose server side is `etcdPutSpecW`): `kv.Put.spec` with
`isKv api γ false` replaced by `kvClientV` at `Γ` and `γ := Γ.kv`, for a cluster with auth off; the
error arm without `kvErr` (nothing is claimed of a remote call's error). -/
abbrev KV_Put_dist.spec (svc : DistView → w64 → GrpcSvc GF) : Prop :=
  ∀ [π : NetProtoGS] (cl api : Loc) (eps : List GoString) (V : WEnv GF) (Γ : DistView)
    (ctx : GoInterfaceOk) (ctx_desc : context.ContextDesc (IProp GF)) (key val : GoString)
    (opts_sl : GoSlice) (opts : List (OpFull → OpFull)) (Q : KVState → IProp GF),
  Γ.auth = false →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ levelTok 0 ∗
      kvClientV svc cl api eps V Γ ∗
      ctxOk ctx ctx_desc ∗ ctxErrClient ctx ctx_desc ∗ optsAt opts_sl opts ∗
      ⌜¬ (opPutModel key val opts).putPanics ∧ (opPutModel key val opts).t = W64 2 ∧
        (putWireOf (opPutModel key val opts)).leaseID = W64 0⌝ ∗
      AU <{ ∃∃ (σ : KVState), etcdKV Γ.kv σ }> @ (⊤ \ ↑srvRaftN) \ ↑kvN, ∅
        <{ etcdKV Γ.kv (kvOpStep (.put (putWireOf (opPutModel key val opts))) σ) ∗ ⌜kvRoom σ⌝,
           COMM Q σ }> ∗
      ⌜opSizeOk (opPutModel key val opts)⌝ }}
    (App (App (App (App (Val (api @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.kv.ty @!!
        go!"Put")) (Val #(GoInterface.ok ctx))) (Val #key)) (Val #val)) (Val #opts_sl))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); levelTok 0 ∗
      ((⌜err = GoInterface.nil⌝ ∗ ∃ (m : PutRespM) (σ : KVState), putRespMsg resp m ∗ Q σ ∗
        ⌜m.hdr.revision = W64 ((σ.rev + 1 : Nat) : Int) ∧
          m.prev = (if (putWireOf (opPutModel key val opts)).base.prevKV then
            (σ.store.lookup (putWireOf (opPutModel key val opts)).key).map
              (KVRec.toKv (putWireOf (opPutModel key val opts)).key) else none) ∧
          kvRevFits (σ.rev + 1) ∧ kvLogOk σ ∧
          kvLogOk (kvOpStep (.put (putWireOf (opPutModel key val opts))) σ)⌝ ∗
        kvRevLb Γ.kv m.hdr.revision) ∨
      ⌜err ≠ GoInterface.nil ∧ resp = null⌝) }}

/-- **DRAFT `KV_Get_dist`: `(*kv).Get(ctx, key, opts...)` across machines** (mirrors `kv.Get.spec`,
server side `etcdRangeSpecEW`/`etcdRangeSpecW`): `kv.Get.spec` with `isKv` replaced by `kvClientV`
at `Γ`, `γ := Γ.kv`. Any auth mode: a read is retried only when immutable (`Unavailable`), so the
read update stays persistent as in `kv.Get.spec`. -/
abbrev KV_Get_dist.spec (svc : DistView → w64 → GrpcSvc GF) : Prop :=
  ∀ [π : NetProtoGS] (cl api : Loc) (eps : List GoString) (V : WEnv GF) (Γ : DistView)
    (ctx : GoInterfaceOk) (ctx_desc : context.ContextDesc (IProp GF)) (key : GoString)
    (opts_sl : GoSlice) (opts : List (OpFull → OpFull)) (R : IProp GF) (Q : KVState → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ levelTok 0 ∗
      kvClientV svc cl api eps V Γ ∗
      ctxOk ctx ctx_desc ∗ ctxErrClient ctx ctx_desc ∗ optsAtRes opts_sl opts R ∗ R ∗
      sortNamesIf (opGetModel key opts).base.sortSet ∗
      ⌜¬ opGetPanics opts ∧ (opGetModel key opts).t = W64 1⌝ ∗
      □ (⌜Q = fun _ => iprop(True)⌝ ∨ (⌜(rangeWireOf (opGetModel key opts)).base.serializable = false⌝ ∗
        AU <{ ∃∃ (σ : KVState), etcdKV Γ.kv σ }> @ (⊤ \ ↑srvRaftN) \ ↑kvN, ∅
        <{ etcdKV Γ.kv σ ∗ ⌜kvRoom σ⌝, COMM □ Q σ }>)) ∗
      ⌜opSizeOk (opGetModel key opts)⌝ }}
    (App (App (App (Val (api @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.kv.ty @!!
        go!"Get")) (Val #(GoInterface.ok ctx))) (Val #key)) (Val #opts_sl))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); levelTok 0 ∗ (R ∗
      ((⌜err = GoInterface.nil⌝ ∗ ∃ (m : RangeRespM) (σ : KVState), rangeRespMsg resp m ∗
          (if (rangeWireOf (opGetModel key opts)).base.serializable then iprop(True) else iprop(□ Q σ)) ∗
          ⌜sint.Z (rangeWireOf (opGetModel key opts)).base.rev ≤ (σ.rev : Int) ∧
            txn.srvRangeOk (rangeWireOf (opGetModel key opts))
              (σ.at (σ.readRev (rangeWireOf (opGetModel key opts)).base.rev)).kvs m.kvs m.more ∧
            m.count = txn.srvCount (rangeWireOf (opGetModel key opts))
              (σ.at (σ.readRev (rangeWireOf (opGetModel key opts)).base.rev)).kvs true ∧
            m.hdr.revision = W64 (σ.rev : Int) ∧ kvRevFits σ.rev ∧ kvLogOk σ⌝) ∨
        ⌜err ≠ GoInterface.nil ∧ resp = null⌝)) }}

/-- **DRAFT `KV_Delete_dist`: `(*kv).Delete(ctx, key, opts...)` across machines** (mirrors
`kv.Delete.spec` at `dup = false`, server side `etcdDeleteSpecW`), auth off. -/
abbrev KV_Delete_dist.spec (svc : DistView → w64 → GrpcSvc GF) : Prop :=
  ∀ [π : NetProtoGS] (cl api : Loc) (eps : List GoString) (V : WEnv GF) (Γ : DistView)
    (ctx : GoInterfaceOk) (ctx_desc : context.ContextDesc (IProp GF)) (key : GoString)
    (opts_sl : GoSlice) (opts : List (OpFull → OpFull)) (Q : KVState → IProp GF),
  Γ.auth = false →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ levelTok 0 ∗
      kvClientV svc cl api eps V Γ ∗
      ctxOk ctx ctx_desc ∗ ctxErrClient ctx ctx_desc ∗ optsAt opts_sl opts ∗
      ⌜¬ opDeletePanics key opts ∧ (opDeleteModel key opts).t = W64 3 ∧
        (deleteWireOf (opDeleteModel key opts)).base.rangeEnd ≠ [W8 0]⌝ ∗
      AU <{ ∃∃ (σ : KVState), etcdKV Γ.kv σ }> @ (⊤ \ ↑srvRaftN) \ ↑kvN, ∅
        <{ etcdKV Γ.kv (kvOpStep (.deleteRange (deleteWireOf (opDeleteModel key opts))) σ) ∗
           ⌜kvRoom σ⌝, COMM Q σ }> ∗
      ⌜opSizeOk (opDeleteModel key opts)⌝ }}
    (App (App (App (Val (api @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.kv.ty @!!
        go!"Delete")) (Val #(GoInterface.ok ctx))) (Val #key)) (Val #opts_sl))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); levelTok 0 ∗
      ((⌜err = GoInterface.nil⌝ ∗ ∃ (m : DelRespM) (σ : KVState), delRespMsg resp m ∗ Q σ ∗
        ⌜m.deleted = W64 ((rangeIn σ.kvs (deleteWireOf (opDeleteModel key opts))).length : Int) ∧
          m.prevs = (if (deleteWireOf (opDeleteModel key opts)).base.prevKV then
            rangeIn σ.kvs (deleteWireOf (opDeleteModel key opts)) else []) ∧
          m.hdr.revision = W64 ((kvOpStep (.deleteRange (deleteWireOf (opDeleteModel key opts))) σ).rev : Int) ∧
          kvRevFits (σ.rev + 1) ∧ kvLogOk σ ∧
          kvLogOk (kvOpStep (.deleteRange (deleteWireOf (opDeleteModel key opts))) σ)⌝) ∨
      ⌜err ≠ GoInterface.nil ∧ resp = null⌝) }}

/-- **DRAFT `KV_Compact_dist`: `(*kv).Compact(ctx, rev)` across machines** (mirrors `kv.Compact.spec`,
server side `etcdCompactSpecW`): a cluster in compaction mode, the caller knowing the KV has reached
`rev` plus the retention (`kvRevLbZ`, which a `Put`'s reply gives). Any auth mode is allowed by
`kv.Compact.spec`; the deployment's compaction mode excludes auth on (`NewServer`'s `cmp = true →
on = false`). -/
abbrev KV_Compact_dist.spec (svc : DistView → w64 → GrpcSvc GF) : Prop :=
  ∀ [π : NetProtoGS] (cl api : Loc) (eps : List GoString) (V : WEnv GF) (Γ : DistView)
    (ctx : GoInterfaceOk) (ctx_desc : context.ContextDesc (IProp GF)) (rev : w64),
  1 ≤ sint.Z rev → Γ.kv.cmp = true →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ levelTok 0 ∗
      kvClientV svc cl api eps V Γ ∗
      ctxOk ctx ctx_desc ∗ ctxErrClient ctx ctx_desc ∗ kvRevLbZ Γ.kv (sint.Z rev + Γ.kv.cret) }}
    (App (App (App (Val (api @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.kv.ty @!!
        go!"Compact")) (Val #(GoInterface.ok ctx))) (Val #rev)) (Val #slice.nil))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); levelTok 0 ∗
      ((⌜err = GoInterface.nil⌝ ∗ ∃ m : CompactRespM, compactRespMsg resp m) ∨
      ⌜err ≠ GoInterface.nil ∧ resp = null⌝) }}

/-- **DRAFT `Txn_Commit_dist`: `(*txn).Commit()` of a transaction built on the client's `*kv`**
(mirrors `txn.Commit.spec` at `dup = false`, server side `etcdTxnSpecW`): the builder's state
`txnObjAt … b` over the client's endpoints and `txnKvIs` of its `*kv` (what `kv.Txn`, `If`, `Then`,
`Else` give, proved, no call), auth off. -/
abbrev Txn_Commit_dist.spec (svc : DistView → w64 → GrpcSvc GF) : Prop :=
  ∀ [π : NetProtoGS] (cl api txn_ptr : Loc) (eps : List GoString) (V : WEnv GF) (Γ : DistView)
    (ctx : GoInterfaceOk) (ctx_desc : context.ContextDesc (IProp GF)) (b : TxnBuild)
    (Q : KVState → IProp GF),
  Γ.auth = false →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ levelTok 0 ∗
      kvClientV svc cl api eps V Γ ∗
      txnObjAt txn_ptr eps ctx ctx_desc b ∗ txnKvIs txn_ptr api ∗
      ⌜TxnModel.plain b.model ∧ txnModelIn (txnWireOf b.model)⌝ ∗
      (⌜txn.txnReadonly (txnWireOf b.model) = true ∧ Q = fun _ => iprop(True)⌝ ∨
        (⌜txn.txnReadonly (txnWireOf b.model) = true ∧ txn.txnSerializable (txnWireOf b.model) = false⌝ ∗
          □ AU <{ ∃∃ (σ : KVState), etcdKV Γ.kv σ }> @ (⊤ \ ↑srvRaftN) \ ↑kvN, ∅
            <{ etcdKV Γ.kv σ ∗ ⌜kvRoom σ⌝, COMM □ Q σ }>) ∨
        (⌜txn.txnReadonly (txnWireOf b.model) = false ∧ txn.txnPlain (txnWireOf b.model) ∧
            txnNoZeroEnd (txnWireOf b.model)⌝ ∗
          AU <{ ∃∃ (σ : KVState), etcdKV Γ.kv σ }> @ (⊤ \ ↑srvRaftN) \ ↑kvN, ∅
            <{ etcdKV Γ.kv (kvOpStep (.txn (txnWireOf b.model)) σ) ∗ ⌜kvRoom σ⌝, COMM Q σ }>)) ∗
      ⌜txnSizeOk (txnWireOf b.model)⌝ }}
    (App (Val (txn_ptr @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.txn.ty @!! go!"Commit"))
      (Val #()))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); levelTok 0 ∗
      ((⌜err = GoInterface.nil⌝ ∗ ∃ (m : TxnRespM) (σ : KVState), txnRespMsg resp m ∗
        (if txn.txnReadonly (txnWireOf b.model) then
          (if txn.txnSerializable (txnWireOf b.model) then iprop(True) else iprop(□ Q σ)) else Q σ) ∗
        ⌜m.succeeded = (txn.srvRunTxn (W64 ((σ.rev + 1 : Nat) : Int)) σ.kvs (txnWireOf b.model)).1 ∧
          opRespsRel false ((txnWireOf b.model).branch m.succeeded)
            (txn.srvRunTxn (W64 ((σ.rev + 1 : Nat) : Int)) σ.kvs (txnWireOf b.model)).2.2 m.resps ∧
          m.hdr.revision = W64 ((if txn.txnReadonly (txnWireOf b.model) then σ.rev else
            (σ.commit (txn.srvRunTxn (W64 ((σ.rev + 1 : Nat) : Int)) σ.kvs
              (txnWireOf b.model)).2.1).rev : Nat) : Int) ∧
          kvRevFits σ.rev ∧ kvLogOk σ ∧
          (txn.txnReadonly (txnWireOf b.model) = false →
            kvLogOk (σ.commit (txn.srvRunTxn (W64 ((σ.rev + 1 : Nat) : Int)) σ.kvs
              (txnWireOf b.model)).2.1))⌝ ∗
        client.txnRevLb Γ.kv (txnWireOf b.model) m) ∨
      ⌜err ≠ GoInterface.nil ∧ resp = null⌝) }}

end kv

/-! ## The lease calls (one endpoint: `LeaseLeases` is a member-local read) -/

section lease
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- What every lease draft takes of the client: `New`'s client `cl` of the one endpoint `ep` (no
proxy), its `Lease` field the `*lessor` `lp`, `ep` serving member `mid` of `Γ`. -/
def leaseClientV (svc : DistView → w64 → GrpcSvc GF) [π : NetProtoGS] (cl lp : Loc) (ep : GoString)
    (V : WEnv GF) (Γ : DistView) (mid : w64) : IProp GF :=
  iprop(isNewClient cl [ep] V ∗ clientNoProxy cl ∗
    clientF cl go!"Lease" ↦□
      (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.v3.lessor.ty) #lp : GoInterface) ∗
    etcdAddrAtV (Gg := hG.goose_globalGS) svc ep Γ mid)

/-- **DRAFT `Lease_Grant_dist`: `(*lessor).Grant(ctx, ttl)` at member `mid`, monotone lease mode**
(mirrors `lessor.Grant.spec` at `etcdLeaseGrantSpec γl`, i.e. `etcdLeaseGrantSpecW`, `γl := Γ.ls mid`;
`etcdReached` dropped: no workload reads it). Reads the lessor name: an axiom only after P-L1. -/
abbrev Lease_Grant_dist.spec (svc : DistView → w64 → GrpcSvc GF) : Prop :=
  ∀ [π : NetProtoGS] (cl lp : Loc) (ep : GoString) (V : WEnv GF) (Γ : DistView) (mid : w64)
    (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (ttl : w64),
  Γ.kv.lm = .mono →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ levelTok 0 ∗
      leaseClientV svc cl lp ep V Γ mid ∗ ctxOk ctx cd ∗ ctxErrClient ctx cd }}
    (App (App (Val (lp @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.lessor.ty @!! go!"Grant"))
      (Val #(GoInterface.ok ctx))) (Val #ttl))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); levelTok 0 ∗
      ((⌜err = GoInterface.nil⌝ ∗ ∃ m : LeaseGrantRespM,
        structFieldRef go_etcd_io.etcd.client.v3.LeaseGrantResponse go!"ID" resp ↦□ m.id ∗
        structFieldRef go_etcd_io.etcd.client.v3.LeaseGrantResponse go!"TTL" resp ↦□ m.ttl ∗
        ⌜m.id ≠ W64 0⌝ ∗ ∃ i : Nat, lease.leaseGrantedAt (Γ.ls mid) i m.id) ∨
      ⌜err ≠ GoInterface.nil ∧ resp = null⌝) }}

/-- **DRAFT `Lease_GrantLive_dist`: `(*lessor).Grant(ctx, ttl)` at member `mid`, revocable lease
mode** (mirrors `lessor.Grant.spec` at `etcdLeaseGrantSpecLive γl`, i.e. `etcdLeaseGrantSpecLiveW`;
clientv3's `Grant` sends `ID = 0`, the filter's request). After P-L1 only. -/
abbrev Lease_GrantLive_dist.spec (svc : DistView → w64 → GrpcSvc GF) : Prop :=
  ∀ [π : NetProtoGS] (cl lp : Loc) (ep : GoString) (V : WEnv GF) (Γ : DistView) (mid : w64)
    (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (ttl : w64),
  Γ.kv.lm = .revocable →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ levelTok 0 ∗
      leaseClientV svc cl lp ep V Γ mid ∗ ctxOk ctx cd ∗ ctxErrClient ctx cd }}
    (App (App (Val (lp @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.lessor.ty @!! go!"Grant"))
      (Val #(GoInterface.ok ctx))) (Val #ttl))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); levelTok 0 ∗
      ((⌜err = GoInterface.nil⌝ ∗ ∃ m : LeaseGrantRespM,
        structFieldRef go_etcd_io.etcd.client.v3.LeaseGrantResponse go!"ID" resp ↦□ m.id ∗
        structFieldRef go_etcd_io.etcd.client.v3.LeaseGrantResponse go!"TTL" resp ↦□ m.ttl ∗
        ⌜m.id ≠ W64 0⌝ ∗ ∃ (i : Nat) (l : Loc),
          lease.leaseLiveFrom (Γ.ls mid) i m.id l ∗ lease.leaseReqIs (Γ.ls mid) m.id ttl) ∨
      ⌜err ≠ GoInterface.nil ∧ resp = null⌝) }}

/-- **DRAFT `Lease_LeasesGranted_dist`: `(*lessor).Leases(ctx)` at member `mid`, monotone mode**
(mirrors `lessor.Leases.spec` at `etcdLeaseLeasesSpec γl`, i.e. `etcdLeaseLeasesSpecW`): the caller's
grants `G` at this member's lessor are all listed, no id twice. After P-L1 only. -/
abbrev Lease_LeasesGranted_dist.spec (svc : DistView → w64 → GrpcSvc GF) : Prop :=
  ∀ [π : NetProtoGS] (cl lp : Loc) (ep : GoString) (V : WEnv GF) (Γ : DistView) (mid : w64)
    (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (G : List w64),
  Γ.kv.lm = .mono →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ levelTok 0 ∗
      leaseClientV svc cl lp ep V Γ mid ∗ ctxOk ctx cd ∗ ctxErrClient ctx cd ∗
      [∗list] id ∈ G, ∃ i : Nat, lease.leaseGrantedAt (Γ.ls mid) i id }}
    (App (Val (lp @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.lessor.ty @!! go!"Leases"))
      (Val #(GoInterface.ok ctx)))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); levelTok 0 ∗
      ((⌜err = GoInterface.nil⌝ ∗ ∃ (ids : List w64) (sl : GoSlice),
          structFieldRef go_etcd_io.etcd.client.v3.LeaseLeasesResponse go!"Leases" resp ↦□ sl ∗
          sl ↦* (ids.map (fun id => (go_etcd_io.etcd.client.v3.LeaseStatus.mk id))) ∗
          ⌜ids.Nodup ∧ ∀ id ∈ G, id ∈ ids⌝) ∨
        ⌜err ≠ GoInterface.nil ∧ resp = null⌝) }}

/-- **DRAFT `Lease_LeasesLive_dist`: `(*lessor).Leases(ctx)` at member `mid`, revocable mode**
(mirrors `lessor.Leases.spec` at `etcdLeaseLeasesSpecLive γl`, i.e. `etcdLeaseLeasesSpecLiveW`): the
caller's lower bound `n` of the member's lessor history; the listing is the ids of a snapshot at an
index `≥ n` (`leaseIdsAt`, no id twice). After P-L1 only. -/
abbrev Lease_LeasesLive_dist.spec (svc : DistView → w64 → GrpcSvc GF) : Prop :=
  ∀ [π : NetProtoGS] (cl lp : Loc) (ep : GoString) (V : WEnv GF) (Γ : DistView) (mid : w64)
    (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (n : Nat),
  Γ.kv.lm = .revocable →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ levelTok 0 ∗
      leaseClientV svc cl lp ep V Γ mid ∗ ctxOk ctx cd ∗ ctxErrClient ctx cd ∗
      lease.lessorLb (Γ.ls mid) n }}
    (App (Val (lp @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.lessor.ty @!! go!"Leases"))
      (Val #(GoInterface.ok ctx)))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); levelTok 0 ∗
      ((⌜err = GoInterface.nil⌝ ∗ ∃ (ids : List w64) (sl : GoSlice) (j : Nat),
          structFieldRef go_etcd_io.etcd.client.v3.LeaseLeasesResponse go!"Leases" resp ↦□ sl ∗
          sl ↦* (ids.map (fun id => (go_etcd_io.etcd.client.v3.LeaseStatus.mk id))) ∗
          ⌜n ≤ j⌝ ∗ lease.leaseIdsAt (Γ.ls mid) j ids) ∨
        ⌜err ≠ GoInterface.nil ∧ resp = null⌝) }}

/-- **`Client_LeaseLeases_dist` (etcd-grove-03's draft, `etcd-safe-n9b` b0076abbbe) re-indexed by the
view**: the body unchanged but for `etcdAddrAt ep γE mid` → `etcdAddrAtV svc ep Γ mid` (inside
`leaseClientV`) and `levelTok 0` threaded (see §18.6). View-free (`etcdLeaseLeasesSpecAnyW`): any lease
mode. -/
abbrev Client_LeaseLeases_dist.spec (svc : DistView → w64 → GrpcSvc GF) : Prop :=
  ∀ [π : NetProtoGS] (cl lp : Loc) (ep : GoString) (V : WEnv GF) (Γ : DistView) (mid : w64)
    (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ levelTok 0 ∗
      leaseClientV svc cl lp ep V Γ mid ∗ ctxOk ci cd ∗ ctxErrClient ci cd }}
    (App (Val (lp @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.lessor.ty @!! go!"Leases"))
      (Val #(GoInterface.ok ci)))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); levelTok 0 ∗
      ((⌜err = GoInterface.nil⌝ ∗ ∃ (ids : List w64) (sl : GoSlice),
          structFieldRef go_etcd_io.etcd.client.v3.LeaseLeasesResponse go!"Leases" resp ↦□ sl ∗
          sl ↦* (ids.map (fun id => (go_etcd_io.etcd.client.v3.LeaseStatus.mk id))) ∗ ⌜ids.Nodup⌝) ∨
        ⌜err ≠ GoInterface.nil ∧ resp = null⌝) }}

/-- **`Client_LeaseTimeToLive_dist` (etcd-grove-03's draft) re-indexed by the view**, as
`Client_LeaseLeases_dist` above. View-free (`etcdLeaseTTLSpecW`), the call without options. -/
abbrev Client_LeaseTimeToLive_dist.spec (svc : DistView → w64 → GrpcSvc GF) : Prop :=
  ∀ [π : NetProtoGS] (cl lp : Loc) (ep : GoString) (V : WEnv GF) (Γ : DistView) (mid : w64)
    (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (id : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ levelTok 0 ∗
      leaseClientV svc cl lp ep V Γ mid ∗ ctxOk ci cd ∗ ctxErrClient ci cd }}
    (App (App (App (Val (lp @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.lessor.ty @!!
        go!"TimeToLive")) (Val #(GoInterface.ok ci))) (Val #id)) (Val #slice.nil))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); levelTok 0 ∗
      ((⌜err = GoInterface.nil⌝ ∗
          structFieldRef go_etcd_io.etcd.client.v3.LeaseTimeToLiveResponse go!"ID" resp ↦□ id) ∨
        ⌜err ≠ GoInterface.nil ∧ resp = null⌝) }}

end lease

end view
end etcd_dist
end EtcdGrove
end Perennial
