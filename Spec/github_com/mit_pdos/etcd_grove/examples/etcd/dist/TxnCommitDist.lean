/-
`(*txn).Commit()` by a client of members at other machines, at the cluster view (`notes/etcd-dist-plan.md` §18.4; a
trust-boundary axiom until #24's S2 client side: `Proof/.../etcd/dist/TxnCommitDist.lean`). Lean-first (no Rocq
counterpart).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.KVClientDist
public import Proof.go_etcd_io.etcd.client.v3.InvKVConn
public import Proof.go_etcd_io.etcd.client.v3.InvOp
public import Proof.go_etcd_io.etcd.client.v3.KVService
public import Proof.go_etcd_io.etcd.client.v3.InvTxnBuilder

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_dist

open Iris Iris.BI Net client go_etcd_io.etcd.api.v3 go_etcd_io.etcd.server.v3.etcdserver

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- **`Txn_Commit_dist`: `(*txn).Commit()` of a transaction built on the client's `*kv`**
(mirrors `txn.Commit.spec` at `dup = false`, server side `etcdTxnSpecW`): the builder's state
`txnObjAt … b` over the client's endpoints and `txnKvIs` of its `*kv` (what `kv.Txn`, `If`, `Then`,
`Else` give, proved, no call), auth off. -/
abbrev Txn_Commit_dist.spec : Prop :=
  ∀ [π : NetProtoGS] (cl api txn_ptr : Loc) (eps : List GoString) (V : WEnv GF) (Γ : DistView)
    (ctx : GoInterfaceOk) (ctx_desc : context.ContextDesc (IProp GF)) (b : TxnBuild)
    (Q : KVState → IProp GF),
  Γ.auth = false →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ levelTok 0 ∗
      kvClientAt cl api eps V Γ ∗
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

end spec

end etcd_dist
end EtcdGrove
end Perennial
