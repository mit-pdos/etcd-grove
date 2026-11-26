/-
`(*txn).Commit()` across machines, auth on, auth on, at the cluster view (F7, `notes/etcd-dist-f7.md`; an interim trust-boundary axiom until #24's S2
client side: `Proof/github_com/mit_pdos/etcd_grove/examples/etcd/dist/TxnCommitOnDist.lean`). Moved from the drafts of `AuthViewDist.lean`, whose definitions it is
written in. Lean-first (no Rocq counterpart).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.AuthViewDist

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial
namespace EtcdGrove
namespace etcd_dist
namespace authd

open Iris Iris.BI Net client go_etcd_io.etcd.api.v3 go_etcd_io.etcd.server.v3.etcdserver

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- **`Txn_CommitOn_dist`: `(*txn).Commit()` across machines, auth on** (mirrors
`client.client_txn_on` at the cluster, in `Txn_Commit_dist`'s statement; linearizable only:
`txnSerializable = false` in the read-only case). A read-only transaction's update is `□ AU` (resent at the
next endpoint on `Unavailable`), its success the member's check (`txnReadCheckedD`); a writing one's is
`writeAuD` (resent after a token refresh), its success the grant of `irrTxn` (`writeCheckedD`, nested
operations included). The error arm claims nothing.

An interim trust-boundary axiom (F7, the lead's approval #50 2026-11-26T06:08Z;
`Proof/github_com/mit_pdos/etcd_grove/examples/etcd/dist/TxnCommitOnDist.lean`). Reviews (`notes/axiom-review/`): first `f7-a.md` (`d946f6cbda`: UNSOUND, the member names a free binder `A`; fixed by `Γ.au`), then `f7-rerev-a.md` (`6d9d9fd662`): SOUND (condition C, the Serve tie). Unchanged since (`f7-changed-since-review.md`). -/
abbrev Txn_CommitOn_dist.spec : Prop :=
  ∀ [NetProtoGS] (cl api txn_ptr : Loc) (eps : List GoString) (V : WEnv GF) (Γ : DistView)
    (cfg : go_etcd_io.etcd.client.v3.Config) (γR : ServerRaftNames)
    (L₀ : List EntryModel) (ctx : GoInterfaceOk) (ctx_desc : context.ContextDesc (IProp GF)) (om : GrpcMd)
    (b : TxnBuild) (Q : KVState → IProp GF),
  (∀ a b : w64, Γ.au a = Γ.au b → a = b) →
  Γ.auth = true → γR.raft.log = Γ.kv.rlog → outTokOk (principalOf cfg) om →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ levelTok 0 ∗
      userClientAt cl api eps V Γ cfg ∗ metadata.outMD ctx om ∗ srvReqLogLb γR L₀ ∗
      txnObjAt txn_ptr eps ctx ctx_desc b ∗ txnKvIs txn_ptr api ∗
      ⌜TxnModel.plain b.model ∧ txnModelIn (txnWireOf b.model)⌝ ∗
      ((⌜txn.txnReadonly (txnWireOf b.model) = true ∧ txn.txnSerializable (txnWireOf b.model) = false⌝ ∗
          □ AU <{ ∃∃ (σ : KVState), etcdKV Γ.kv σ }> @ (⊤ \ ↑srvRaftN) \ ↑kvN, ∅
            <{ etcdKV Γ.kv σ ∗ ⌜kvRoom σ⌝, COMM □ Q σ }>) ∨
        (⌜txn.txnReadonly (txnWireOf b.model) = false ∧ txn.txnPlain (txnWireOf b.model) ∧
            txnNoZeroEnd (txnWireOf b.model)⌝ ∗
          writeAuD Γ.kv (principalOf cfg) (.txn (txnWireOf b.model)) L₀ Q)) ∗
      ⌜txnSizeOk (txnWireOf b.model)⌝ }}
    (App (Val (txn_ptr @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.txn.ty @!! go!"Commit"))
      (Val #()))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); levelTok 0 ∗
      ((⌜err = GoInterface.nil⌝ ∗ ∃ (m : TxnRespM) (σ : KVState), txnRespMsg resp m ∗
        (if txn.txnReadonly (txnWireOf b.model) then iprop(□ Q σ) else Q σ) ∗
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
        client.txnRevLb Γ.kv (txnWireOf b.model) m ∗
        (if txn.txnReadonly (txnWireOf b.model) then
          txnReadCheckedD eps Γ γR (principalOf cfg) L₀ (txnWireOf b.model)
        else iprop(∃ tw : txn.TxnModelW, ⌜tw.toModel = txnWireOf b.model⌝ ∗
          writeCheckedD eps Γ γR (principalOf cfg) (irrTxn tw) L₀))) ∨
      ⌜err ≠ GoInterface.nil ∧ resp = null⌝) }}

/-! ### KV read -/

end spec

end authd
end etcd_dist
end EtcdGrove
end Perennial
