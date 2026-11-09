/-
`(*leasingKV).delete` (`kv.go`): `Delete`'s and `Do`'s delete. Proof sketch: `waitSession`; a range:
`deleteRange`; one key: as `put` (`tryModifyOp`, else `revoke`), then `leaseCache.Delete` with the
reply's header (copied). Changes: from `specs-ref`'s `leasingKV__delete.lean`: restated over `isLeasingKV`/`Internal.lean` (was the cache's log states and the history premise); weakened to what the leasing contract's proofs need.
-/
module

public import Spec.go_etcd_io.etcd.client.v3.leasing.Internal

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Leasing

open Iris Iris.BI EtcdModel EtcdWire ClientV3
open Classical

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.leasing.Assumptions]

/-- `delete(ctx, op)` for a delete `op`: as `LKV.DeleteTriple`. -/
def leasingKV.delete.spec : Prop :=
  ∀ (lkv : Loc) (γ : Cluster) (who p : Principal) (lo : Nat) (pfx : Key) (γL : LeasingNames) (ctx : GoInterface) (op : go_etcd_io.etcd.client.v3.Op) (o : OpM)
    (Q : State → State → Resp → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.leasing ∗ isLeasingKV lkv γ who pfx γL ∗ Context.ctxOk ctx ∗ ctxPrin who ctx p ∗ authLb γ lo ∗ opAt op o ∗ ⌜o.t = tDeleteRange⌝ ∗
      lkvMarks γL (reqWrites (.deleteRange o.deleteReq)) ∗ threadTok ∗
      □ AU <{ ∃∃ (σ : State), etcdState γ σ }> @ ⊤ \ ↑etcdN, ∅
        <{ ∀∀ (σ' : State) (r : Option Resp), lstep γL pfx p lo (.deleteRange o.deleteReq) σ σ' r ∗ etcdState γ σ',
           COMM LQ Q σ σ' r }> }}
    (App (App (Val (lkv @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.leasing.leasingKV.ty @!! go!"delete")) (Val #ctx)) (Val #op))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); threadTok ∗
      ((∃ σ σ' res, Q σ σ' res ∗ deleteReply res resp err) ∨ ⌜resp = null ∧ err ≠ GoInterface.nil⌝) }}

end spec

end Leasing
end EtcdGrove
end Perennial
