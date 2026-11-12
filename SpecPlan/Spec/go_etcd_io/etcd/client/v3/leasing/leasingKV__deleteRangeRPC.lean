/-
`(*leasingKV).deleteRangeRPC` (`kv.go`): `If(CreateRevision(pfx++key..pfx++end) < maxLeaseRev+1)
.Then(OpGet(key, WithRange(end), WithKeysOnly()), OpDelete(key, WithRange(end)))`. Proof sketch: the
inner `Commit` with the caller's update: success is the range delete without `prevKv` (`execReq`;
the get before it reads the same store; valid by `kvStep`'s `t.valid`), failure aborts; on error `EvictRange`; on success
`leaseCache.Delete` of each key (header copied). Changes: from `specs-ref`'s `leasingKV__deleteRangeRPC.lean`: restated over `isLeasingKV`/`Internal.lean` (was the cache's log states and the history premise); weakened to what the leasing contract's proofs need.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.client.v3.leasing.Internal

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

/-- `deleteRangeRPC(ctx, maxLeaseRev, key, end)` for the range delete `d` of `[key, end)`: nothing
(`nil`, `nil`: the guard failed), an error, or the delete committed. -/
def leasingKV.deleteRangeRPC.spec : Prop :=
  ∀ (lkv : Loc) (γ : Cluster) (who p : Principal) (lo : Nat) (pfx : Key) (γL : LeasingNames) (ctx : GoInterface) (maxLeaseRev : w64) (key «end» : GoString) (d : DeleteReq)
    (Q : State → State → Resp → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.leasing ∗ isLeasingKV lkv γ who pfx γL ∗ Context.ctxOk ctx ∗ ctxPrin who ctx p ∗ authLb γ lo ∗ ⌜d.key = key ∧ d.rangeEnd = «end» ∧ «end» ≠ []⌝ ∗
      lkvMarks γL (reqWrites (.deleteRange d)) ∗ □ AU <{ ∃∃ (σ : State), etcdState γ σ }> @ ⊤ \ ↑etcdN, ∅
        <{ ∀∀ (σ' : State) (r : Option Resp), lstep γL pfx p lo (.deleteRange d) σ σ' r ∗ etcdState γ σ',
           COMM LQ Q σ σ' r }> }}
    (App (App (App (App (Val (lkv @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.leasing.leasingKV.ty @!! go!"deleteRangeRPC")) (Val #ctx)) (Val #maxLeaseRev)) (Val #key)) (Val #«end»))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
      ⌜resp = null ∧ err = GoInterface.nil⌝ ∨ (∃ σ σ' res, Q σ σ' res ∗ deleteReply res resp err) ∨
      ⌜resp = null ∧ err ≠ GoInterface.nil⌝ }}

end spec

end Leasing
end EtcdGrove
end Perennial
