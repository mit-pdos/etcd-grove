/-
`(*leasingKV).get` (`kv.go`): `Get`'s and `Do`'s range. Proof sketch: not ready (`readySession`) or
not cacheable (`leaseCache.Get`: a bad op, or serializable) or recently revoked (`MayAcquire`):
`lkv.kv.Do` (W0's `KV.DoTriple`, the update restricted to `Step`, `LStep`'s first case); a cached
response (`leaseCache.Get`: `leaseGetM o me` of an entry `me` with `entryOk` and an `etcdLb γ σ0`):
the update opened at the current state, `Reach σ0 σ` (`etcdLb_reach`), committed with `σ' = σ` and
the answer `CachedRange1` (`some`): from `recAtHdr`, W0's serializable answer (the view at the
header's revision; `leaseGetM` is `RangeReq.answers` on one key, up to a keys-only answer's lease,
a pure fact), or with the key's mark the shape; else `acquire` (a protocol step), then `leaseCache.Add` (`leaseGetM`: still
`entryOk`) and a lease monitor (`wg.Add(1)` with the open token's share, the forked thread's
token deposited; `monitorLease`), or the plain get's response as is
(`issues/leasing-get-failed-acquire-options.md`): both fired as a cached answer at the current state.
Changes: from `specs-ref`'s `leasingKV__get.lean`: restated over `isLeasingKV`/`Internal.lean` (was the cache's log states and the history premise); weakened to what the leasing contract's proofs need.
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

/-- `get(ctx, op)` for a range `op`: as `LKV.GetTriple`. -/
def leasingKV.get.spec : Prop :=
  ∀ (lkv : Loc) (γ : Cluster) (who p : Principal) (lo : Nat) (pfx : Key) (γL : LeasingNames) (q : Qp) (ctx : GoInterface) (op : go_etcd_io.etcd.client.v3.Op) (o : OpM)
    (Q : State → State → Resp → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.leasing ∗ isLeasingKV lkv γ who pfx γL ∗ lkvOpen γL q ∗ Context.ctxOk ctx ∗ ctxPrin who ctx p ∗ authLb γ lo ∗ opAt op o ∗ ⌜o.t = tRange⌝ ∗ threadTok ∗
      □ AU <{ ∃∃ (σ : State), etcdState γ σ }> @ ⊤ \ ↑etcdN, ∅
        <{ ∀∀ (σ' : State) (r : Option Resp), lstep γL pfx p lo (.range o.rangeReq) σ σ' r ∗ etcdState γ σ',
           COMM LQ Q σ σ' r }> }}
    (App (App (Val (lkv @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.leasing.leasingKV.ty @!! go!"get")) (Val #ctx)) (Val #op))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); lkvOpen γL q ∗ threadTok ∗
      ((∃ σ σ' res, Q σ σ' res ∗ getReply res resp err) ∨ ⌜resp = null ∧ err ≠ GoInterface.nil⌝) }}

end spec

end Leasing
end EtcdGrove
end Perennial
