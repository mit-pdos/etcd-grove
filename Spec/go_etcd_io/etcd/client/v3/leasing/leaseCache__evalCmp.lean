/-
`leaseCache.evalCmp(cmps)` (`client/v3/leasing/cache.go`). Lean-first (no Rocq counterpart); see `InvLeaseCache.lean`.
-/
module

public import Proof.go_etcd_io.etcd.client.v3.leasing.InvLeaseEval

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace leasing

open Iris Iris.BI go_etcd_io.etcd.client.v3.leasing go_etcd_io.etcd.api.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.leasing.Assumptions]

/-- **`lc.evalCmp(cmps)`**, called with the read lock held (the caller owns a fraction of the
state `st`): `leaseEvalCmps st` of the comparisons. -/
abbrev leaseCache.evalCmp.spec : Prop :=
  ∀ (lc : Loc) (st : LeaseCacheSt) (dq : DFrac) (sl : GoSlice) (ms : List CmpModel),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.leasing ∗ lcOwn lc st dq ∗ ⌜LeaseCacheWf st⌝ ∗ cmpsSetAt sl ms }}
    (App (Val (lc @!! go.GoType.PointerType leaseCache.ty @!! go!"evalCmp")) (Val #sl))
  {{ (b ok : Bool), RET (PairV #b #ok); lcOwn lc st dq ∗ ⌜(b, ok) = leaseEvalCmps st ms⌝ }}

end spec

end leasing
end EtcdGrove
end Perennial
