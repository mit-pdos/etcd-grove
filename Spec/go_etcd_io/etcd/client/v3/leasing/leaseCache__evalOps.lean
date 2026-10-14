/-
`leaseCache.evalOps(ops)` (`client/v3/leasing/cache.go`). Lean-first (no Rocq counterpart); see `InvLeaseCache.lean`.
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
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [EM : EtcdModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.leasing.Assumptions]

/-- **`lc.evalOps(ops)`**, called with the read lock held: if every operation is a get the cache
serves, of a cached key (`leaseEvalOk`), the cached answers in fresh `ResponseOp`s, in order;
otherwise `(nil, false)`. -/
abbrev leaseCache.evalOps.spec : Prop :=
  ∀ (lc : Loc) (st : LeaseCacheSt) (dq : DFrac) (sl : GoSlice) (os : List OpFull),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.leasing ∗ lcOwn lc st dq ∗ ⌜LeaseCacheWf st⌝ ∗ opsAt sl os }}
    (App (Val (lc @!! go.GoType.PointerType leaseCache.ty @!! go!"evalOps")) (Val #sl))
  {{ (rs : GoSlice) (ok : Bool), RET (PairV #rs #ok); lcOwn lc st dq ∗
      ⌜ok = leaseEvalOk st os⌝ ∗
      (⌜ok = false ∧ rs = slice.nil⌝ ∨
       (⌜ok = true⌝ ∗ ∃ ps : List Loc, rs ↦* ps ∗ ⌜ps.length = os.length⌝ ∗
         [∗list] i ↦ p ∈ ps, ∃ (o : OpFull) (e : LeaseEntry),
           ⌜os[i]? = some o ∧ st.entries !! o.key = some e⌝ ∗ respOpFresh p o e)) }}

end spec

end leasing
end EtcdGrove
end Perennial
