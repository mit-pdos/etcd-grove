/-
`leaseCache.Get(ctx, op)` (`client/v3/leasing/cache.go`). Lean-first (no Rocq counterpart); see `InvLeaseCache.lean`.
-/
module

public import Proof.go_etcd_io.etcd.client.v3.leasing.InvLeaseCache

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

/-- **`lc.Get(ctx, op)`**: `(nil, false)` for an operation the cache does not serve (`isBadOp`);
otherwise `ok = true` and either `nil` (no entry for the key, or the context was done while
waiting), or, after waiting for the entry's waiter channel, the cached get's answer of the entry
`e` as it is in the state `st` of the second read (still the key's entry, or frozen since:
evicted after it was found), with its facts. -/
abbrev leaseCache.Get.spec : Prop :=
  ∀ (lc : Loc) (γ : LeaseCacheNames) (pfx : GoString) (X : LeaseCacheSt → Qp → IProp GF)
    (Qr : LeaseCacheSt → IProp GF) (ctx : GoInterfaceOk) (cs : context.ContextDesc (IProp GF)) (opv : go_etcd_io.etcd.client.v3.Op) (o : OpFull),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.leasing ∗ isLeaseCache lc γ pfx X ∗ leaseCacheReader lc γ pfx X ∗ lcPeek X Qr ∗
      context.isContext ctx cs ∗ opFullAt opv o }}
    (App (App (Val (lc @!! go.GoType.PointerType leaseCache.ty @!! go!"Get")) (Val #(GoInterface.ok ctx))) (Val #opv))
  {{ (ret : Loc) (ok : Bool), RET (PairV #ret #ok); leaseCacheReader lc γ pfx X ∗
      ((⌜isBadOpM o = true ∧ ret = null ∧ ok = false⌝) ∨
       (⌜isBadOpM o = false ∧ ok = true ∧ ret = null⌝) ∨
       (⌜isBadOpM o = false ∧ ok = true⌝ ∗ ∃ (st : LeaseCacheSt) (e : LeaseEntry),
          □ Qr st ∗ ⌜st.entries !! o.key = some e ∨ (o.key, e) ∈ st.frozen⌝ ∗
          entryFacts pfx o.key e ∗ freshGetResp ret e.hm e.more e.count (getResult o e))) }}

end spec

end leasing
end EtcdGrove
end Perennial
