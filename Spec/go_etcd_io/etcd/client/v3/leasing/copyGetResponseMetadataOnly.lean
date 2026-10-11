/-
`copyGetResponseMetadataOnly(resp)` (`client/v3/leasing/util.go`). Lean-first (no Rocq counterpart); see `InvLeaseCache.lean`.
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
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.leasing.Assumptions]

/-- **`copyGetResponseMetadataOnly(resp)`** of the entry `e`'s response (read on any fraction): a
fresh response with a copy of its header, its `More` and `Count`, and no key-values. -/
abbrev copyGetResponseMetadataOnly.spec : Prop :=
  ∀ (e : LeaseEntry) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.leasing ∗ respOwn e dq }}
    (App (Val (@! go_etcd_io.etcd.client.v3.leasing.copyGetResponseMetadataOnly)) (Val #e.resp))
  {{ (r : Loc), RET #r; respOwn e dq ∗ ⌜r ≠ null⌝ ∗ ∃ h : Loc,
      structFieldRef etcdserverpb.RangeResponse go!"Header" r ↦ h ∗ hdrFull h e.hm ∗
      structFieldRef etcdserverpb.RangeResponse go!"Kvs" r ↦ slice.nil ∗
      structFieldRef etcdserverpb.RangeResponse go!"More" r ↦ e.more ∗
      structFieldRef etcdserverpb.RangeResponse go!"Count" r ↦ e.count }}

end spec

end leasing
end EtcdGrove
end Perennial
