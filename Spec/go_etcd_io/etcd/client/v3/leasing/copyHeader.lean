/-
`copyHeader(hdr)` (`client/v3/leasing/util.go`). Lean-first (no Rocq counterpart); see `InvLeaseCache.lean`.
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

/-- **`copyHeader(hdr)`**: `nil` for `nil`, otherwise a fresh header with `hdr`'s fields (read-only
from then on: the cache shares it). -/
abbrev copyHeader.spec : Prop :=
  ∀ (h : Loc) (hm : HdrM),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.leasing ∗ headerOk h hm }}
    (App (Val (@! go_etcd_io.etcd.client.v3.leasing.copyHeader)) (Val #h))
  {{ (h' : Loc), RET #h'; (⌜h = null ∧ h' = null⌝ ∨ (⌜h ≠ null⌝ ∗ hdrFull h' hm)) }}

end spec

end leasing
end EtcdGrove
end Perennial
