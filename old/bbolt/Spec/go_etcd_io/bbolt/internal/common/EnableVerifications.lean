module
public import Proof.go_etcd_io.bbolt.internal.common.Init

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI go_etcd_io.bbolt.internal.common

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.internal.common.Assumptions]

/-- `EnableVerifications(..)` sets `BBOLT_VERIFY` to `t` and returns a function that restores it; calling that function
returns. -/
abbrev EnableVerifications.spec : Prop :=
  ∀ (t : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common }}
    (App (Val #(functions EnableVerifications [])) (Val #t))
  {{ (r : GoFunc), RET #r; □ WP (App (Val #r) (Val #())) {{ fun _ => iprop(True) }} }}

end spec

end bbolt
end EtcdGrove
end Perennial
