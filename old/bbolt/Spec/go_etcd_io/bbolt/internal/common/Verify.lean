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

/-- `Verify(f)` runs the optional check `f` if the environment asks for it: so `Q` must
follow from `f` returning, and hold if it does not run. -/
abbrev Verify.spec : Prop :=
  ∀ (f : GoFunc) (Q : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common ∗ (WP (App (Val #f) (Val #())) {{ fun _ => Q }} ∧ Q) }}
    (App (Val #(functions Verify [])) (Val #f))
  {{ RET #(); Q }}

end spec

end bbolt
end EtcdGrove
end Perennial
