module
public import Proof.go_etcd_io.bbolt.internal.freelist.Model

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI go_etcd_io.bbolt.internal.freelist

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.internal.freelist.Assumptions]

/-- `t.pendingPageIds()`: the pending map. -/
abbrev shared.pendingPageIds.spec : Prop :=
  ∀ (s : Loc) (sv : shared) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.freelist ∗ s ↦{dq} sv }}
    (App (Val (s @!! go.GoType.PointerType shared.ty @!! go!"pendingPageIds")) (Val #()))
  {{ RET #sv.pending'; s ↦{dq} sv }}

end spec

end bbolt
end EtcdGrove
end Perennial
