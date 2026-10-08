import EtcdGrove.Btree.Defs
import EtcdGrove.Btree.Model
import EtcdGrove.Btree.Init

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Btree

open Iris Iris.BI github_com.google.btree

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.google.btree.Assumptions]

/-- `(*BTreeG[T]).minItems()`: `degree - 1`. -/
abbrev BTreeG.minItems.spec : Prop :=
  ∀ {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] {T : go.GoType}
    [IntoValTyped (GF := GF) V T] (t : Loc) (dq : DFrac) (tv : BTreeG V),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.google.btree ∗ t ↦{dq} tv }}
    (App (Val (t @!! go.GoType.PointerType (BTreeG.ty T) @!! go!"minItems")) (Val #()))
  {{ RET #(tv.degree' - W64 1); t ↦{dq} tv }}

end spec

end Btree
end EtcdGrove
end Perennial
