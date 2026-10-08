import EtcdGrove.Btree.Defs
import EtcdGrove.Btree.Model
import EtcdGrove.Btree.Init
import EtcdGrove.Btree.Item

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

/-- `(*copyOnWriteContext[T]).newNode()`: an empty node owned by the context. -/
abbrev copyOnWriteContext.newNode.spec : Prop :=
  ∀ {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] {T : go.GoType}
    [IntoValTyped (GF := GF) V T] {K : Type} (o : ItemOrder GF V K) (c f : Loc) (less : GoFunc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.google.btree ∗ isCow o c f less }}
    (App (Val (c @!! go.GoType.PointerType (copyOnWriteContext.ty T) @!! go!"newNode"))
      (Val #()))
  {{ (n : Loc), RET #n; nodeShallow (V := V) (K := K) c (DFrac.own 1) n [] [] }}

end spec

end Btree
end EtcdGrove
end Perennial
