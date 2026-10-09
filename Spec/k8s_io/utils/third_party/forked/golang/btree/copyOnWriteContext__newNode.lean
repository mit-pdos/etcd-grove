module
public import Proof.k8s_io.utils.third_party.forked.golang.btree.Defs
public import Proof.k8s_io.utils.third_party.forked.golang.btree.Model
public import Proof.k8s_io.utils.third_party.forked.golang.btree.Init

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace btree

open Iris Iris.BI k8s_io.utils.third_party.forked.golang.btree

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.utils.third_party.forked.golang.btree.Assumptions]

/-- `(*copyOnWriteContext[T]).newNode()`: an empty node owned by the context. -/
abbrev copyOnWriteContext.newNode.spec : Prop :=
  ∀ {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] {T : go.GoType}
    [IntoValTyped (GF := GF) V T] {K : Type} (o : ItemOrder GF V K) (c f : Loc) (less : GoFunc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.utils.third_party.forked.golang.btree ∗ isCow o c f less }}
    (App (Val (c @!! go.GoType.PointerType (copyOnWriteContext.ty T) @!! go!"newNode"))
      (Val #()))
  {{ (n : Loc), RET #n; nodeShallow (V := V) (K := K) c (DFrac.own 1) n [] [] }}

end spec

end btree
end EtcdGrove
end Perennial
