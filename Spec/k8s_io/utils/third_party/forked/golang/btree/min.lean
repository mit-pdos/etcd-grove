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

/-- `min[T](n)`: the smallest item of the tree rooted at `n` (`nil` for none). -/
abbrev min.spec : Prop :=
  ∀ {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] {T : go.GoType}
    [IntoValTyped (GF := GF) V T] {K : Type} (o : ItemOrder GF V K) (c f : Loc) (less : GoFunc) (d : Nat) (dq : DFrac) (n : Loc) (s : List (V × K)),
  2 ≤ d →
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.utils.third_party.forked.golang.btree ∗ ownRoot o c f less d dq n s }}
    (App (Val #(functions min [T])) (Val #n))
  {{ RET (PairV #((s.head?.map Prod.fst).getD (zero_val V)) #(!s.isEmpty));
      ownRoot o c f less d dq n s }}

end spec

end btree
end EtcdGrove
end Perennial
