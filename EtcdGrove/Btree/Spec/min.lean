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

/-- `min[T](n)`: the smallest item of the tree rooted at `n` (`nil` for none). -/
abbrev min.spec : Prop :=
  ∀ {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] {T : go.GoType}
    [IntoValTyped (GF := GF) V T] {K : Type} (o : ItemOrder GF V K) (c f : Loc) (less : GoFunc) (d : Nat) (dq : DFrac) (n : Loc) (s : List (V × K)),
  2 ≤ d →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.google.btree ∗ ownRoot o c f less d dq n s }}
    (App (Val #(functions min [T])) (Val #n))
  {{ RET (PairV #((s.head?.map Prod.fst).getD (zero_val V)) #(!s.isEmpty));
      ownRoot o c f less d dq n s }}

end spec

end Btree
end EtcdGrove
end Perennial
