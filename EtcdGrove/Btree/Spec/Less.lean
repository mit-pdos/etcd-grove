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

/-- `Less[T]()`: `func(a, b T) bool { return a < b }`, for an ordered `T` whose `<` is a
strict total order (integers and strings; not floats, whose NaN is unordered). -/
abbrev Less.spec : Prop :=
  ∀ {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] {T : go.GoType}
    [IntoValTyped (GF := GF) V T] (ltb : V → V → Bool)
    (hord : StrictOrder (fun a b => ltb a b = true)),
  (∀ a b : V, ⟦GoOp GoLt T, (#a, #b)⟧ ⤳[under] #(ltb a b)) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.google.btree }}
    (App (Val #(functions Less [T])) (Val #()))
  {{ (less : GoFunc), RET #less; isLess (orderedOrder (GF := GF) _ hord) less }}

end spec

end Btree
end EtcdGrove
end Perennial
