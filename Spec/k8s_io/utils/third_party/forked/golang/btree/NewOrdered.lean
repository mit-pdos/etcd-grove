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

/-- `NewOrdered[T](degree)`: an empty tree of an ordered type, by `<`. -/
abbrev NewOrdered.spec : Prop :=
  ∀ {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] {T : go.GoType}
    [IntoValTyped (GF := GF) V T] (ltb : V → V → Bool)
    (hord : StrictOrder (fun a b => ltb a b = true)),
  (∀ a b : V, ⟦GoOp GoLt T, (#a, #b)⟧ ⤳[under] #(ltb a b)) →
  ∀ (degree : w64), 1 < sint.Z degree → sint.Z degree ≤ 2 ^ 62 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.utils.third_party.forked.golang.btree }}
    (App (Val #(functions NewOrdered [T])) (Val #degree))
  {{ (t : Loc), RET #t; ownBTree (orderedOrder (GF := GF) _ hord) t (DFrac.own 1) [] }}

end spec

end btree
end EtcdGrove
end Perennial
