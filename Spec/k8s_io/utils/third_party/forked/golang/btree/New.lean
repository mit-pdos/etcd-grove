/-
`btree.New[T](degree, less)`, of `k8s.io/utils/third_party/forked/golang/btree` (translated names-only:
the trust boundary). Lean-first (no Rocq counterpart); see `InvBtree.lean`.
-/
module

public import Proof.go_etcd_io.etcd.cache.v3.InvBtree

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.cache.v3 k8s_io.utils.third_party.forked.golang

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

/-- `btree.New[T](degree, less)` (`New` → `NewWithFreeList(degree, less,
NewFreeList(DefaultFreeListSize))`): an empty tree, for `degree > 1` (Go panics with "bad
degree" otherwise) and a `LessFunc` closure `less` deciding a strict weak order
`lessR` (`btLessSpec`; Go's documentation: "It should implement a strict ordering"). -/
abbrev btree.New.spec : Prop :=
  ∀ {T' : Type} [ZeroVal T'] [TypedPointsto (GF := GF) T'] (T : go.GoType)
    [IntoValTyped (GF := GF) T' T] {V : Type}
    (degree : w64) (less : GoFunc) (isItem : T' → V → IProp GF) [∀ p v, Persistent (isItem p v)]
    (lessR : V → V → Prop) [DecidableRel lessR],
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.utils.third_party.forked.golang.btree ∗
      ⌜1 < sint.Z degree⌝ ∗ ⌜StrictWeakOrder lessR⌝ ∗ btLessSpec less isItem lessR }}
    (App (App (Val #(functions btree.New [T])) (Val #degree)) (Val #less))
  {{ (t : Loc), RET #t; ownBTree T t isItem lessR [] (DFrac.own 1) }}

end spec

end EtcdGrove
end Perennial
