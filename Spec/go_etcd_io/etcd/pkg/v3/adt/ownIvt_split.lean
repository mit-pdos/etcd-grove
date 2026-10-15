/-
The interval tree's ownership is fractional, its parts agreeing (`Defs.lean`'s `ownIvt`). Lean-first (no Rocq
counterpart); see `Model.lean`, `Defs.lean`. Not a Go function: a property of the opaque
`ownIvt`, stated as a pending spec. Pending: proved in unit 4 (the tree's proof, where
`ownIvt` gets its definition); until then a hypothesis of every result that reaches it (`?` in
`etc/link-lean-first-adt.txt`), as the contract's triples are.
-/
module

public import Proof.go_etcd_io.etcd.pkg.v3.adt.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.pkg.v3.adt

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.pkg.v3.adt.Assumptions]

/-- The tree's ownership splits and combines by fractions, and two parts agree on the
entries (the watcher groups under the watchable store's read lock: `ownWatcherGroup_fractional`). -/
abbrev adt.ownIvt_split.spec : Prop :=
  (∀ (t : Loc) (L : List adt.Entry) (q1 q2 : Qp),
    adt.ownIvt (GF := GF) t L (q1 + q2) ⊣⊢ adt.ownIvt t L q1 ∗ adt.ownIvt t L q2) ∧
  (∀ (t : Loc) (L1 L2 : List adt.Entry) (q1 q2 : Qp),
    adt.ownIvt (GF := GF) t L1 q1 ∗ adt.ownIvt t L2 q2 ⊢ ⌜L1 = L2⌝)

end spec

end EtcdGrove
end Perennial
