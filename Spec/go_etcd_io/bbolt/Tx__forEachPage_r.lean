/-
`Tx.forEachPage_r` (bbolt, internal): its spec (U0b of `notes/bbolt-proof-plan.md`, a frozen
cross-unit contract). Proved by U6; used by U10 (`tx_check`'s `checkInvariantProperties`). Proof:
`Proof/go_etcd_io/bbolt/Tx__forEachPage_r.lean` (a `sorry` until U6).
-/
module

public import Proof.go_etcd_io.bbolt.Inv.Ctx

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [ExtSemantics fsExt] [FsSemOk] [hos : HasExt fsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- `tx.forEachPage(root, fn)` of a reader, over a well-formed tree of its view: `fn` runs on each
page of the walk in order (`pageWalk`: the page's location, its depth, and the stack of page ids
from the root, read at some fraction), with the invariant `I i` before the `i`-th. -/
abbrev Tx.forEachPage_r.spec : Prop :=
  ∀ (K : BC) (tx : Loc) (src : PairSrc) (q : Qp) (T : TxView) (v : View) (root : w64)
    (fn : GoFunc) (I : Nat → IProp GF),
  (∃ hwm, treeWF v.pages hwm root.toNat) →
  {{ rdTxK (GF := GF) K tx src q T v ∗ I 0 ∗
      □ (∀ (i id : Nat) (ids : List Nat) (stk : GoSlice) (dq : DFrac),
          {{ rdTxK K tx src q T v ∗ I i ∗ stk ↦*{dq} (ids.map fun x : Nat => W64 (x : Int)) ∗
              ⌜(pageWalk v.pages root.toNat)[i]? = some (id, ids)⌝ }}
            (App (App (App (Val #fn) (Val #(pageLoc v id)))
              (Val #(W64 ((ids.length - 1 : Nat) : Int)))) (Val #stk))
          {{ RET #(); rdTxK K tx src q T v ∗ I (i + 1) ∗
              stk ↦*{dq} (ids.map fun x : Nat => W64 (x : Int)) }}) }}
    (App (App (Val (tx @!! go.GoType.PointerType Tx.ty @!! go!"forEachPage")) (Val #root))
      (Val #fn))
  {{ RET #(); rdTxK K tx src q T v ∗ I (pageWalk v.pages root.toNat).length }}

end spec

end bbolt
end EtcdGrove
end Perennial
