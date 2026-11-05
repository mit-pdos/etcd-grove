/-
The proof of `Spec/go_etcd_io/bbolt/Cursor__Next.lean`: (U6h, `notes/bbolt-proof-plan.md`): split on `T.rw`;
the reader's case OPEN (two shared statements too weak, `wp_reader`), the writer's U6w's.
-/
module

public import Spec.go_etcd_io.bbolt.Cursor__Next

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- **A reader's `Next`**: OPEN (U6h's report). Two shared statements are too weak: `rCurPos`
(`Read/PosDefs`) admits a stack past its leaf's end in the middle of the bucket (`rPosAt els i i`,
`i < (rEnts v bv).length`), from which Go's `next` returns entry `i`, not `i + 1`; and
`Cursor.next_r`'s post past the last entry gives the stack at some position (`∃ i'`), where `Next`
at the last entry needs it unchanged (at `len - 1`) and `Seek` past the end at `len`. -/
theorem Cursor.Next.wp_reader [HasExt osFsExt]
    (tx c : Loc) (γ : BoltName) (q : Qp) (T : TxView) (es : List BoltEnt) (pos : Option Nat)
    (hro : T.rw = false) :
  {{ boltTx (GF := GF) tx γ q T ∗ boltCur tx γ c T es pos }}
    (App (Val (c @!! go.GoType.PointerType Cursor.ty @!! go!"Next")) (Val #()))
  {{ (k v : GoSlice), RET (PairV #k #v); boltTx tx γ q T ∗
      (match pos with
       | none => iprop(boltCur tx γ c T es none ∗ ⌜k = slice.nil ∧ v = slice.nil⌝)
       | some i => iprop(boltCur tx γ c T es (some (if i + 1 < es.length then i + 1 else i)) ∗
           curAt tx γ es (i + 1) k v)) }} := by
  sorry

/-- **A writer's `Next`**: U6w's (`Cursor.Next.wp_writer`, `Read/PubW*`). -/
theorem Cursor.Next.wp_writer [HasExt osFsExt]
    (tx c : Loc) (γ : BoltName) (q : Qp) (T : TxView) (es : List BoltEnt) (pos : Option Nat)
    (hrw : T.rw = true) :
  {{ boltTx (GF := GF) tx γ q T ∗ boltCur tx γ c T es pos }}
    (App (Val (c @!! go.GoType.PointerType Cursor.ty @!! go!"Next")) (Val #()))
  {{ (k v : GoSlice), RET (PairV #k #v); boltTx tx γ q T ∗
      (match pos with
       | none => iprop(boltCur tx γ c T es none ∗ ⌜k = slice.nil ∧ v = slice.nil⌝)
       | some i => iprop(boltCur tx γ c T es (some (if i + 1 < es.length then i + 1 else i)) ∗
           curAt tx γ es (i + 1) k v)) }} := by
  sorry

theorem Cursor.Next.wp_proof : Cursor.Next.spec (GF := GF) (hG := hG) := by
  intro _ tx c γ q T es pos
  by_cases hrw : T.rw = true
  · exact Cursor.Next.wp_writer tx c γ q T es pos hrw
  · exact Cursor.Next.wp_reader tx c γ q T es pos (Bool.eq_false_iff.2 hrw)

end proof

end bbolt
end EtcdGrove
end Perennial
