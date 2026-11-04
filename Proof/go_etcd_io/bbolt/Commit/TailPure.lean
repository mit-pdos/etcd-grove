/-
`Commit`'s pure steps after `rebalance` (U10j of `notes/bbolt-proof-plan.md`): the root bucket's
children at the spill's start (from `wrFacts` and `gensOK`, kept by `rebalance`), and what a remap
inside `commitFreelist`'s `allocate` keeps of the records (`writable`, the root bucket).
-/
module

public import Proof.go_etcd_io.bbolt.Mmap.RemapRec
public import Proof.go_etcd_io.bbolt.Inv.Tx

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

set_option linter.unusedSectionVars false

section pure
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **The root bucket's children at the spill's start** (`spillStartOK`'s last clause): no cached
child is the root bucket (`wrFacts`), and no two names share a child (`gensOK`), of `X`'s root
bucket, whose `bm` `rebalance` keeps. -/
theorem cm_root_children (T : TxView) (X X1 : WX) (hg : gensOK T X)
    (hnr : ∀ B, X.t.bs !! X.rl = some B → ∀ k c, B.bm !! k = some c → c ≠ X.rl)
    (hrl : X1.rl = X.rl)
    (hbm : (X1.t.bs !! X.rl).map BRec.bm = (X.t.bs !! X.rl).map BRec.bm) :
    ∀ B0, X1.t.bs !! X1.rl = some B0 → (∀ k c, B0.bm !! k = some c → c ≠ X1.rl) ∧
      ∀ k k' c, B0.bm !! k = some c → B0.bm !! k' = some c → k = k' := by
  intro B0 hB0
  rw [hrl] at hB0 ⊢
  rw [hB0] at hbm
  obtain ⟨B, hB, hBm⟩ : ∃ B, X.t.bs !! X.rl = some B ∧ B.bm = B0.bm := by
    revert hbm
    cases h : X.t.bs !! X.rl with
    | none => simp
    | some B => intro e; simp only [Option.map_some, Option.some.injEq] at e; exact ⟨B, rfl, e.symm⟩
  refine ⟨fun k c hk => hnr B hB k c (by rw [hBm]; exact hk), fun k k' c hk hk' => ?_⟩
  have h1 : bktLoc X k = some c := by unfold bktLoc; rw [hB]; simp only [Option.bind_some, hBm]; exact hk
  have h2 : bktLoc X k' = some c := by
    unfold bktLoc; rw [hB]; simp only [Option.bind_some, hBm]; exact hk'
  exact (gensOK_bktLoc_inj T X hg k k' c h1 h2).symm

/-- **A remap keeps the records' `writable` flag and their root bucket** (`commitFreelist`'s
second rollback entailment: `wtxEnd`'s facts after a failed remap). -/
theorem cm_derefKeep (X Xd : WX) (b : Loc) (hd : derefRel X Xd) (hwr : X.t.t.writable' = true)
    (hrl : (X.t.bs !! X.rl).isSome) :
    (Xd.rebase b).t.t.writable' = true ∧ ((Xd.rebase b).t.bs !! (Xd.rebase b).rl).isSome := by
  refine ⟨by rw [derefRel_rebase_tt X Xd b hd]; exact hwr, ?_⟩
  have hrl' : (Xd.rebase b).rl = X.rl := hd.2.2.2.2.2.1
  rw [hrl', (derefRel_rebase_root X Xd b hd).1]
  exact hrl

/-- **`allocate` keeps the transaction's struct, the root bucket and the txid** (`allocRes`:
`addPage` changes `pm`, `bufs` and the mark, a remap re-bases). -/
theorem allocRes_keep (X X' : WX) (fl fl' : FLPg) (txid : w64) (count : Nat) (p id : _)
    (h : allocRes X X' fl fl' txid count p id) :
    X'.t.t = X.t.t ∧ ((X'.t.bs !! X'.rl).isSome = (X.t.bs !! X.rl).isSome) ∧
      X'.t.mv.txid' = X.t.mv.txid' := by
  obtain ⟨-, -, Xr, hr, hc⟩ := h
  have hX' : ∃ h', X' = Xr.addPage id p count h' := by
    rcases hc with ⟨-, -, e⟩ | ⟨-, -, -, e⟩ <;> exact ⟨_, e⟩
  obtain ⟨h', rfl⟩ := hX'
  rcases hr with rfl | ⟨Xd, b, hd, rfl⟩
  · exact ⟨rfl, rfl, rfl⟩
  · refine ⟨derefRel_rebase_tt X Xd b hd, ?_, ?_⟩
    · show ((Xd.rebase b).t.bs !! (Xd.rebase b).rl).isSome = _
      rw [show (Xd.rebase b).rl = X.rl from hd.2.2.2.2.2.1, (derefRel_rebase_root X Xd b hd).1]
    · show Xd.t.mv.txid' = _
      rw [hd.2.2.2.2.2.2.1]

/-- No growth (`grow` not called). -/
theorem wdbGrown_refl (w : WDb) : wdbGrown w w :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, Nat.le_refl _, fun _ h => ⟨h, fun _ => rfl⟩⟩

end pure

end bbolt
end EtcdGrove
end Perennial
