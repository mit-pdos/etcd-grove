/- Lean-first (no Rocq counterpart). Lemmas of the client programs' proofs (`testMinibolt`,
`testMiniboltConcurrent`): the absent file `Open` lays out, one reader token out of `Open`'s,
the committer token as `dbOwnerOpt`, and reads under `valueOkP`. -/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.bboltfs.Open
public import Spec.github_com.mit_pdos.etcd_grove.examples.bboltfs.valueOk
public import Proof.github_com.mit_pdos.etcd_grove.examples.bboltfs.OpenLemmas

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bboltfs

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode github_com.mit_pdos.etcd_grove.examples.bboltfs

theorem w64_of_toNat (x : w64) (n : Nat) (h : x.toNat = n) : x = W64 (n : Int) := by
  subst h; apply BitVec.eq_of_toNat_eq; simp

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt osFsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.bboltfs.Assumptions]

theorem dbOwnerOpt_some (γ : DBNames) (t n : Nat) :
    dbOwnerOpt (GF := GF) γ (some (t, n)) = dbOwner (GF := GF) γ t n := rfl

theorem dbTx_vp (γ : DBNames) (t : Nat) (vo : Option w64) :
    dbTx (GF := GF) γ t vo ⊢ ⌜γ.vp t vo⌝ := by
  unfold dbTx; iintro ⟨-, %H⟩; ipureintro; exact H

/-- A read of transaction `x ≥ 2` (the txid is the token's), under `valueOkP`: `x` holding `x`. -/
theorem read_val (vp : Nat → Option w64 → Prop) (Hvp : vp = valueOkP) (x txid v : w64) (has : Bool)
    (h2 : 2 ≤ x.toNat) (htx : txid.toNat = x.toNat) (H : vp txid.toNat (if has then some v else none)) :
    txid = x ∧ has = true ∧ v = x := by
  have hx : txid = x := BitVec.eq_of_toNat_eq htx
  subst hx Hvp
  refine ⟨rfl, ?_⟩
  simp only [valueOkP, if_neg (show ¬ txid.toNat ≤ 1 by omega)] at H
  cases has
  · simp at H
  · simp only [if_true, Option.some.injEq] at H
    exact ⟨rfl, by rw [H]; exact (w64_of_toNat txid _ rfl).symm⟩

theorem valueOkP_next (x : w64) (h2 : 2 ≤ x.toNat) : valueOkP (x.toNat - 1 + 1) (some x) := by
  rw [show x.toNat - 1 + 1 = x.toNat by omega]
  simp only [valueOkP, if_neg (show ¬ x.toNat ≤ 1 by omega)]
  rw [← w64_of_toNat x _ rfl]

/-- No file: `Open` lays one out, at transaction 1 with no value, high water mark 4. -/
theorem dbFile_absent (p : GoString) :
    osMeta (GF := GF) p (DFrac.own 1) none ⊢ dbFile (GF := GF) p 1 none 4 := by
  iintro Hm
  unfold dbFile dbFresh
  ileft
  iexists none, []
  iframe Hm
  isplitr
  · dsimp only; iempintro
  ipureintro
  refine ⟨fun _ => rfl, fun m h => absurd h (by simp), ?_⟩
  simp only [freshTx, List.length_nil]
  rw [if_neg (by omega)]

end lemmas

end bboltfs
end EtcdGrove
end Perennial
