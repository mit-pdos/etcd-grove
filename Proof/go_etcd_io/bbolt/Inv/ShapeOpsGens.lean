/-
**The handles' generations across the writer's updates** (batch 37 item 14; `gensOK`,
`Inv/Tx`): a bucket's new contents (`TxView.setBkt` keeps the generations: `gensOK_setBkt`), a
change of the records that keeps the handles and the root bucket's cache (`gensOK_congr`: a
materialization, an entry put or delete, a free), and a bucket's open (`gensOK_bktOpened`: the new
handle at a generation no greater than its name's, its name's when opened from the root bucket).
-/
module

public import Proof.go_etcd_io.bbolt.Inv.Tx

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section gens
variable [GooseExts]

/-- **`TxView.setBkt` keeps the generations** (U7: `Put`'s, `Delete`'s, `CreateBucket`'s view). -/
theorem gensOK_setBkt (T : TxView) (X : WX) (n : GoString) (m : BktData) :
    gensOK (T.setBkt n m) X ↔ gensOK T X := Iff.rfl

/-- **The same handles and root bucket cache** (a materialization, an entry's update, a free). -/
theorem gensOK_congr (T : TxView) (X X' : WX) (hh : X'.handles = X.handles)
    (hloc : ∀ n, bktLoc X' n = bktLoc X n) (h : gensOK T X) : gensOK T X' := by
  refine ⟨fun b n g hb => h.1 b n g (by rw [← hh]; exact hb), fun n b hb => ?_,
    fun b n hb => ?_⟩
  · rw [hh]; exact h.2.1 n b (by rw [← hloc]; exact hb)
  · rw [hloc]; exact h.2.2 b n (by rw [← hh]; exact hb)

/-- **A bucket's open** (`bktOpened`, U6's `Bucket_w`): the new handle `(name, g)` at a generation
no greater than its name's, its name's when opened from the root bucket (`bl = X.rl`); the handles
were the transaction's buckets (`handlesOK`). -/
theorem gensOK_bktOpened (T : TxView) (X X' : WX) (bl c : Loc) (name : List w8) (g : Nat)
    (h : bktOpened X X' bl c name g) (hho : handlesOK X) (hg : g ≤ T.gen name)
    (hroot : bl = X.rl → g = T.gen name) (hnr : bl ≠ X.rl → g < T.gen name)
    (hok : gensOK T X) : gensOK T X' := by
  obtain ⟨B, C, w, hB, -, -, -, hbm, -, hcfresh, -, -, -, -, hCbm, -, -, -, hX'⟩ := h
  have hcnone : X.handles !! c = none := by
    cases e : X.handles !! c with
    | none => rfl
    | some p =>
      have := hho c p e
      rw [Option.isNone_iff_eq_none] at hcfresh; rw [hcfresh] at this; cases this
  have hbsc : X.t.bs !! c = none := by
    have := hcfresh; unfold WTx.bobjs at this; rw [GMap.lookup_union] at this
    cases e : X.t.bs !! c with
    | none => rfl
    | some _ => rw [e] at this; simp at this
  subst hX'
  refine ⟨?_, ?_, ?_⟩
  · intro b n g' hb
    simp only at hb
    by_cases e : c = b
    · subst e; rw [GMap.lookup_insert] at hb; cases hb; exact hg
    · rw [GMap.lookup_insert_ne _ _ e] at hb; exact hok.1 b n g' hb
  · intro n b hb
    simp only
    unfold bktLoc at hb; simp only at hb
    by_cases erc : c = X.rl
    · rw [erc, GMap.lookup_insert] at hb; simp only [Option.bind_some] at hb
      rw [hCbm] at hb; simp at hb
    rw [GMap.lookup_insert_ne _ _ erc] at hb
    by_cases erl : bl = X.rl
    · subst erl
      rw [GMap.lookup_insert] at hb; simp only [Option.bind_some] at hb
      by_cases en : name = n
      · subst en; rw [GMap.lookup_insert] at hb; cases hb
        rw [GMap.lookup_insert, hroot rfl]
      · rw [GMap.lookup_insert_ne _ _ en] at hb
        have hb' : bktLoc X n = some b := by unfold bktLoc; rw [hB]; exact hb
        have hh := hok.2.1 n b hb'
        have hcb : c ≠ b := by intro e; rw [← e, hcnone] at hh; cases hh
        rw [GMap.lookup_insert_ne _ _ hcb]; exact hh
    · rw [GMap.lookup_insert_ne _ _ erl] at hb
      have hh := hok.2.1 n b hb
      have hcb : c ≠ b := by intro e; rw [← e, hcnone] at hh; cases hh
      rw [GMap.lookup_insert_ne _ _ hcb]; exact hh
  · -- D1: a handle at its name's current generation is the root cache's bucket
    intro b n hb
    simp only at hb
    unfold bktLoc; simp only
    by_cases e : c = b
    · subst e
      rw [GMap.lookup_insert] at hb
      simp only [Option.some.injEq, Prod.mk.injEq] at hb
      obtain ⟨rfl, hgg⟩ := hb
      have erl : bl = X.rl := by
        by_cases hne : bl = X.rl
        · exact hne
        · have := hnr hne; omega
      subst erl
      have erc : ¬ c = X.rl := by intro e; rw [e, hB] at hbsc; cases hbsc
      rw [GMap.lookup_insert_ne _ _ erc, GMap.lookup_insert]
      simp only [Option.bind_some]
      rw [GMap.lookup_insert]
    · rw [GMap.lookup_insert_ne _ _ e] at hb
      have hl := hok.2.2 b n hb
      unfold bktLoc at hl
      by_cases erc : c = X.rl
      · rw [← erc, hbsc] at hl; simp at hl
      rw [GMap.lookup_insert_ne _ _ erc]
      by_cases erl : bl = X.rl
      · subst erl
        rw [GMap.lookup_insert]; simp only [Option.bind_some]
        rw [hB] at hl; simp only [Option.bind_some] at hl
        by_cases en : name = n
        · subst en; rw [hbm] at hl; cases hl
        · rw [GMap.lookup_insert_ne _ _ en]; exact hl
      · rw [GMap.lookup_insert_ne _ _ erl]; exact hl

end gens

end bbolt
end EtcdGrove
end Perennial
