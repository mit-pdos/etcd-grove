/- Lean-first (no Rocq counterpart).

# Taking named files after a crash, with no old resources (`notes/wal-fsext-w4c-plan.md`, "W4c U3 log")

`crashRest_take_named`: the new generation's start resources of files the new tree names, not yet
taken, without the old generation's resources of them (`crashRest_take_list` takes those too, for the
facts of the crash it proves; a file whose new contents nothing needs, the crash boot's non-segment
files, needs none). Each is a file of the new state, being named (`crashRest`'s `Named` part).
-/
module

public import GooseLang.Ext.Fs.CrashTakeFiles

@[expose] public section

noncomputable section

namespace Perennial
namespace Fs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode

section crash
variable {GF : BundledGFunctors}

variable (hL hL' : OsGS GF)

/-- **Taking named files at a fixed crash**, with no old resources. -/
theorem crashRestAt_take_named (Q : OsState → OsState → Prop) (tt : Bool) (V' : Hist)
    (st st' : OsState) :
    ∀ (xs D : List Ino), (∀ i ∈ xs, i ∉ D) → xs.Nodup → (∀ i ∈ xs, Named V'.now i) →
    crashRestAt Q hL hL' D tt V' st st' ⊢
      ([∗list] i ∈ xs, ∃ f, fileStart hL' i f) ∗
        crashRestAt Q hL hL' (xs ++ D) tt V' st st'
  | [], D, _, _, _ => by
    iintro Hr
    simp only [List.nil_append]
    iframe Hr
    iapply BigSepL.bigSepL_nil.2; iempintro
  | i :: xs, D, hD, hnd, hn => by
    have hi : i ∉ D := hD i (List.mem_cons_self ..)
    have hnd' := List.nodup_cons.1 hnd
    have hD' : ∀ y ∈ xs, y ∉ i :: D := by
      intro y hy hm
      rcases List.mem_cons.1 hm with h | h
      · exact hnd'.1 (h ▸ hy)
      · exact hD y (List.mem_cons_of_mem _ hy) h
    iintro Hr
    iunfold crashRestAt at Hr
    icases Hr with ⟨%Γb, %Γm, %F, %Γf, %Γt, %hrel, Hab, Ham, Hfs, HAt, Htok, HAd, Ht⟩
    obtain ⟨hwf, hcoh, hcr, hQ, hF, hroots, hV, hnamed⟩ := hrel
    icases files_take hL' F i $$ Hfs with ⟨Hf, Hfs⟩
    have hFi := hF i hi
    obtain ⟨f, hf⟩ : ∃ f, st'.fs.files !! i = some f := by
      have h := hnamed i (hn i (List.mem_cons_self ..))
      cases e : st'.fs.files !! i with
      | none => rw [e] at h; cases h
      | some f => exact ⟨f, rfl⟩
    rw [hFi, hf]
    simp only [fileStartO]
    ihave Hr : crashRestAt Q hL hL' (i :: D) tt V' st st' $$ [Hab Ham Hfs HAt Htok HAd Ht]
    · unfold crashRestAt
      iexists Γb, Γm, GMap.delete i F, Γf, Γt
      iframe Hab Ham Hfs HAt Htok HAd Ht
      ipureintro
      exact ⟨hwf, hcoh, hcr, hQ, crashRest_files_delete hF, hroots, hV, hnamed⟩
    icases crashRestAt_take_named Q tt V' st st' xs (i :: D) hD' hnd'.2
      (fun y hy => hn y (List.mem_cons_of_mem _ hy)) $$ Hr with ⟨Hxs, Hr⟩
    isplitl [Hf Hxs]
    · iapply BigSepL.bigSepL_cons.2
      iframe Hxs
      iexists f; iexact Hf
    · iapply crashRestAt_mono hL Q hL' _ _ tt V' st st' _ $$ Hr
      intro q hq
      simp only [List.mem_append, List.mem_cons] at hq ⊢
      rcases hq with h | h | h
      · exact Or.inl (Or.inr h)
      · exact Or.inl (Or.inl h)
      · exact Or.inr h

/-- **Taking named files after a crash**, with no old resources: the files `xs` (distinct, named in
the new tree, none taken), each with its new start resources; the restart's resources with them
taken. -/
theorem crashRest_take_named (Q : OsState → OsState → Prop) (D : List Ino) (tt : Bool) (V' : Hist)
    (xs : List Ino) (hD : ∀ i ∈ xs, i ∉ D) (hnd : xs.Nodup) (hn : ∀ i ∈ xs, Named V'.now i) :
    crashRest Q hL hL' D tt V' ⊢
      ([∗list] i ∈ xs, ∃ f, fileStart hL' i f) ∗
        crashRest Q hL hL' (xs ++ D) tt V' := by
  iintro Hr
  icases (crashRest_at hL Q hL' D tt V').1 $$ Hr with ⟨%st, %st', Hr⟩
  icases crashRestAt_take_named hL hL' Q tt V' st st' xs D hD hnd hn $$ Hr with ⟨Hxs, Hr⟩
  iframe Hxs
  iapply (crashRest_at hL Q hL' _ tt V').2
  iexists st, st'
  iexact Hr

end crash

end Fs
end Perennial

end
