/-
Taking several files after a crash at once (`crashRest_take_list`). Untrusted.

`crashRest_take_runs_keep` gives each file its own existential crashed state (`CrashSeenR`); a
premise on the crash that speaks of several files at once (the WAL's W1, over a directory's
segments) needs one crashed state for all of them. `crashRestAt` is `crashRest` with the crashed
state `st` and the new state `st'` fixed (`crashRest_at`); taking files from it keeps them, so
the facts of every file taken are about the same crash (`FileCrashAt`), with the premise `Q st st'`
and the new tree (`st'.fs.treeDur = V'.now`).
-/
module

public import GooseLang.Ext.Fs.CrashTok

@[expose] public section

noncomputable section

namespace Perennial
namespace Fs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode

section crash
variable {GF : BundledGFunctors}

/-- `crashRest` with the crashed state `st` and the new state `st'` fixed. -/
def crashRestAt (Q : OsState → OsState → Prop) (hL hL' : OsGS GF) (D : List Ino) (tt : Bool)
    (V' : Hist) (st st' : OsState) : IProp GF :=
  iprop(∃ (Γb : GMap (Ino × Nat) ByteG) (Γm : GMap Ino OsMeta) (F : GMap Ino OsFile)
      (Γf : GMap w64 OsFd) (Γt : GMap Nat TokInfo) (V : Hist),
    ⌜OsWf st ∧ OsCoh st Γb Γm Γf Γt ∧ OsCrash st st' ∧ Q st st' ∧
      (∀ i, i ∉ D → F !! i = st'.fs.files !! i) ∧
      st'.fs.roots = st.fs.roots ∧ TreeCrashed V V' ∧
      (∀ i, Named V'.now i → (st'.fs.files !! i).isSome) ∧ st'.fs.treeDur = V'.now⌝ ∗
    gAuth hL hL.γb Γb ∗ gAuth hL hL.γm Γm ∗ ([∗map] i ↦ f ∈ F, fileStart hL' i f) ∗
    gAuth hL hL.γt Γt ∗ tokRes hL Γt ∗
    gAuth hL hL.γd (histMap (st.fs.roots, V)) ∗ treeLeft hL' st.fs.roots V' tt ∗
    crashMode hL st V V')

/-- What the crash from `st` to `st'` did to the file `i`, the old generation knowing its `OsMeta`
as `m` and its bytes as the runs `rs`: `FileCrashedR`; named in the new tree, it is there; it was a
file of `st`, whose candidates are the runs' if `m` has no sync cut, and whose resize stamps include
those `m` knows. -/
def FileCrashAt (st st' : OsState) (V' : Hist) (i : Ino) (m : OsMeta)
    (rs : List (Nat × DFrac × List ByteG)) : Prop :=
  FileCrashedR m rs (st'.fs.files !! i) ∧ (Named V'.now i → (st'.fs.files !! i).isSome) ∧
  ∃ f, st.fs.files !! i = some f ∧ (m.cut = none →
    ∀ r ∈ rs, ∀ k (hk : k < r.2.2.length), f.cand (r.1 + k) = (r.2.2[k]).2) ∧
    ∀ s ∈ m.rz, s ∈ f.rzs

variable (hL : OsGS GF)

theorem crashRest_at (Q : OsState → OsState → Prop) (hL' : OsGS GF) (D : List Ino) (tt : Bool)
    (V' : Hist) :
    crashRest Q hL hL' D tt V' ⊣⊢ ∃ st st', crashRestAt Q hL hL' D tt V' st st' := by
  unfold crashRest crashRestAt
  constructor
  · iintro ⟨%Γb, %Γm, %F, %st, %st', %Γf, %Γt, %V, %hrel, H⟩
    iexists st, st', Γb, Γm, F, Γf, Γt, V
    iframe H
    ipureintro; exact hrel
  · iintro ⟨%st, %st', %Γb, %Γm, %F, %Γf, %Γt, %V, %hrel, H⟩
    iexists Γb, Γm, F, st, st', Γf, Γt, V
    iframe H
    ipureintro; exact hrel

theorem crashRestAt_facts (Q : OsState → OsState → Prop) (hL' : OsGS GF) (D : List Ino)
    (tt : Bool) (V' : Hist) (st st' : OsState) :
    ⊢ crashRestAt Q hL hL' D tt V' st st' -∗
      ⌜Q st st' ∧ st'.fs.treeDur = V'.now⌝ ∗ crashRestAt Q hL hL' D tt V' st st' := by
  unfold crashRestAt
  iintro ⟨%Γb, %Γm, %F, %Γf, %Γt, %V, %hrel, H⟩
  isplitr
  · ipureintro; exact ⟨hrel.2.2.2.1, hrel.2.2.2.2.2.2.2.2⟩
  iexists Γb, Γm, F, Γf, Γt, V
  iframe H
  ipureintro; exact hrel

/-- Files taken are only excluded: more may be counted as taken. -/
theorem crashRestAt_mono (Q : OsState → OsState → Prop) (hL' : OsGS GF) (D D' : List Ino)
    (tt : Bool) (V' : Hist) (st st' : OsState) (hD : ∀ i, i ∈ D → i ∈ D') :
    crashRestAt Q hL hL' D tt V' st st' ⊢ crashRestAt Q hL hL' D' tt V' st st' := by
  unfold crashRestAt
  iintro ⟨%Γb, %Γm, %F, %Γf, %Γt, %V, %hrel, H⟩
  iexists Γb, Γm, F, Γf, Γt, V
  iframe H
  ipureintro
  obtain ⟨hwf, hcoh, hcr, hQ, hF, hroots, htc, hnamed, htd⟩ := hrel
  exact ⟨hwf, hcoh, hcr, hQ, fun i hi => hF i (fun h => hi (hD i h)), hroots, htc, hnamed, htd⟩

/-- **Taking a file** from the restart's resources at a fixed crash, keeping its old resources. -/
theorem crashRestAt_take (Q : OsState → OsState → Prop) (hL' : OsGS GF) (D : List Ino)
    (tt : Bool) (V' : Hist) (st st' : OsState) (i : Ino) (hi : i ∉ D) (dq : DFrac) (m : OsMeta)
    (rs : List (Nat × DFrac × List ByteG)) :
    ⊢ crashRestAt Q hL hL' D tt V' st st' -∗ gElem hL hL.γm i dq m -∗
      ([∗list] r ∈ rs, bytesG hL i r.1 r.2.1 r.2.2) -∗
      ⌜FileCrashAt st st' V' i m rs⌝ ∗ fileStartO hL' i (st'.fs.files !! i) ∗
        crashRestAt Q hL hL' (i :: D) tt V' st st' ∗
        gElem hL hL.γm i dq m ∗ ([∗list] r ∈ rs, bytesG hL i r.1 r.2.1 r.2.2) := by
  unfold crashRestAt
  iintro ⟨%Γb, %Γm, %F, %Γf, %Γt, %V, %hrel, Hab, Ham, Hfs, HAt, Htok, HAd, Ht⟩ Hm Hbs
  obtain ⟨hwf, hcoh, hcr, hQ, hF, hroots, htc, hnamed, htd⟩ := hrel
  icases gAuth_lookup hL _ _ _ _ _ $$ Ham Hm with %hmo
  icases bytesG_lookup_runs hL i Γb rs $$ Hab Hbs with %hxs
  icases tokRes_meta_whole hL $$ Htok Hm with %hnt
  icases files_take hL' F i $$ Hfs with ⟨Hf, Hfs⟩
  have hFi := hF i hi
  have hseen : CrashSeenR Q i m rs [] (F !! i) :=
    ⟨st, st', Γb, Γm, Γf, Γt, hwf, hcoh, hcr, hQ, hFi.symm, hmo, hxs,
      fun t ti ht hp => absurd hp (hnt t ti ht), fun _ h => nomatch h⟩
  rw [hFi] at hseen
  rw [hFi]
  iframe Hf Hm Hbs
  isplitr
  · ipureintro
    refine ⟨crashSeen_crashed hseen, fun hn => hnamed i hn, ?_⟩
    obtain ⟨f, hf, hmok⟩ := hcoh.meta_some i m hmo
    refine ⟨f, hf, fun hcut r hr k hk => ?_, hmok.rz⟩
    obtain ⟨f1, hf1, -, -, -, hrel⟩ := hcoh.bytes i _ _ (hxs r hr k hk)
    simp only [OsState.file, hf, Option.some.injEq] at hf1
    subst hf1
    have hc : cutOf Γm i = none := by simp [cutOf, hmo, hcut]
    rw [hc] at hrel
    exact hrel
  iexists Γb, Γm, GMap.delete i F, Γf, Γt, V
  iframe Hab Ham Hfs HAt Htok HAd Ht
  ipureintro
  exact ⟨hwf, hcoh, hcr, hQ, crashRest_files_delete hF, hroots, htc, hnamed, htd⟩

/-- The old resources of a file a client takes: a fraction of its `OsMeta`, its bytes in runs. -/
def fileOld (x : Ino × DFrac × OsMeta × List (Nat × DFrac × List ByteG)) : IProp GF :=
  iprop(gElem hL hL.γm x.1 x.2.1 x.2.2.1 ∗ [∗list] r ∈ x.2.2.2, bytesG hL x.1 r.1 r.2.1 r.2.2)

/-- **Taking files** at a fixed crash. -/
theorem crashRestAt_take_list (Q : OsState → OsState → Prop) (hL' : OsGS GF) (tt : Bool)
    (V' : Hist) (st st' : OsState) :
    ∀ (xs : List (Ino × DFrac × OsMeta × List (Nat × DFrac × List ByteG))) (D : List Ino),
    (∀ x ∈ xs, x.1 ∉ D) → (xs.map (·.1)).Nodup →
    ⊢ crashRestAt Q hL hL' D tt V' st st' -∗ ([∗list] x ∈ xs, fileOld hL x) -∗
      ⌜∀ x ∈ xs, FileCrashAt st st' V' x.1 x.2.2.1 x.2.2.2⌝ ∗
        ([∗list] x ∈ xs, fileStartO hL' x.1 (st'.fs.files !! x.1)) ∗
        crashRestAt Q hL hL' (xs.map (·.1) ++ D) tt V' st st' ∗ ([∗list] x ∈ xs, fileOld hL x)
  | [], D, _, _ => by
    iintro Hr Hx
    isplitr
    · ipureintro; intro x hx; cases hx
    simp only [List.map_nil, List.nil_append]
    iframe Hr Hx
    iapply BigSepL.bigSepL_nil.2; iempintro
  | x :: xs, D, hD, hnd => by
    have hx : x.1 ∉ D := hD x (List.mem_cons_self ..)
    have hnd' := List.nodup_cons.1 (show (x.1 :: xs.map (·.1)).Nodup from hnd)
    have hD' : ∀ y ∈ xs, y.1 ∉ x.1 :: D := by
      intro y hy hm
      rcases List.mem_cons.1 hm with h | h
      · exact hnd'.1 (h ▸ List.mem_map_of_mem hy)
      · exact hD y (List.mem_cons_of_mem _ hy) h
    iintro Hr Hxs
    icases BigSepL.bigSepL_cons.1 $$ Hxs with ⟨Hx, Hxs⟩
    iunfold fileOld at Hx
    icases Hx with ⟨Hm, Hb⟩
    icases crashRestAt_take hL Q hL' D tt V' st st' x.1 hx x.2.1 x.2.2.1 x.2.2.2 $$ Hr Hm Hb
      with ⟨%h1, Hf, Hr, Hm, Hb⟩
    icases crashRestAt_take_list Q hL' tt V' st st' xs (x.1 :: D) hD' hnd'.2 $$ Hr Hxs
      with ⟨%h2, Hfs, Hr, Hxs⟩
    isplitr
    · ipureintro
      intro y hy
      rcases List.mem_cons.1 hy with rfl | hy
      · exact h1
      · exact h2 y hy
    isplitl [Hf Hfs]
    · iapply BigSepL.bigSepL_cons.2; iframe
    isplitl [Hr]
    · iapply crashRestAt_mono hL Q hL' _ _ tt V' st st' _ $$ Hr
      intro i hi
      simp only [List.mem_append, List.mem_map, List.mem_cons, List.map_cons] at hi ⊢
      rcases hi with h | h | h
      · exact Or.inl (Or.inr h)
      · exact Or.inl (Or.inl h)
      · exact Or.inr h
    iapply BigSepL.bigSepL_cons.2
    iframe
    unfold fileOld; iframe

/-- **Taking files after a crash, all at the same crash**: from the restart's resources, the old
resources of the files `xs` (distinct, none taken): one crashed state `st` and new state `st'`, the
premise `Q st st'`, the new tree the new history's, each file's `FileCrashAt`, each new file's start
resources; the restart's resources with the files taken, the old resources back. -/
theorem crashRest_take_list (Q : OsState → OsState → Prop) (hL' : OsGS GF) (D : List Ino)
    (tt : Bool) (V' : Hist) (xs : List (Ino × DFrac × OsMeta × List (Nat × DFrac × List ByteG)))
    (hD : ∀ x ∈ xs, x.1 ∉ D) (hnd : (xs.map (·.1)).Nodup) :
    ⊢ crashRest Q hL hL' D tt V' -∗ ([∗list] x ∈ xs, fileOld hL x) -∗
      ∃ st st', ⌜Q st st' ∧ st'.fs.treeDur = V'.now ∧
          ∀ x ∈ xs, FileCrashAt st st' V' x.1 x.2.2.1 x.2.2.2⌝ ∗
        ([∗list] x ∈ xs, fileStartO hL' x.1 (st'.fs.files !! x.1)) ∗
        crashRest Q hL hL' (xs.map (·.1) ++ D) tt V' ∗ ([∗list] x ∈ xs, fileOld hL x) := by
  iintro Hr Hxs
  icases (crashRest_at hL Q hL' D tt V').1 $$ Hr with ⟨%st, %st', Hr⟩
  icases crashRestAt_facts hL Q hL' D tt V' st st' $$ Hr with ⟨%hf, Hr⟩
  icases crashRestAt_take_list hL Q hL' tt V' st st' xs D hD hnd $$ Hr Hxs
    with ⟨%h, Hfs, Hr, Hxs⟩
  iexists st, st'
  iframe Hfs Hxs
  isplitr
  · ipureintro; exact ⟨hf.1, hf.2, h⟩
  iapply (crashRest_at hL Q hL' _ tt V').2
  iexists st, st'
  iexact Hr

end crash

end Fs
end Perennial

end
