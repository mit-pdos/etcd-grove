/-
The proof of `Spec/os/File__Truncate.lean`: the model's `EINTR` loop, by Löb induction, over
`wp_osFtruncateStart` and `wp_osFtruncateFinish`. An attempt that did not land leaves the `OsMeta`
as its first step announced it, which a further attempt announces again (`announce_idem`); after
one that landed, a further attempt is a resize to the size the file has (`rsPost_rsPost`).
-/
module

public import Proof.os.ErrorOk
public import Spec.os.File__Truncate

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open Fs

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [os.Assumptions]

/-- What an attempt from a state that has not landed leaves, when it lands. -/
theorem rsDone_ftDone (p : Ino) (m m0 : OsMeta) (tg n : Nat)
    (hm0 : m0 = m ∨ m0 = m.announce (min m.size tg) (max m.size tg) tg) :
    rsDone (GF := GF) p tg tg m0 n ⊢ os.ftDone p m tg := by
  have hsz : m0.size = m.size := by rcases hm0 with rfl | rfl <;> simp
  have hmaps : m0.maps = m.maps := by rcases hm0 with rfl | rfl <;> simp
  have hpost : rsPost m0 tg tg = rsPost m tg tg := by
    rcases hm0 with rfl | rfl
    · rfl
    · exact os.rsPost_announce m tg tg
  unfold rsDone os.ftDone
  iintro ⟨%zs, %hzs, Hm, Hb, Hc⟩
  iexists zs.map (fun c0 => c0 ++ [(0, n)])
  rw [hpost, hsz, hmaps, List.map_map]
  iframe
  ipureintro; rw [List.length_map, hzs.1, hsz]

/-- The state of the loop: no attempt landed yet (the `OsMeta` is `m`, or as an attempt announced
it; the bytes to cut off have `xs`'s values), or one did. -/
def ftState (p : Ino) (m : OsMeta) (tg : Nat) (xs : List ByteG) : IProp GF :=
  iprop((∃ (m0 : OsMeta) (xs0 : List ByteG),
      ⌜(m0 = m ∨ m0 = m.announce (min m.size tg) (max m.size tg) tg) ∧
        xs0.map Prod.fst = xs.map Prod.fst ∧ xs0.length = m.size - tg⌝ ∗
      osMeta p (DFrac.own 1) m0 ∗ osBytes p (min m.size tg) (DFrac.own 1) xs0 ∗
      mcellsAny m.maps (min m.size tg) (max m.size tg)) ∨
    os.ftDone p m tg)

theorem os.File.Truncate.wp_proof : os.File.Truncate.spec (GF := GF) (hG := hG) := by
  intro f fd name dqf sz dq d m xs hfd0 hwr hsz hxs
  unfold os.ownFile
  wp_start as ⟨#Hinv, ⟨%inner, #Hf, Hfd, #Hn⟩, Hosfd, Hm, Hb, Hc⟩
  unfold os.model.inner
  rw [os.file_ty_eq, os.File_ty_eq]
  try rw [os.file_ty_eq, os.File_ty_eq]
  ihave #Hf2 := Hf
  iStructNamed Hf2
  wp_auto
  have h1 : ¬ (sint.Z fd < sint.Z (W64 0)) := by
    rw [show sint.Z (W64 0) = 0 from rfl]; exact Int.not_lt.2 hfd0
  rw [decide_eq_false h1]
  wp_auto
  have h2 : ¬ (sint.Z sz < sint.Z (W64 0)) := by
    rw [show sint.Z (W64 0) = 0 from rfl]; exact Int.not_lt.2 hsz
  rw [decide_eq_false h2]
  wp_auto
  ihave HS : ftState d.ino m sz.toNat xs $$ [Hm Hb Hc]
  · unfold ftState; ileft; iexists m, xs; iframe; ipureintro; exact ⟨.inl rfl, rfl, hxs⟩
  iloeb as IH generalizing HS Hosfd Hfd HΦ
  unfold ftState
  icases HS with (⟨%m0, %xs0, %hm0, Hm, Hb, Hc⟩ | Hd)
  · obtain ⟨hm0, hv, hl⟩ := hm0
    have hsz0 : m0.size = m.size := by rcases hm0 with rfl | rfl <;> simp
    have hmaps0 : m0.maps = m.maps := by rcases hm0 with rfl | rfl <;> simp
    wp_apply wp_osFtruncateStart fd sz dq d m0 xs0 CoPset.subseteq_top hwr hsz (by rw [hsz0]; exact hl)
      $$ Hinv Hosfd Hm [Hb] [Hc] as %t %n %- Hosfd Ht
    · rw [hsz0]; iexact Hb
    · rw [hsz0, hmaps0]; iexact Hc
    wp_apply wp_osFtruncateFinish t d.ino sz.toNat m0 xs0 n CoPset.subseteq_top $$ Hinv Ht as %e Hr
    have hann : m0.announce (min m0.size sz.toNat) (max m0.size sz.toNat) sz.toNat =
        m.announce (min m.size sz.toNat) (max m.size sz.toNat) sz.toNat := by
      rw [hsz0]; rcases hm0 with rfl | rfl
      · rfl
      · exact os.announce_idem _ _ _ _
    ihave Hr : (⌜e = 0⌝ ∗ os.ftDone d.ino m sz.toNat) ∨
        (⌜e ≠ 0⌝ ∗ (os.ftDone d.ino m sz.toNat ∨
          (∃ xs1 : List ByteG, ⌜xs1.map Prod.fst = xs.map Prod.fst ∧ xs1.length = m.size - sz.toNat⌝ ∗
            osMeta d.ino (DFrac.own 1) (m.announce (min m.size sz.toNat) (max m.size sz.toNat) sz.toNat) ∗
            osBytes d.ino (min m.size sz.toNat) (DFrac.own 1) xs1 ∗
            mcellsAny m.maps (min m.size sz.toNat) (max m.size sz.toNat)))) $$ [Hr]
    · unfold rsUndone
      icases Hr with (⟨%he, Hd⟩ | ⟨%he, (Hd | ⟨Hm, Hb, Hc⟩)⟩)
      · ileft; isplitr; · ipureintro; exact he
        iapply rsDone_ftDone _ m m0 _ n hm0 $$ Hd
      · iright; isplitr; · ipureintro; exact he
        ileft; iapply rsDone_ftDone _ m m0 _ n hm0 $$ Hd
      · iright; isplitr; · ipureintro; exact he
        iright; iexists rsAnn n xs0
        rw [hann, hsz0, hmaps0]
        ihave Hc := mcells_any _ _ _ _ $$ Hc
        iframe
        ipureintro
        refine ⟨?_, by rw [rsAnn_length]; exact hl⟩
        rw [← hv]; simp [rsAnn, List.map_map, Function.comp_def]
    by_cases he4 : e = W64 4
    · rw [decide_eq_true he4]
      wp_auto
      icases Hr with (⟨%he, -⟩ | ⟨-, HS⟩)
      · exact absurd (he4 ▸ he) (by decide)
      iapply IH $$ [HS] Hosfd Hfd HΦ
      icases HS with (H | ⟨%xs1, %hxs1, Hm, Hb, Hc⟩)
      · iright; iexact H
      · ileft; iexists _, xs1; iframe; ipureintro; exact ⟨.inr rfl, hxs1⟩
    · rw [decide_eq_false he4]
      wp_auto
      icases Hr with (⟨%he, Hg⟩ | ⟨%he, HS⟩)
      · subst he
        rw [show decide ((0 : w64) = W64 0) = true from decide_eq_true rfl]
        simp only [Bool.not_true]
        wp_auto
        ihave #Hokn := (EtcdGrove.fmtErrorOkOrNil_nil (GF := GF))
        iapply HΦ
        iframe Hokn
        iframe
        isplitl []
        · isplitl [] <;> iassumption
        ileft
        iframe
        ipureintro; rfl
      · have he0' : ¬ e = W64 0 := he
        rw [decide_eq_false he0']
        wp_auto
        wp_apply os.wp_wrapErrno_ok _ inner name e he0' $$ Hn as %pe #Hok
        ihave #Hokn := EtcdGrove.fmtErrorOkOrNil_of _ $$ Hok
        iapply HΦ
        iframe Hokn
        iframe
        isplitl []
        · isplitl [] <;> iassumption
        iright
        isplitr
        · ipureintro; intro h; cases h
        icases HS with (H | ⟨%xs1, %hxs1, Hm, Hb, Hc⟩)
        · ileft; iexact H
        · iright; unfold os.ftUndone; iexists xs1; iframe; ipureintro; exact hxs1.1
  · -- a further attempt after one that landed: a resize to the size the file has
    iunfold os.ftDone at Hd
    icases Hd with ⟨%zs, %hzs, Hm, Hbs, Hcs⟩
    have hdsz : (rsPost m sz.toNat sz.toNat).size = sz.toNat := rfl
    have hdmaps : (rsPost m sz.toNat sz.toNat).maps = m.maps := by simp [rsPost]
    ihave Hc0 := os.mcellsAny_nil (GF := GF) m.maps sz.toNat sz.toNat (Nat.le_refl _)
    wp_apply wp_osFtruncateStart fd sz dq d (rsPost m sz.toNat sz.toNat) [] CoPset.subseteq_top hwr hsz
      (by rw [hdsz]; simp) $$ Hinv Hosfd Hm [] [Hc0] as %t %n %- Hosfd Ht
    · unfold osBytes; iapply (bytesG_nil _ _ _ _).2; iempintro
    · rw [hdsz, hdmaps, Nat.min_self, Nat.max_self]; iexact Hc0
    wp_apply wp_osFtruncateFinish t d.ino sz.toNat _ [] n CoPset.subseteq_top $$ Hinv Ht as %e Hr
    ihave Hm : osMeta d.ino (DFrac.own 1) (rsPost m sz.toNat sz.toNat) $$ [Hr]
    · unfold rsDone rsUndone
      icases Hr with (⟨-, ⟨%_, -, Hm, -, -⟩⟩ | ⟨-, (⟨%_, -, Hm, -, -⟩ | ⟨Hm, -, -⟩)⟩)
      · rw [os.rsPost_rsPost]; iexact Hm
      · rw [os.rsPost_rsPost]; iexact Hm
      · rw [os.announce_rsPost]; iexact Hm
    ihave Hd : os.ftDone d.ino m sz.toNat $$ [Hm Hbs Hcs]
    · unfold os.ftDone; iexists zs; iframe; ipureintro; exact hzs
    by_cases he4 : e = W64 4
    · rw [decide_eq_true he4]
      wp_auto
      iapply IH $$ [Hd] Hosfd Hfd HΦ
      iright; iexact Hd
    · rw [decide_eq_false he4]
      wp_auto
      by_cases he0 : e = W64 0
      · rw [decide_eq_true he0]
        simp only [Bool.not_true]
        wp_auto
        ihave #Hokn := (EtcdGrove.fmtErrorOkOrNil_nil (GF := GF))
        iapply HΦ
        iframe Hokn
        iframe
        isplitl []
        · isplitl [] <;> iassumption
        ileft
        iframe
        ipureintro; rfl
      · rw [decide_eq_false he0]
        wp_auto
        wp_apply os.wp_wrapErrno_ok _ inner name e he0' $$ Hn as %pe #Hok
        ihave #Hokn := EtcdGrove.fmtErrorOkOrNil_of _ $$ Hok
        iapply HΦ
        iframe Hokn
        iframe
        isplitl []
        · isplitl [] <;> iassumption
        iright
        ipureintro; intro h; cases h

end proof

end EtcdGrove
end Perennial
