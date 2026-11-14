/-
The proof of `Spec/os/File__TruncateAu.lean` (I3b), no `sorry`: `File__Truncate.lean`'s Löb loop, its state
`ftStateH` at half (the caller's halves of an attempt's start state) and the tie `K`, each attempt
`wp_osFtruncateStart_auW` with the supply's `os.truncAuW` for that state (the halves and `K` handed
to it), then `wp_osFtruncateFinish_au` with the commit's update; the outcome's halves
(`os.truncOutH`) and `K` re-enter the loop on `EINTR` (`os.announce_idem`, `os.rsPost_announce`, `os.rsPost_rsPost`, `os.announce_rsPost`
relate the states to `m`'s). Lean-first.
-/
module

public import LinuxFs.Spec.os.File__TruncateAu
public import LinuxFs.Proof.os.ErrorOk

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

/-- The caller's half of a landed attempt from a state that had not landed is the landing from `m`. -/
theorem os.ftDoneH_of (p : Ino) (m m0 : OsMeta) (tg : Nat) (zs : List Cands)
    (hm0 : m0 = m ∨ m0 = m.announce (min m.size tg) (rsHi true m.size tg) tg) :
    os.ftDoneH (GF := GF) p m0 tg zs ⊢ os.ftDoneH p m tg zs := by
  have hsz : m0.size = m.size := by rcases hm0 with rfl | rfl <;> simp
  have hpost : rsPost true m0 tg tg = rsPost true m tg tg := by
    rcases hm0 with rfl | rfl
    · rfl
    · exact os.rsPost_announce true m tg tg
  unfold os.ftDoneH
  rw [hpost, hsz]

/-- A further attempt after one that landed (from `rsPost true m tg tg` up to the candidates known
past the size, nothing to cut off) leaves the landing from `m`, whatever its outcome. -/
theorem os.truncOutH_again (p : Ino) (m : OsMeta) (tc0 : GMap Nat Cands) (rz0 : List Nat) (tg n : Nat) (e : w64)
    (zs : List Cands) (hzs : zs.length = tg - m.size) :
    os.truncOutH (GF := GF) p tg ((rsPost true m tg tg).withTc tc0 rz0) [] n e ∗
      osBytes p m.size (DFrac.own (1 : Qp).half) (zs.map (fun c => ((0 : w8), c))) ⊢
      os.ftDoneH p m tg zs := by
  have hgo : ∀ zs' : List Cands,
      os.ftDoneH (GF := GF) p ((rsPost true m tg tg).withTc tc0 rz0) tg zs' ∗
      osBytes p m.size (DFrac.own (1 : Qp).half) (zs.map (fun c => ((0 : w8), c))) ⊢
      os.ftDoneH p m tg zs := by
    intro zs'
    unfold os.ftDoneH
    iintro ⟨⟨-, ⟨%tc, %rz, Hm⟩, -⟩, Hb⟩
    rw [rsPost_withTc, os.rsPost_rsPost]
    iframe
    ipureintro; exact hzs
  unfold os.truncOutH
  iintro ⟨Hr, Hb⟩
  icases Hr with (⟨-, %zs', Hd⟩ | ⟨-, (⟨%zs', Hd⟩ | Hu)⟩)
  · iapply hgo zs' $$ [Hd Hb]; iframe
  · iapply hgo zs' $$ [Hd Hb]; iframe
  · unfold os.ftUndoneH os.ftDoneH
    icases Hu with ⟨Hm, -⟩
    simp only [OsMeta.withTc_size]
    rw [← OsMeta.withTc_self (OsMeta.announce _ _ _ _), announce_withTc, os.announce_rsPost]
    iframe
    ipureintro; exact hzs

/-- The state of the loop, the caller's halves: no attempt landed yet (the `OsMeta` is `m`, or as
an attempt announced it; the bytes to cut off have `xs`'s values), or one did. -/
def ftStateH (p : Ino) (m : OsMeta) (tg : Nat) (xs : List ByteG) : IProp GF :=
  iprop((∃ (m0 : OsMeta) (xs0 : List ByteG),
      ⌜(m0 = m ∨ m0 = m.announce (min m.size tg) (rsHi true m.size tg) tg) ∧
        xs0.map Prod.fst = xs.map Prod.fst ∧ xs0.length = m.size - tg⌝ ∗
      osMeta p (DFrac.own (1 : Qp).half) m0 ∗ osBytes p (min m.size tg) (DFrac.own (1 : Qp).half) xs0) ∨
    ∃ zs, os.ftDoneH p m tg zs)

theorem os.File.Truncate.wp_proofAu : os.File.Truncate.specAu (GF := GF) (hG := hG) := by
  intro f fd name dqf sz dq d m xs K hfd0 hwr hsz hmaps hxs
  unfold os.truncSup
  unfold os.ownFile
  wp_start as ⟨#Hinv, ⟨%inner, #Hf, Hfd, #Hn⟩, Hosfd, Hm, Hb, HK, #Hsup⟩
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
  ihave HS : ftStateH d.ino m sz.toNat xs $$ [Hm Hb]
  · unfold ftStateH; ileft; iexists m, xs; iframe; ipureintro; exact ⟨.inl rfl, rfl, hxs⟩
  iloeb as IH generalizing HS HK Hosfd Hfd HΦ
  unfold ftStateH
  icases HS with (⟨%m0, %xs0, %hm0, Hm, Hb⟩ | ⟨%zs, Hd⟩)
  · obtain ⟨hm0, hv, hl⟩ := hm0
    have hsz0 : m0.size = m.size := by rcases hm0 with rfl | rfl <;> simp
    have hmaps0 : m0.maps = m.maps := by rcases hm0 with rfl | rfl <;> simp
    rw [← hsz0] at hl
    ihave Hb : osBytes d.ino (min m0.size sz.toNat) (DFrac.own (1 : Qp).half) xs0 $$ [Hb]
    · rw [hsz0]; iexact Hb
    ihave Hau := Hsup $$ %m0 %xs0 %hl HK Hm Hb
    unfold os.truncAuW
    wp_apply wp_osFtruncateStart_auW fd sz dq d m0 xs0 hwr hsz (by rw [hmaps0]; exact hmaps)
      hl _ $$ Hinv Hosfd Hau as %t %n %- Hosfd Hau
    wp_apply wp_osFtruncateFinish_au t d.ino sz.toNat m0 xs0 n _ $$ Hinv Hau as %e ⟨Hr, HK⟩
    rw [hsz0] at hl
    have hann : m0.announce (min m0.size sz.toNat) (rsHi true m0.size sz.toNat) sz.toNat =
        m.announce (min m.size sz.toNat) (rsHi true m.size sz.toNat) sz.toNat := by
      rw [hsz0]; rcases hm0 with rfl | rfl
      · rfl
      · exact os.announce_idem _ _ _ _
    ihave Hr : (⌜e = 0⌝ ∗ ∃ zs, os.ftDoneH d.ino m sz.toNat zs) ∨
        (⌜e ≠ 0⌝ ∗ ((∃ zs, os.ftDoneH d.ino m sz.toNat zs) ∨
          (∃ xs1 : List ByteG, ⌜xs1.map Prod.fst = xs.map Prod.fst ∧ xs1.length = m.size - sz.toNat⌝ ∗
            osMeta d.ino (DFrac.own (1 : Qp).half)
              (m.announce (min m.size sz.toNat) (rsHi true m.size sz.toNat) sz.toNat) ∗
            osBytes d.ino (min m.size sz.toNat) (DFrac.own (1 : Qp).half) xs1))) $$ [Hr]
    · unfold os.truncOutH os.ftUndoneH
      icases Hr with (⟨%he, %zs, Hd⟩ | ⟨%he, (⟨%zs, Hd⟩ | ⟨Hm, Hb⟩)⟩)
      · ileft; isplitr; · ipureintro; exact he
        iexists zs; iapply os.ftDoneH_of _ m m0 _ zs hm0 $$ Hd
      · iright; isplitr; · ipureintro; exact he
        ileft; iexists zs; iapply os.ftDoneH_of _ m m0 _ zs hm0 $$ Hd
      · iright; isplitr; · ipureintro; exact he
        iright; iexists rsAnn n xs0
        rw [hann, hsz0]
        iframe
        ipureintro
        refine ⟨?_, by rw [rsAnn_length]; exact hl⟩
        rw [← hv]; simp [rsAnn, List.map_map, Function.comp_def]
    by_cases he4 : e = W64 4
    · rw [decide_eq_true he4]
      wp_auto
      icases Hr with (⟨%he, -⟩ | ⟨-, HS⟩)
      · exact absurd (he4 ▸ he) (by decide)
      iapply IH $$ [HS] HK Hosfd Hfd HΦ
      icases HS with (H | ⟨%xs1, %hxs1, Hm, Hb⟩)
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
        icases HS with (H | ⟨%xs1, %hxs1, Hm, Hb⟩)
        · ileft; iexact H
        · iright; unfold os.ftUndoneH; iexists xs1; iframe; ipureintro; exact hxs1.1
  · -- a further attempt after one that landed: a resize to the size the file has
    iunfold os.ftDoneH at Hd
    icases Hd with ⟨%hzs, ⟨%tc0, %rz0, Hm⟩, Hbs⟩
    have hdsz : ((rsPost true m sz.toNat sz.toNat).withTc tc0 rz0).size = sz.toNat := rfl
    have hdmaps : ((rsPost true m sz.toNat sz.toNat).withTc tc0 rz0).maps = m.maps := by
      simp [rsPost]
    ihave Hb0 : osBytes d.ino (min ((rsPost true m sz.toNat sz.toNat).withTc tc0 rz0).size sz.toNat)
        (DFrac.own (1 : Qp).half) [] $$ []
    · unfold osBytes; iapply (bytesG_nil _ _ _ _).2; iempintro
    ihave Hau := Hsup $$ %((rsPost true m sz.toNat sz.toNat).withTc tc0 rz0) %([] : List ByteG)
      %(by rw [hdsz]; simp) HK Hm Hb0
    unfold os.truncAuW
    wp_apply wp_osFtruncateStart_auW fd sz dq d ((rsPost true m sz.toNat sz.toNat).withTc tc0 rz0) []
      hwr hsz (by rw [hdmaps]; exact hmaps) (by rw [hdsz]; simp) _ $$ Hinv Hosfd Hau
      as %t %n %- Hosfd Hau
    wp_apply wp_osFtruncateFinish_au t d.ino sz.toNat _ [] n _ $$ Hinv Hau as %e ⟨Hr, HK⟩
    ihave Hd : os.ftDoneH d.ino m sz.toNat zs $$ [Hr Hbs]
    · iapply os.truncOutH_again _ m tc0 rz0 sz.toNat n e zs hzs $$ [Hr Hbs]; iframe
    by_cases he4 : e = W64 4
    · rw [decide_eq_true he4]
      wp_auto
      iapply IH $$ [Hd] HK Hosfd Hfd HΦ
      iright; iexists zs; iexact Hd
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
        ipureintro; rfl
      · rw [decide_eq_false he0]
        wp_auto
        wp_apply os.wp_wrapErrno_ok _ inner name e he0 $$ Hn as %pe #Hok
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
