/-
The proof of `Spec/.../examples/lib/durable/tryWrite.lean`. The temporary's paths
(`filepath.Dir`, `Base`, `Join`); its open, creating or truncating it (`durTmpOpen`); the data written
in one `WriteAt` (skipped when empty), synced, the file closed; the rename over the name, whose
update (`durRename_osAUnc`) makes the temporary's file a candidate and commits the client's first
update (or, after an earlier attempt's, keeps the state); the directory opened and synced, which
commits every entry of the name's claim, and at the next step the client's second update
(`durInv_commit`). Every failure returns `false` with the handle rebuilt and what is still owed.
Lean-first (no Rocq counterpart).
-/
module

public import WalTester.Spec.github_com.mit_pdos.etcd_grove.examples.lib.durable.tryWrite
public import WalTester.Proof.github_com.mit_pdos.etcd_grove.examples.lib.durable.WriteOpen
public import Spec.path.filepath.Dir
public import Spec.path.filepath.Base
public import Spec.path.filepath.Join
public import Spec.os.WriteLong
public import Spec.os.File__Sync
public import Spec.os.File__SyncS
public import Spec.os.File__Close
public import Proof.os.NsS
public import Perennial.GooseLang.NotCrashed
public import Perennial.Proof.github_com.mit_pdos.perennial.goose.model.strings.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open Fs DurFs

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.lib.durable.Assumptions]
variable [os.file.FieldAssumptions]

theorem github_com.mit_pdos.etcd_grove.examples.lib.durable.tryWrite.wp_proof
    (wp_Dir : filepath.Dir.spec (GF := GF) (hG := hG))
    (wp_Base : filepath.Base.spec (GF := GF) (hG := hG))
    (wp_Join : filepath.Join.spec (GF := GF) (hG := hG))
    (wp_OpenCT : os.OpenFile.specCreateTruncSnc (GF := GF) (hG := hG))
    (wp_WriteAt : os.File.WriteAt.specLong (GF := GF) (hG := hG))
    (wp_Sync : os.File.Sync.spec (GF := GF) (hG := hG))
    (wp_SyncDir : os.File.Sync.specDirS (GF := GF) (hG := hG))
    (wp_Close : os.File.Close.spec (GF := GF) (hG := hG))
    (wp_Rename : os.Rename.specFileSnc (GF := GF) (hG := hG)) :
    github_com.mit_pdos.etcd_grove.examples.lib.durable.tryWrite.spec (GF := GF) (hG := hG) := by
  intro γ f R qc p data Ψ hf hdata hok
  obtain ⟨s0, hok⟩ := hok
  wp_start as ⟨#Hinv, #Hsi, #Hdi, Hh, Hperm, Howe⟩
  iunfold durHandleP at Hh
  icases Hh with ⟨%qd, Hp, Hnb, Hnt, Hcur, Htmp, Hpath⟩
  wp_auto
  wp_apply wp_Dir f.name $$ Hpkg2 as %dir %hdir
  rw [DFile.dir_name hf] at hdir
  subst hdir
  (try wp_auto)
  wp_apply wp_Base f.name $$ Hpkg2 as %base %hbase
  rw [DFile.base_name hf] at hbase
  subst hbase
  (try wp_auto)
  wp_apply wp_slice_literal (V := GoString) [f.d, f.tb]
  isplitr
  · ipureintro; rfl
  iintro %jsl ⟨Hjsl, -⟩
  (try wp_auto)
  wp_apply wp_Join _ [f.d, f.tb] _ (DFile.join_len hf) $$ [$Hpkg2 $Hjsl] as %tmp ⟨%htmp, -⟩
  rw [DFile.join_tmp hf] at htmp
  subst htmp
  (try wp_auto)
  wp_apply durTmpOpen wp_OpenCT γ f R qc qd p s0 (W64 2 ||| W64 64 ||| W64 512) (W32 384) hf hok
      durOpenFlag_ok.1 durOpenFlag_ok.2.1 durOpenFlag_ok.2.2 $$ [Hinv Hsi Hdi Hp Hnt Htmp Hpath Hperm]
      as %fl %err ⟨Hpath, Hperm, %ht1, Hp, Hnt, Hres⟩
  · iframe; iframe #
  icases Hres with (⟨%herr, Htmp⟩ | ⟨%fd, %i, %hres, Htr, Hf, Hoff, Hfd⟩)
  · -- the open failed
    cases err with
    | nil => exact absurd rfl herr
    | ok ie =>
    (try wp_auto)
    iapply HΦ
    iframe Hperm
    iexists { p with ht := ht1 }
    isplitl [Hp Hnb Hnt Hcur Htmp Hpath]
    · iunfold durHandleP; iexists qd; iframe
      iapply (curRes_congr f p { p with ht := ht1 } rfl rfl).2 $$ Hcur
    iright
    isplitr
    · ipureintro; rfl
    iapply (durWOwe_congr γ f data p { p with ht := ht1 } Ψ rfl rfl rfl).2 $$ Howe
  obtain ⟨rfl, hi⟩ := hres
  iunfold trFile at Htr
  icases Htr with ⟨%m, %xs, Hm, Hby, Hmc, %htf⟩
  obtain ⟨hxs, hsz, hmaps, hcut, hlo, hzf, -⟩ := htf
  have hsz : m.size = 0 := hsz trivial
  obtain rfl : xs = [] := List.eq_nil_of_length_eq_zero (hxs.trans hsz)
  have htr0 : TrOk m [] := ⟨hxs, hmaps, hcut, hlo, hzf⟩
  (try wp_auto)
  -- `if len(data) > 0 { _, err = f.WriteAt([]byte(data), 0) }`: the file after it
  wp_bind (If _ _ _)
  iapply (wp_wand (Φ := fun v => iprop(⌜v = executeVal⌝ ∗ data_ptr ↦ data ∗ f_ptr ↦ fl ∗
      os.ownFile fl fd f.tmp (DFrac.own 1) ∗
      osFd fd (DFrac.own 1) (openFd i (W64 2 ||| W64 64 ||| W64 512 ||| W64 524288)) ∗
      ∃ (e : GoInterface) (m1 : OsMeta) (ys : List ByteG), err_ptr ↦ e ∗ osMeta i (DFrac.own 1) m1 ∗
        osBytes i 0 (DFrac.own 1) ys ∗
        ⌜TrOk m1 ys ∧ (e = interface.nil → ys.map Prod.fst = data ∧ m1.size = data.length)⌝)))
    $$ [data f err Hf Hfd Hm Hby Hmc]
  · wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len data as %hlen
    (try wp_auto)
    wp_if_destruct
    · -- `data` non-empty: one `WriteAt`
      have hd0 : 0 < data.length := by word
      wp_apply wp_string_to_bytes data as %sl ⟨Hsl, -⟩
      (try wp_auto)
      icases mcellsAny_of_empty m.maps hmaps (W64 0).toNat ((W64 0).toNat + data.length) with Hmc'
      wp_apply wp_WriteAt fl fd f.tmp (DFrac.own 1) sl data (DFrac.own 1) (W64 0) (DFrac.own 1)
          (openFd i (W64 2 ||| W64 64 ||| W64 512 ||| W64 524288)) m [] (durOpenFlag_writable i)
          (by decide) (by rw [hsz]; decide) (by simp only [show (W64 0).toNat = 0 from rfl]; omega)
          hd0 (by omega) (by simp [hsz])
          $$ [Hinv Hf Hsl Hfd Hm Hby Hmc'] as %n %err1 ⟨Hf, Hsl, Hfd, %j, %A, %E, %ys, %hw, Hm, Hby, -, -⟩
      · iframe; iframe #
      obtain ⟨hjA, hA, -, -, -, hpw, -, hres⟩ := hw
      have hj : j ≤ data.length := Nat.le_trans hjA hA
      (try wp_auto)
      iframe
      ipureintro
      refine ⟨rfl, htr0.pwA hsz data A j E hjA hj hpw, fun he => ?_⟩
      rcases hres with ⟨rfl, -, -⟩ | ⟨-, hne⟩
      · obtain rfl : A = data.length := by omega
        exact pw_wholeA hsz data hd0 _ E hpw
      · exact absurd he hne.1
    · -- `data` empty: nothing written
      have hd0 : data = [] := List.eq_nil_of_length_eq_zero (by word)
      subst hd0
      (try wp_auto)
      iframe
      ipureintro
      exact ⟨htr0, fun _ => ⟨rfl, hsz⟩⟩
  iintro %v ⟨%hv, data, f, Hf, Hfd, %e, %m1, %ys, err, Hm, Hby, %htr1⟩
  subst hv
  (try wp_auto)
  cases e with
  | ok ie =>
    -- the write failed: the file closed, the temporary kept
    (try wp_auto)
    wp_apply wp_Close fl fd f.tmp _ $$ [Hinv Hf Hfd] as %e2 -
    · iframe; iframe #; iapply lockToks_unlocked <;> rfl
    (try wp_auto)
    iapply HΦ
    iframe Hperm
    iexists { p with ht := ht1 }
    isplitl [Hp Hnb Hnt Hcur Hpath Hm Hby]
    · iapply durHandle_tmp γ f R p ht1 qd i m1 ys hi htr1.1 $$ Hp Hnb Hnt Hcur Hpath Hm Hby
    iright
    isplitr
    · ipureintro; rfl
    iapply (durWOwe_congr γ f data p { p with ht := ht1 } Ψ rfl rfl rfl).2 $$ Howe
  | nil =>
  obtain ⟨hys, hsz1⟩ := htr1.2 rfl
  (try wp_auto)
  wp_apply wp_Sync fl fd f.tmp (DFrac.own 1) (DFrac.own 1) (openFd i (W64 2 ||| W64 64 ||| W64 512 ||| W64 524288)) m1 0 ys (OsMeta.covers_whole m1 htr1.1.1)
    $$ [Hinv Hf Hfd Hm Hby] as %e2 ⟨Hf, Hfd, Hres, -⟩
  · simp only [durOpenFd_ino]; iframe; iframe #
  try simp only [durOpenFd_ino]
  icases Hres with (⟨%he2, Hm, Hby⟩ | ⟨%he2, Hm, Hby⟩)
  rotate_left
  · -- the sync failed
    cases e2 with
    | nil => exact absurd rfl he2
    | ok ie =>
    (try wp_auto)
    wp_apply wp_Close fl fd f.tmp _ $$ [Hinv Hf Hfd] as %e3 -
    · iframe; iframe #; iapply lockToks_unlocked <;> rfl
    (try wp_auto)
    iapply HΦ
    iframe Hperm
    iexists { p with ht := ht1 }
    isplitl [Hp Hnb Hnt Hcur Hpath Hm Hby]
    · iapply durHandle_tmp γ f R p ht1 qd i m1 ys hi htr1.1 $$ Hp Hnb Hnt Hcur Hpath Hm Hby
    iright
    isplitr
    · ipureintro; rfl
    iapply (durWOwe_congr γ f data p { p with ht := ht1 } Ψ rfl rfl rfl).2 $$ Howe
  subst he2
  (try wp_auto)
  wp_apply wp_Close fl fd f.tmp _ $$ [Hinv Hf Hfd] as %e3 -
  · iframe; iframe #; iapply lockToks_unlocked <;> rfl
  have htr2 := htr1.1.synced
  have hby : ys.map (fun x => durB x.1) = data.map durB := by rw [← hys, List.map_map]; rfl
  rw [hby] at htr2
  rw [hby]
  cases e3 with
  | ok ie =>
    -- the close failed
    (try wp_auto)
    iapply HΦ
    iframe Hperm
    iexists { p with ht := ht1 }
    isplitl [Hp Hnb Hnt Hcur Hpath Hm Hby]
    · iapply durHandle_tmp γ f R p ht1 qd i m1.synced (data.map durB) hi htr2 $$ Hp Hnb Hnt Hcur Hpath Hm Hby
    iright
    isplitr
    · ipureintro; rfl
    iapply (durWOwe_congr γ f data p { p with ht := ht1 } Ψ rfl rfl rfl).2 $$ Howe
  | nil =>
  (try wp_auto)
  -- the rename: the temporary's file a candidate, the client's first update (or a retry's)
  have hc : (DCand.mk i m1.synced data).Ok := dcand_ok i data hsz1 hdata
  have hNt : (NameSet.only [f.tb]).Mem f.tb := by simp [NameSet.Mem]
  have hNb : (NameSet.only [f.b]).Mem f.b := by simp [NameSet.Mem]
  have hkey : (f.J, NameSet.only [f.tb]) ≠ (f.J, NameSet.only [f.b]) := by
    intro h
    simp only [Prod.mk.injEq, NameSet.only.injEq, List.cons.injEq, _root_.and_true, _root_.true_and] at h
    exact f.tb_ne h
  have hnd : ∀ J, p.hb.cur !! f.b ≠ some (.dir J) := by
    intro J
    have hc0 := hok.cur
    cases hs : s0.cur with
    | none => rw [hs] at hc0; simp only at hc0; rw [hc0]; simp
    | some v =>
      rw [hs] at hc0
      obtain ⟨c', -, -, he⟩ := hc0
      rw [he]; simp
  ihave Hq : durRenQ γ f { p with ht := ht1 } ⟨i, m1.synced, data⟩ Ψ none $$ [Hp Hm Hby Howe]
  · simp only [durRenQ]
    iframe Hp Hm Hby
    iapply (durWOwe_congr γ f data p { p with ht := ht1 } Ψ rfl rfl rfl).2 $$ Howe
  ihave Hau := durRename_osAUnc γ f { p with ht := ht1 } ⟨i, m1.synced, data⟩ Ψ hc $$ Hdi Hq
  icases osPathS_split_halves R f.d qd f.J $$ Hpath with ⟨Hpa, Hpb⟩
  unfold DFile.tmp DFile.name
  icases osPathS_sameRoot R f.d f.tb f.b _ f.J $$ Hpa with ⟨Hpa, %hsr⟩
  wp_apply wp_Rename f.d f.tb f.d f.b f.J f.J i (.only [f.tb]) (.only [f.b]) R (DFrac.own qd.half)
      (DFrac.own qd.half) ht1 p.hb (1 : Qp).half (1 : Qp).half (1 : Qp).half (1 : Qp).half qc _
      hf.2.2.2.2.1 hf.2.2.2.1 hNt hNb hkey hi hnd (Qp.half_add_half 1) (Qp.half_add_half 1) hsr
    $$ [Hinv Hsi Hpa Hpb Hperm Hnt Hnb Hau] as %e4 ⟨Hpa, Hpb, Hperm, %o, %ho, Hq, Hout⟩
  · iframe; iframe #
  ihave Hpath := osPathS_join_halves R f.d qd f.J $$ [$Hpa $Hpb]
  rcases o with _ | ⟨x, s1⟩
  · -- no effect: the rename failed, the temporary kept
    have he4 : e4 ≠ interface.nil := fun h => by simpa using ho.1 h
    cases e4 with
    | nil => exact absurd rfl he4
    | ok ie =>
    simp only [durRenQ]
    icases Hq with ⟨Hp, Hm, Hby, Howe⟩
    unfold renFileOut
    simp only [logOut, claimOut]
    icases Hout with ⟨-, Hnt, Hnb⟩
    (try wp_auto)
    iapply HΦ
    iframe Hperm
    iexists { p with ht := ht1 }
    isplitl [Hp Hnb Hnt Hcur Hpath Hm Hby]
    · iapply durHandle_tmp γ f R p ht1 qd i m1.synced (data.map durB) hi htr2 $$ Hp Hnb Hnt Hcur Hpath Hm Hby
    iright
    isplitr
    · ipureintro; rfl
    iexact Howe
  -- the rename took effect
  simp only [durRenQ]
  icases Hq with ⟨%a, %ha, Hp, Hc, Hsync⟩
  unfold renFileOut
  simp only [logOut, claimOut]
  icases Hout with ⟨-, Hnt, Hnb⟩
  iclear Hcur
  cases e4 with
  | ok ie =>
    -- reported a failure: the second update still owed
    (try wp_auto)
    iapply HΦ
    iframe Hperm
    iexists (renPhys f { p with ht := ht1 } ⟨i, m1.synced, data⟩ a x s1)
    isplitl [Hp Hnb Hnt Hc Hpath]
    · iapply durHandle_ren γ f R { p with ht := ht1 } ⟨i, m1.synced, data⟩ a x s1 qd _ rfl rfl rfl
        $$ Hp Hnb Hnt Hc Hpath
    iright
    isplitr
    · ipureintro; rfl
    iapply durWOwe_ren γ f { p with ht := ht1 } ⟨i, m1.synced, data⟩ a x s1 Ψ ha $$ Hsync
  | nil =>
  (try wp_auto)
  -- the directory opened and synced
  wp_apply os.Open.wp_dirS f.d R f.J (DFrac.own qd) qc $$ [Hinv Hsi Hpath Hperm]
    as %dfl %e5 ⟨Hpath, Hperm, Hres⟩
  · iframe; iframe #
  icases Hres with (⟨%dfd, %he5, Hdf, Hdfd⟩ | ⟨%he5, -⟩)
  rotate_left
  · cases e5 with
    | nil => exact absurd rfl he5
    | ok ie =>
    (try wp_auto)
    iapply HΦ
    iframe Hperm
    iexists (renPhys f { p with ht := ht1 } ⟨i, m1.synced, data⟩ a x s1)
    isplitl [Hp Hnb Hnt Hc Hpath]
    · iapply durHandle_ren γ f R { p with ht := ht1 } ⟨i, m1.synced, data⟩ a x s1 qd _ rfl rfl rfl
        $$ Hp Hnb Hnt Hc Hpath
    iright
    isplitr
    · ipureintro; rfl
    iapply durWOwe_ren γ f { p with ht := ht1 } ⟨i, m1.synced, data⟩ a x s1 Ψ ha $$ Hsync
  subst he5
  (try wp_auto)
  imod osNames_next R f.J _ _ _ CoPset.subseteq_top $$ Hsi Hnb with ⟨Hnb, #Hlb⟩
  wp_apply wp_SyncDir dfl dfd f.d (DFrac.own 1) R f.J .idle _ $$ [Hinv Hsi Hdf Hdfd Hlb]
    as %e6 ⟨Hdf, Hdfd, Hres⟩
  · iframe; iframe #
  icases Hres with (⟨%he6, -⟩ | ⟨%he6, #Hclb⟩)
  · cases e6 with
    | nil => exact absurd rfl he6.1
    | ok ie =>
    (try wp_auto)
    wp_apply os.File.Close.wp_dirS dfl dfd f.d f.J .idle $$ [Hinv Hdf Hdfd] as %e7 -
    · iframe; iframe #
    (try wp_auto)
    iapply HΦ
    iframe Hperm
    iexists (renPhys f { p with ht := ht1 } ⟨i, m1.synced, data⟩ a x s1)
    isplitl [Hp Hnb Hnt Hc Hpath]
    · iapply durHandle_ren γ f R { p with ht := ht1 } ⟨i, m1.synced, data⟩ a x s1 qd _ rfl rfl rfl
        $$ Hp Hnb Hnt Hc Hpath
    iright
    isplitr
    · ipureintro; rfl
    iapply durWOwe_ren γ f { p with ht := ht1 } ⟨i, m1.synced, data⟩ a x s1 Ψ ha $$ Hsync
  subst he6
  (try wp_auto)
  -- the client's second update
  imod osNames_histCoh R f.J _ _ _ CoPset.subseteq_top $$ Hsi Hnb with ⟨Hnb, %hcoh⟩
  iapply wp_notCrashed_acc _ _ rfl
  iintro Hnc
  imod durInv_commit γ f (renPhys f { p with ht := ht1 } ⟨i, m1.synced, data⟩ a x s1)
    (p.hb.log x (renFileEnt f.J f.tb f.J f.b i p.hb s1) (<[f.b := .file i]> p.hb.cur)).next Ψ
    (by simpa using hcoh) (by simp) $$ Hdi Hnc Hp Hclb Hsync with ⟨Hnc, Hp, HΨ⟩
  iframe Hnc
  imodintro
  wp_apply os.File.Close.wp_dirS dfl dfd f.d f.J .idle $$ [Hinv Hdf Hdfd] as %e7 -
  · iframe; iframe #
  (try wp_auto)
  iapply HΦ
  iframe Hperm
  iexists { renPhys f { p with ht := ht1 } ⟨i, m1.synced, data⟩ a x s1 with
    nc := (p.hb.log x (renFileEnt f.J f.tb f.J f.b i p.hb s1) (<[f.b := .file i]> p.hb.cur)).next, alt := none }
  isplitl [Hp Hnb Hnt Hc Hpath]
  · iapply durHandle_ren γ f R { p with ht := ht1 } ⟨i, m1.synced, data⟩ a x s1 qd
      { renPhys f { p with ht := ht1 } ⟨i, m1.synced, data⟩ a x s1 with
        nc := (p.hb.log x (renFileEnt f.J f.tb f.J f.b i p.hb s1) (<[f.b := .file i]> p.hb.cur)).next,
        alt := none } rfl rfl rfl
      $$ Hp Hnb Hnt Hc Hpath
  ileft
  iframe HΨ
  ipureintro
  exact ⟨rfl, rfl⟩

end proof

end EtcdGrove
end Perennial
