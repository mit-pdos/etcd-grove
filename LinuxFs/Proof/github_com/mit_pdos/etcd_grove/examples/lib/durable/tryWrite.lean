/-
The proof of `LinuxFs/Spec/.../examples/lib/durable/tryWrite.lean`. The temporary's paths
(`filepath.Dir`, `Base`, `Join`); its open, creating or truncating it (`durTmpOpen`); the data written
in one `WriteAt` (skipped when empty), synced, the file closed; the rename over the name, whose
update (`durRename_osAUnc`) makes the temporary's file a candidate and commits the client's first
update (or, after an earlier attempt's, keeps the state); the directory opened and synced, which
commits every entry of the name's claim, and at the next step the client's second update
(`durInv_commit`). Every failure returns `false` with the handle rebuilt and what is still owed.
Lean-first (no Rocq counterpart).
-/
module

public import LinuxFs.Spec.github_com.mit_pdos.etcd_grove.examples.lib.durable.tryWrite
public import LinuxFs.Proof.github_com.mit_pdos.etcd_grove.examples.lib.durable.WriteOpen
public import LinuxFs.Spec.path.filepath.Dir
public import LinuxFs.Spec.path.filepath.Base
public import LinuxFs.Spec.path.filepath.Join
public import LinuxFs.Spec.os.File__WriteAt
public import LinuxFs.Spec.os.File__Sync
public import LinuxFs.Spec.os.File__SyncS
public import LinuxFs.Spec.os.File__Close
public import LinuxFs.Proof.os.NsS
public import GooseLang.Ext.Fs.NotCrashedAcc
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
    (wp_WriteAt : os.File.WriteAt.spec (GF := GF) (hG := hG))
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
          hd0 hdata (by simp [hsz])
          $$ [Hinv Hf Hsl Hfd Hm Hby Hmc'] as %n %err1 ⟨Hf, Hsl, Hfd, %j, %ys, %hw, Hm, Hby, -, -⟩
      · iframe; iframe #
      obtain ⟨hj, hpw, -, hres⟩ := hw
      (try wp_auto)
      iframe
      ipureintro
      refine ⟨rfl, htr0.pw hsz data hd0 j hj hpw, fun he => ?_⟩
      rcases hres with ⟨rfl, -, -⟩ | ⟨-, hne⟩
      · exact pw_whole hsz data hd0 hpw
      · exact absurd he hne
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
  sorry

end proof

end EtcdGrove
end Perennial
