/-
The proof of `Spec/go_etcd_io/etcd/client/pkg/v3/fileutil/IsDirWriteable.lean`, over
`filepath.Join`/`Abs`, `os.WriteFile.specEmptyS` and `os.Remove.specFileS` (with the trivial update).
-/
module

public import Spec.go_etcd_io.etcd.client.pkg.v3.fileutil.IsDirWriteable
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.PipeLemmas
public import Spec.path.filepath.Join
public import Spec.path.filepath.Abs
public import Proof.go_etcd_io.etcd.client.pkg.v3.fileutil.IsDirWriteableLemmas

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open Fs WalFs

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [go_etcd_io.etcd.client.pkg.v3.fileutil.Assumptions]
variable [os_sem : os.Assumptions] [os.file.FieldAssumptions]

theorem go_etcd_io.etcd.client.pkg.v3.fileutil.IsDirWriteable.wp_proof
    (wp_Join : filepath.Join.spec (GF := GF) (hG := hG))
    (wp_Abs : filepath.Abs.spec (GF := GF) (hG := hG))
    (wp_WriteFile : os.WriteFile.specEmptyS (GF := GF) (hG := hG))
    (wp_Remove : os.Remove.specFileS (GF := GF) (hG := hG)) :
    go_etcd_io.etcd.client.pkg.v3.fileutil.IsDirWriteable.spec (GF := GF) (hG := hG) := by
  intro dir R J dq hJ qc hlen hnone
  wp_start as ⟨#Hinv, #Hsi, Hp, Hperm, Hn⟩
  icases osPathS_cleanAbs_keep R dir dq J $$ Hp with ⟨Hp, %hclean⟩
  (try wp_auto)
  wp_apply wp_slice_literal (V := GoString) [dir, go!".touch"]
  isplitr
  · ipureintro; rfl
  iintro %jsl ⟨Hjsl, -⟩
  (try wp_auto)
  wp_apply wp_Join _ [dir, go!".touch"] _ (by simp [_root_.Perennial.strings.joinMax]; omega) $$ [$Hjsl] as %pth ⟨%hpth, -⟩
  rw [join_child hclean touch_nameOk] at hpth
  subst hpth
  (try wp_auto)
  wp_apply wp_Abs (child dir go!".touch") (child_head hclean)
  rw [abs_child hclean touch_nameOk]
  (try wp_auto)
  wp_apply wp_string_to_bytes ([] : GoString) as %sl ⟨Hsl, -⟩
  (try wp_auto)
  wp_apply wp_WriteFile dir go!".touch" sl (DFrac.own 1) _ R J dq hJ qc touch_nameOk hnone
    $$ [Hp Hperm Hn Hsl] as %err ⟨#Hfe, Hp, Hperm, -, %o, %hok, Hout, Htr⟩
  · iframe; isplitl [] <;> iassumption
  cases err with
  | ok e =>
    (try wp_auto)
    iapply HΦ
    isplitr
    · iexact Hfe
    iframe
    rcases o with _ | ⟨x, s, i⟩
    · dsimp only [crOut]
      iexists hJ
      iframe
      isplitl []
      · ileft; ipureintro; exact hnone
      ipureintro; intro hc; cases hc
    · dsimp only [crOut, crTr]
      icases Hout with ⟨-, -, Hn⟩
      iexists _
      iframe Hn
      isplitl [Htr]
      · iright; iexists i; iframe; ipureintro; simp [NamesH.log]
      ipureintro; intro hc; cases hc
  | nil =>
    obtain ⟨⟨x, s, i⟩, rfl⟩ := Option.isSome_iff_exists.1 (hok rfl)
    dsimp only [crOut, crTr]
    icases Hout with ⟨-, -, Hn⟩
    wp_auto
    generalize hh : hJ.log x (crEnt J go!".touch" i s) (<[go!".touch" := Node.file i]> hJ.cur) = h1
    have hcur : h1.cur !! go!".touch" = some (.file i) := by
      subst hh; simp [NamesH.log]
    icases (osNames_join J _ _ _ _ (Qp.half_add_half 1)).2 $$ Hn with ⟨Hq, Hr⟩
    ihave Hau := os.osAU_triv (A := Option (Nat × Nat))
      (osNames J (.only [go!".touch"]) (DFrac.own (1 : Qp).half) h1)
      (rmFileOut J go!".touch" i h1 (DFrac.own (1 : Qp).half)) $$ Hr
    wp_apply wp_Remove dir go!".touch" J i R dq h1 (1 : Qp).half (1 : Qp).half qc
        (rmFileOut J go!".touch" i h1 (DFrac.own (1 : Qp).half)) touch_nameOk hcur
        (Qp.half_add_half 1) $$ [Hp Hperm Hq Hau]
      as %e ⟨#Hfe', Hp, Hperm, %o', %hok', HQ, Hout⟩
    · iframe; isplitl [] <;> iassumption
    icases os.rmFileOut_join J _ i h1 o' $$ [HQ Hout] with ⟨%h', Hn, %hc⟩
    · iframe
    (try wp_auto)
    iapply HΦ
    isplitr
    · iexact Hfe'
    iframe Hp Hperm
    iexists h'
    iframe Hn
    isplitl [Htr]
    · rcases hc.2 with hc2 | hc2
      · ileft; ipureintro; exact hc2
      · iright; iexists i; iframe; ipureintro; rw [hc2, hcur]
    ipureintro; exact fun he => hc.1 (hok' he)

end proof

end EtcdGrove
end Perennial
