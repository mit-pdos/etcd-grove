/-
The proof of `LinuxFs/Spec/go_etcd_io/etcd/client/pkg/v3/fileutil/IsDirWriteableFile.lean`, as
`IsDirWriteable.wp_proof` (`IsDirWriteable.lean`), over `filepath.Join`/`Abs`, `os.WriteFile.specTruncS`
and `os.Remove.specFileS` (with the trivial update). Lean-first.
-/
module

public import LinuxFs.Spec.go_etcd_io.etcd.client.pkg.v3.fileutil.IsDirWriteableFile
public import LinuxFs.Proof.go_etcd_io.etcd.client.pkg.v3.fileutil.IsDirWriteable

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

theorem go_etcd_io.etcd.client.pkg.v3.fileutil.IsDirWriteable.wp_proofFile
    (wp_Join : filepath.Join.spec (GF := GF) (hG := hG))
    (wp_Abs : filepath.Abs.spec (GF := GF) (hG := hG))
    (wp_WriteFile : os.WriteFile.specTruncS (GF := GF) (hG := hG))
    (wp_Remove : os.Remove.specFileS (GF := GF) (hG := hG)) :
    go_etcd_io.etcd.client.pkg.v3.fileutil.IsDirWriteable.specFile (GF := GF) (hG := hG) := by
  intro dir R J i dq hJ qc hlen hfile
  wp_start as ⟨#Hinv, #Hsi, Hp, Hperm, Hn, Htr⟩
  icases osPathS_cleanAbs_keep R dir dq J $$ Hp with ⟨Hp, %hclean⟩
  (try wp_auto)
  wp_apply wp_slice_literal (V := GoString) [dir, go!".touch"]
  isplitr
  · ipureintro; rfl
  iintro %jsl ⟨Hjsl, -⟩
  (try wp_auto)
  wp_apply wp_Join _ [dir, go!".touch"] _ (by simp; omega) $$ [$Hjsl] as %pth ⟨%hpth, -⟩
  rw [join_child hclean touch_nameOk] at hpth
  subst hpth
  (try wp_auto)
  wp_apply wp_Abs (child dir go!".touch") (child_head hclean)
  rw [abs_child hclean touch_nameOk]
  (try wp_auto)
  wp_apply wp_string_to_bytes ([] : GoString) as %sl ⟨Hsl, -⟩
  (try wp_auto)
  wp_apply wp_WriteFile dir go!".touch" sl (DFrac.own 1) _ R J i (.only [go!".touch"]) dq (DFrac.own 1)
      hJ qc touch_nameOk (by simp [NameSet.Mem]) hfile
    $$ [Hp Hperm Hn Htr Hsl] as %err ⟨Hp, Hperm, Hn, Htr, -⟩
  · iframe; isplitl [] <;> iassumption
  cases err with
  | ok e =>
    (try wp_auto)
    iapply HΦ
    iframe
    isplitl
    · iright; iframe; ipureintro; exact hfile
    ipureintro; intro hc; cases hc
  | nil =>
    wp_auto
    icases (osNames_join J _ _ _ _ (Qp.half_add_half 1)).2 $$ Hn with ⟨Hq, Hr⟩
    ihave Hau := os.osAU_triv (A := Option (Nat × Nat))
      (osNames J (.only [go!".touch"]) (DFrac.own (1 : Qp).half) hJ)
      (rmFileOut J go!".touch" i hJ (DFrac.own (1 : Qp).half)) $$ Hr
    wp_apply wp_Remove dir go!".touch" J i R dq hJ (1 : Qp).half (1 : Qp).half qc
        (rmFileOut J go!".touch" i hJ (DFrac.own (1 : Qp).half)) touch_nameOk hfile
        (Qp.half_add_half 1) $$ [Hp Hperm Hq Hau]
      as %e ⟨Hp, Hperm, %o', %hok', HQ, Hout⟩
    · iframe; isplitl [] <;> iassumption
    icases os.rmFileOut_join J _ i hJ o' $$ [HQ Hout] with ⟨%h', Hn, %hc⟩
    · iframe
    (try wp_auto)
    iapply HΦ
    iframe
    rcases hc with ⟨hc1, hc2 | hc2⟩
    · isplitl
      · ileft; ipureintro; exact hc2
      ipureintro; intro _; exact hc2
    · rw [hfile] at hc2
      isplitl
      · iright; iframe; ipureintro; exact hc2
      ipureintro; intro he; exact hc1 (hok' he)

end proof

end EtcdGrove
end Perennial
