/-
The proof of `Spec/os/Remove.lean`: `Proof/os/RemoveN.lean`'s `os.Remove.wp_fileSncNFmt` (Go's
`os.Remove`: the `unlink` loop, then for an error the `rmdir` loop) with the claim on `.only [b]`, its
error `fmtErrorOkOrNil` from `syscall`'s package fact (`isPkgInit os` gives it).
-/
module

public import Spec.os.Remove
public import Proof.os.PkgInit
public import Proof.os.RemoveN

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open Fs

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [os.Assumptions]

theorem os.Remove.wp_proofFileSnc : os.Remove.specFileSnc (GF := GF) (hG := hG) := by
  intro d b j i R dq h q r qc Q hb hi hq
  wp_start as ⟨#Hos, #Hsi, Hp, Hperm, Hn, Hau⟩
  ihave #Hsys0 : isPkgInit (PROP := IProp GF) pkg_id.syscall $$ []
  · iPkgInit
  ihave #Hsys := syscall.errnoOk_of_isPkgInit $$ Hsys0
  wp_apply (os.Remove.wp_fileSncNFmt d b j i (.only [b]) R dq h q r qc Q hb
    (by simp [NameSet.Mem]) hi hq) $$ [Hp Hperm Hn Hau] as %err ⟨#Hfe, Hp, Hperm, Hrest⟩
  · iframe; iframe #
  iapply HΦ
  isplitr
  · iapply Hfe $$ Hsys
  iframe

/-- `specFileS` from `specFileSnc`: an `osAU` is an `osAUnc`. -/
theorem os.Remove.wp_proofFileS : os.Remove.specFileS (GF := GF) (hG := hG) := by
  intro d b j i R dq h q r qc Q hb hi hq
  iintro %Φ ⟨#Hpk, #Hos, #Hsi, Hp, Hperm, Hn, Hau⟩ HΦ
  iapply os.Remove.wp_proofFileSnc d b j i R dq h q r qc Q hb hi hq $$ [Hp Hperm Hn Hau] HΦ
  iframe Hpk Hos Hsi Hp Hperm Hn
  iapply osAU_osAUnc $$ Hau

end proof

end EtcdGrove
end Perennial
