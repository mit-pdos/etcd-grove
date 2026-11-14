/-
The proof of `Spec/os/File__CloseNil.lean`: the model's nil test, and a load of `os.ErrInvalid`
(`os.errInvalid_of_pkgInit`).
-/
module

public import LinuxFs.Spec.os.File__CloseNil

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

theorem os.File.Close.wp_proofNil : os.File.Close.specNil (GF := GF) (hG := hG) := by
  wp_start
  ihave ⟨%e, #He⟩ := os.errInvalid_of_pkgInit $$ Hpkg
  unfold os.ErrInvalid at *
  wp_auto
  iapply HΦ
  ipureintro; trivial

end proof

end EtcdGrove
end Perennial
