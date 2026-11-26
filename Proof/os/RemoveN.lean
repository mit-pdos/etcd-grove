/-
The proof of `Spec/os/RemoveN.lean`: `Proof/os/RemoveParts.lean`'s `os.Remove.wp_fileSncNFmt` (Go's
`os.Remove`; the proof of `specFileSnc` with the claim generalized), its post's `fmt` fact dropped.
-/
module

public import Spec.os.RemoveN
public import Proof.os.RemoveParts

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

theorem os.Remove.wp_proofFileSncN : os.Remove.specFileSncN (GF := GF) (hG := hG) := by
  intro d b j i N R dq h q r qc Q hb hbN hi hq
  iintro %Φ Hpre HΦ
  iapply (os.Remove.wp_fileSncNFmt d b j i N R dq h q r qc Q hb hbN hi hq) $$ Hpre
  iintro %err
  inext
  iintro ⟨-, Hrest⟩
  iapply HΦ $$ Hrest

end proof

end EtcdGrove
end Perennial
