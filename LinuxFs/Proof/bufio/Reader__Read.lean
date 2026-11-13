/-
`(*bufio.Reader).Read` (see `LinuxFs/Spec/bufio/Reader__Read.lean`).
-/
module

public import LinuxFs.Spec.bufio.Reader__Read

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.bufio.Assumptions]

theorem bufio.Reader.Read.wp_proof : bufio.Reader.Read.spec (GF := GF) (hG := hG) := by
  intro b ri S E r p xs
  iintro #Hrd
  wp_start as ⟨Hb, Hp⟩
  iunfold bufio.ownReader at Hb
  icases Hb with ⟨#Hpkg, %v, %bs, Hv, Hbuf, %Hwf, HS, %Herr⟩
  ihave %Hplen := ownSlice_len _ _ _ $$ Hp
  ihave %Hblen := ownSlice_len _ _ _ $$ Hbuf
  try wp_auto
  sorry

end proof

end EtcdGrove
end Perennial
