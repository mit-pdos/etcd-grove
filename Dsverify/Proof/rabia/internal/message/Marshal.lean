/-
(Ported from dsverify-lab `examples/rabia/proof/Proof/rabia/internal/message/Marshal.lean`, run `rabia-r1wake-1`.)

The frozen `Marshal` specs at the run's package instances (prover C1): the generic proofs
(`*.Marshal.wp_gen`, which take `isPkgInit math/bits`) with `isPkgInit math/bits` from
`isPkgInit message` (the run's instance includes its imports').
-/
module

public import Dsverify.Proof.rabia.internal.message.Command__Marshal
public import Dsverify.Proof.rabia.internal.message.Msg__Marshal

@[expose] public section

noncomputable section

namespace Perennial.rabia.internal.message

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode model bufio

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [package_sem : rabia.internal.message.Assumptions]

theorem Command.Marshal.wp_proof : Command.Marshal.spec (GF := GF) := by
  intro l v c dq
  iintro %Φ ⟨#Hpkg, Hl, #Hrep, %hb⟩ HΦ
  ihave #Hbits : isPkgInit (PROP := IProp GF) pkg_id.math.bits $$ []
  · iPkgInit
  iapply (Command.Marshal.wp_gen l v c dq hb) $$ [Hl] HΦ
  iframe
  isplitl []; · iexact Hpkg
  isplitl []; · iexact Hbits
  iexact Hrep

theorem Msg.Marshal.wp_proof : Msg.Marshal.spec (GF := GF) := by
  intro l v m dq
  iintro %Φ ⟨#Hpkg, Hl, #Hrep, %hb⟩ HΦ
  ihave #Hbits : isPkgInit (PROP := IProp GF) pkg_id.math.bits $$ []
  · iPkgInit
  iapply (Msg.Marshal.wp_gen l v m dq hb) $$ [Hl] HΦ
  iframe
  isplitl []; · iexact Hpkg
  isplitl []; · iexact Hbits
  iexact Hrep

end proof
end Perennial.rabia.internal.message
