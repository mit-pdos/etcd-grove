/-
(Ported from dsverify-lab `examples/rabia/proof/Proof/rabia/internal/message/WriteFlush.lean`, run
`rabia-r1wake-1`, onto the revised bufio.)

`message.WriteFlush`'s proof: `BufWrite` (`BufWrite.wp_of`), then, without an error, `Flush`
(`wp_Flush`). 
-/
module

public import Dsverify.Proof.rabia.internal.message.FrameDeps
public import Spec.bufio.Writer__Flush

@[expose] public section

noncomputable section

namespace Perennial.rabia.internal.message

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode model

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [package_sem : rabia.internal.message.Assumptions]
variable [_root_.Perennial.bufio.Assumptions]

set_option maxHeartbeats 1000000 in
theorem WriteFlush.wp_proof (hBW : BufWrite.spec (GF := GF))
    (wp_Flush : EtcdGrove.bufio.Writer.Flush.spec (GF := GF) (hG := hG)) :
    WriteFlush.spec (GF := GF) := by
  intro bw wi J Q Ew sz sent pend err sl dq bs
  wp_start as ⟨%hbs, #Hwr, Hown, #HQ, Hsl⟩
  ihave ⟨#Hpb, #Hpio, #Hpbin⟩ := msgPkgDeps_get $$ Hpkg
  wp_auto
  wp_apply hBW bw wi J Q Ew sz sent pend err sl dq bs $$ [$Hpkg $Hwr $Hown $HQ $Hsl]
    as %e1 ⟨%k, %sent1, %pend1, %Hk, Hsl, Hown⟩
  · ipureintro; exact hbs
  obtain ⟨hkl, hks, hkp, hke⟩ := Hk
  rcases e1 with ei | _
  · wp_auto
    iapply HΦ
    iexists sent1, pend1
    iframe Hsl Hown
    ipureintro
    refine ⟨hkp, ?_, fun h => by cases h⟩
    rw [hks]
    exact (List.prefix_append_right_inj _).2 (List.take_prefix _ _)
  have hk : k = (model.frame bs).length := hke rfl
  subst hk
  rw [List.take_length] at hks
  wp_auto
  wp_apply wp_Flush bw wi J Q Ew sz sent1 pend1 _ $$ [$Hown] as %e2 ⟨%k2, %Hk2, Hown⟩
  obtain ⟨hk2l, hk2e, -⟩ := Hk2
  iapply HΦ
  iexists sent1 ++ pend1.take k2, pend1.drop k2
  iframe Hsl Hown
  ipureintro
  refine ⟨hkp.trans (List.prefix_append _ _), ?_, fun h => ?_⟩
  · rw [List.append_assoc, List.take_append_drop, hks]; exact List.prefix_refl _
  · rw [hk2e h, List.take_length, List.drop_length, hks]
    exact ⟨rfl, rfl⟩

end proof

end Perennial.rabia.internal.message
