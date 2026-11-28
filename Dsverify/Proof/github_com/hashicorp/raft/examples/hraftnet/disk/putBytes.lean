/-
(hraft_robust R3) The proof of `disk.putBytes`.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.disk.putUint64
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.disk.putBytes

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.examples.hraftnet.disk.Assumptions]

open github_com.hashicorp.raft.examples.hraftnet.disk

theorem github_com.hashicorp.raft.examples.hraftnet.disk.putBytes.wp_proof
    (wp_putUint64 : github_com.hashicorp.raft.examples.hraftnet.disk.putUint64.spec (GF := GF) (hG := hG)) :
    github_com.hashicorp.raft.examples.hraftnet.disk.putBytes.spec (GF := GF) (hG := hG) := by
  intro b s bs cs dq
  wp_start as ⟨Hb, Hcap, Hs⟩
  wp_auto
  ihave %Hl := ownSlice_len $$ Hs
  wp_apply wp_putUint64 $$ [$Hb $Hcap] as %b1 ⟨Hb, Hcap⟩
  wp_apply wp_slice_append $$ [$Hb $Hcap $Hs] as %b2 ⟨Hb, Hcap, Hs⟩
  iapply HΦ
  unfold encBytes
  rw [← List.append_assoc, show W64 (cs.length : Int) = W64 (sint.Z s.len) by
    obtain ⟨h1, h2⟩ := Hl; rw [h1]; simp only [sint.nat]; rw [Int.toNat_of_nonneg h2]]
  iframe
  rw [show W64 (sint.Z s.len) = s.len by word]
  iexact Hb

end proof

end Perennial
