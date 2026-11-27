/-
The proof of `rpctransport.copyBytes`.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.rpctransport.copyBytes

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.examples.hraftnet.rpctransport.Assumptions]

open github_com.hashicorp.raft.examples.hraftnet.rpctransport

theorem github_com.hashicorp.raft.examples.hraftnet.rpctransport.copyBytes.wp_proof :
    github_com.hashicorp.raft.examples.hraftnet.rpctransport.copyBytes.spec (GF := GF) (hG := hG) := by
  intro b dq bs
  wp_start as Hb
  wp_auto
  ihave %Hlen := ownSlice_len _ _ _ $$ Hb
  wp_if_destruct
  · have hbs : bs = [] := by
      rw [← List.length_eq_zero_iff]; rw [Hlen.1]; rfl
    subst hbs
    iapply HΦ
    iframe Hb
    iapply ownSlice_nil
  · wp_apply (wp_slice_make2 (V := w8) b.len) as %c ⟨Hc, -⟩
    · ipureintro; exact Hlen.2
    wp_apply (wp_slice_copy (V := w8)) $$ [$Hc $Hb] as %k ⟨%Hk, Hc, Hb⟩
    wp_end
    have e : sint.nat b.len = bs.length := Hlen.1.symm
    rw [e]
    simp only [List.length_replicate, List.take_length, List.drop_replicate, Nat.sub_self, List.replicate_zero,
      List.append_nil]
    iframe

end proof

end Perennial
