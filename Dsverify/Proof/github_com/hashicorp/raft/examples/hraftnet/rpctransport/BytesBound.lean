/-
The proof of `rpctransport.BytesBound`.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.rpctransport.BytesBound

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

theorem github_com.hashicorp.raft.examples.hraftnet.rpctransport.BytesBound.wp_proof :
    github_com.hashicorp.raft.examples.hraftnet.rpctransport.BytesBound.spec (GF := GF) (hG := hG) := by
  intro b dq bs
  wp_start as Hb
  ihave %Hlen := ownSlice_len _ _ _ $$ Hb
  have hl : (bs.length : Int) = uint.Z b.len := by word
  have hd : uint.Z (W64 1073741824) = 1073741824 := by word
  wp_auto
  wp_if_destruct
  · iapply HΦ
    iframe Hb
    ipureintro
    unfold bytesBoundN; rw [ite_eq_left_iff.mpr (by intro h; exfalso; unfold maxReqN at h; omega)]
    word
  · iapply HΦ
    iframe Hb
    ipureintro
    unfold bytesBoundN; rw [ite_eq_right_iff.mpr (by intro h; exfalso; unfold maxReqN at h; omega)]
    word

end proof

end Perennial
