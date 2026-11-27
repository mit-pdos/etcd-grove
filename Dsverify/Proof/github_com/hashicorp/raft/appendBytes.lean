/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/appendBytes.lean (241f27e).
-/
/-
The proof of `raft.appendBytes`.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.appendBytes
public import Dsverify.Spec.github_com.hashicorp.raft.appendUint64
public import Dsverify.Proof.github_com.hashicorp.raft.EncodingLemmas

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.Assumptions]

open github_com.hashicorp.raft proto

theorem github_com.hashicorp.raft.appendBytes.wp_proof
    (wp_appendUint64 : github_com.hashicorp.raft.appendUint64.spec (GF := GF) (hG := hG)) :
    github_com.hashicorp.raft.appendBytes.spec (GF := GF) (hG := hG) := by
  intro b bs s xs dq
  wp_start as ⟨Hb, Hcap, Hs⟩
  ihave %Hlen := ownSlice_len _ _ _ $$ Hs
  wp_auto
  wp_apply wp_appendUint64 $$ [$Hb $Hcap] as %b1 ⟨Hb, Hcap⟩
  wp_apply (wp_slice_append (V := w8)) $$ [$Hb $Hcap $Hs] as %b2 ⟨Hb, Hcap, Hs⟩
  iapply HΦ
  rw [show W64 (xs.length : Int) = s.len by word]
  iframe

end proof

end Perennial
