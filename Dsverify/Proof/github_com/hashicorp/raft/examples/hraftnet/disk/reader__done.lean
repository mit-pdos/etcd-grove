/-
(hraft_robust R3) The proof of `disk.(*reader).done`.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.disk.reader__done

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

theorem rd_len0 (len : w64) (hl : ([] : List w8).length = sint.nat len ∧ 0 ≤ sint.Z len) : len = W64 0 := by
  obtain ⟨h1, h2⟩ := hl; simp at h1; word

theorem github_com.hashicorp.raft.examples.hraftnet.disk.reader.done.wp_proof :
    github_com.hashicorp.raft.examples.hraftnet.disk.reader.done.spec (GF := GF) (hG := hG) := by
  intro r
  wp_start as Hr
  iunfold readerSt at Hr
  icases Hr with ⟨%sl, Hr, #Hsl⟩
  ihave %Hlen := ownSlice_len $$ Hsl
  have h0 := rd_len0 sl.len Hlen
  wp_auto
  rw [h0]
  wp_auto
  iapply HΦ
  iunfold readerSt
  iexists sl
  iframe Hr Hsl

end proof

end Perennial
