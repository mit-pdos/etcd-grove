/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swiftnet/codec/CodecFns.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
The proofs of `Spec/swiftnet/CodecFns.lean` (change log C7: the codec functions that the master's
dispatch calls), as instances of the codec's lemmas (`DecodeAs.lean`, `Prim.lean`, `Enc.lean`).
-/
module

public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.examples.swiftnet.CodecFns
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.codec.DecodeAs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.codec.Enc

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section proofs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics]
variable [examples.swiftnet.Assumptions]

open examples.swiftnet sp

theorem examples.swiftnet.rpcDecodeAs_defs_RegisterArgs.wp_proof :
    examples.swiftnet.rpcDecodeAs_defs_RegisterArgs.spec := by
  intro data dq ip port
  iintro %Φ Hb HΦ
  wp_apply wp_rpcDecodeAs_defs_RegisterArgs $$ Hb as %v %err Hpost
  unfold decAsPost
  icases Hpost with ⟨Hb, (⟨%He, %x, Hown, %Hx⟩ | ⟨-, %Hne⟩)⟩
  · iunfold ownRA at Hown
    icases Hown with %Hown
    have h := Hx (.registerArgs ip port) rfl trivial rfl
    subst h He
    obtain ⟨a, p⟩ := v
    simp only [KitVal.registerArgs.injEq] at Hown
    obtain ⟨rfl, rfl⟩ := Hown
    iapply HΦ; iexact Hb
  · exact absurd rfl (Hne (.registerArgs ip port) rfl trivial)

theorem examples.swiftnet.rpcDecodeAs_defs_GetReplicaListArgs.wp_proof :
    examples.swiftnet.rpcDecodeAs_defs_GetReplicaListArgs.spec := by
  intro data dq
  iintro %Φ Hb HΦ
  wp_apply wp_rpcDecodeAs_defs_GetReplicaListArgs $$ Hb as %v %err Hpost
  unfold decAsPost
  icases Hpost with ⟨Hb, (⟨%He, %x, -, -⟩ | ⟨-, %Hne⟩)⟩
  · subst He
    iapply HΦ; iexact Hb
  · exact absurd rfl (Hne .getReplicaListArgs rfl trivial)

theorem examples.swiftnet.rpcDecodeAs_defs_GetLeaderArgs.wp_proof :
    examples.swiftnet.rpcDecodeAs_defs_GetLeaderArgs.spec := by
  intro data dq
  iintro %Φ Hb HΦ
  wp_apply wp_rpcDecodeAs_defs_GetLeaderArgs $$ Hb as %v %err Hpost
  unfold decAsPost
  icases Hpost with ⟨Hb, (⟨%He, %x, -, -⟩ | ⟨-, %Hne⟩)⟩
  · subst He
    iapply HΦ; iexact Hb
  · exact absurd rfl (Hne .getLeaderArgs rfl trivial)

theorem examples.swiftnet.rpcPutU64.specNil.wp_proof :
    examples.swiftnet.rpcPutU64.specNil := by
  intro x
  iintro %Φ - HΦ
  ihave Hn := ownSlice_nil (GF := netDistGF) (V := w8) (DFrac.own 1)
  ihave Hc := ownSliceCap_nil (GF := netDistGF) (V := w8)
  wp_apply wp_rpcPutU64 slice.nil [] x $$ [Hn Hc] as %b ⟨Hb, Hcap⟩
  · isplitl [Hn]
    · iexact Hn
    · iexact Hc
  iapply HΦ
  simp only [List.nil_append, cU64]
  iframe

theorem examples.swiftnet.rpcEnc_defs_RegisterReply.wp_proof :
    examples.swiftnet.rpcEnc_defs_RegisterReply.spec := by
  intro b bs v ns dq
  obtain ⟨i, sl, r, l⟩ := v
  iintro %Φ ⟨Hb, Hcap, Hns⟩ HΦ
  ihave Hb := bytesOwn_intro b bs $$ [Hb Hcap]
  · iframe
  wp_apply wp_rpcEnc_defs_RegisterReply (bs := bs) $$ [Hb Hns] as %b' ⟨⟨Hb, Hcap⟩, Hns⟩
  · iframe
  iapply HΦ
  simp only [kitBody]
  iframe

theorem examples.swiftnet.rpcEnc_defs_GetReplicaListReply.wp_proof :
    examples.swiftnet.rpcEnc_defs_GetReplicaListReply.spec := by
  intro b bs v rs al dq1 dq2
  obtain ⟨s1, s2, r⟩ := v
  iintro %Φ ⟨Hb, Hcap, H1, H2⟩ HΦ
  ihave Hb := bytesOwn_intro b bs $$ [Hb Hcap]
  · iframe
  wp_apply wp_rpcEnc_defs_GetReplicaListReply (bs := bs) $$ [Hb H1 H2] as %b' ⟨⟨Hb, Hcap⟩, H1, H2⟩
  · iframe
  iapply HΦ
  simp only [kitBody]
  iframe

theorem examples.swiftnet.rpcEnc_defs_GetLeaderReply.wp_proof :
    examples.swiftnet.rpcEnc_defs_GetLeaderReply.spec := by
  intro b bs v
  obtain ⟨i⟩ := v
  iintro %Φ ⟨Hb, Hcap⟩ HΦ
  ihave Hb := bytesOwn_intro b bs $$ [Hb Hcap]
  · iframe
  wp_apply wp_rpcEnc_defs_GetLeaderReply (bs := bs) $$ [Hb] as %b' ⟨Hb, Hcap⟩
  · iframe
  iapply HΦ
  simp only [kitBody]
  iframe

end proofs

end Perennial.github_com.imdea_software.swiftpaxos
