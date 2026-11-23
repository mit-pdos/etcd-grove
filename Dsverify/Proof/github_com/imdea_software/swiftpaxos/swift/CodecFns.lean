/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/CodecFns.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
The proofs of the codec functions' specs the replica's dispatch calls (`Rcvr.lean`), as
instances of the codec group's lemmas (`Proof/swiftnet/codec/DecodeAs.lean`, `Enc.lean`), the
way `Proof/swiftnet/codec/CodecFns.lean` proves the master's.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.Rcvr
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
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF]
variable [examples.swiftnet.Assumptions]

open examples.swiftnet sp

theorem examples.swiftnet.rpcDecodeAs_defs_BeTheLeaderArgs.wp_proof :
    examples.swiftnet.rpcDecodeAs_defs_BeTheLeaderArgs.spec := by
  intro data dq
  iintro %Φ Hb HΦ
  wp_apply wp_rpcDecodeAs_defs_BeTheLeaderArgs $$ Hb as %v %err Hpost
  unfold decAsPost
  icases Hpost with ⟨Hb, (⟨%He, %x, -, -⟩ | ⟨-, %Hne⟩)⟩
  · subst He
    iapply HΦ; iexact Hb
  · exact absurd rfl (Hne .beTheLeaderArgs rfl trivial)

theorem examples.swiftnet.rpcDecodeAs_defs_PingArgs.wp_proof :
    examples.swiftnet.rpcDecodeAs_defs_PingArgs.spec := by
  intro data dq a
  iintro %Φ Hb HΦ
  wp_apply wp_rpcDecodeAs_defs_PingArgs $$ Hb as %v %err Hpost
  unfold decAsPost
  icases Hpost with ⟨Hb, (⟨%He, %x, Hown, %Hx⟩ | ⟨-, %Hne⟩)⟩
  · iunfold ownPA at Hown
    icases Hown with %Hown
    have h := Hx (.pingArgs a) rfl trivial rfl
    subst h He
    obtain ⟨a'⟩ := v
    simp only [id, KitVal.pingArgs.injEq] at Hown
    subst Hown
    iapply HΦ; iexact Hb
  · exact absurd rfl (Hne (.pingArgs a) rfl trivial)

theorem examples.swiftnet.rpcEnc_defs_BeTheLeaderReply.wp_proof :
    examples.swiftnet.rpcEnc_defs_BeTheLeaderReply.spec := by
  intro b bs v
  obtain ⟨l, n⟩ := v
  iintro %Φ ⟨Hb, Hcap⟩ HΦ
  ihave Hb := bytesOwn_intro b bs $$ [Hb Hcap]
  · iframe
  wp_apply wp_rpcEnc_defs_BeTheLeaderReply (bs := bs) $$ [Hb] as %b' ⟨Hb, Hcap⟩
  · iframe
  iapply HΦ
  simp only [kitBody]
  iframe

theorem examples.swiftnet.rpcEnc_defs_PingReply.wp_proof :
    examples.swiftnet.rpcEnc_defs_PingReply.spec := by
  intro b bs v
  iintro %Φ ⟨Hb, Hcap⟩ HΦ
  ihave Hb := bytesOwn_intro b bs $$ [Hb Hcap]
  · iframe
  wp_apply wp_rpcEnc_defs_PingReply (bs := bs) $$ [Hb] as %b' ⟨Hb, Hcap⟩
  · iframe
  iapply HΦ
  simp only [kitBody, List.append_nil]
  iframe

end proofs

end Perennial.github_com.imdea_software.swiftpaxos
