/-
The proof of `rpctransport.Transport.EncodePeer`.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.rpctransport.Transport__EncodePeer

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
variable [π : Net.NetProtoGS] [net.rpc.Assumptions] [net.Assumptions]

open github_com.hashicorp.raft.examples.hraftnet.rpctransport

set_option goose.wp.extras true

theorem github_com.hashicorp.raft.examples.hraftnet.rpctransport.Transport.EncodePeer.wp_proof :
    github_com.hashicorp.raft.examples.hraftnet.rpctransport.Transport.EncodePeer.spec (GF := GF) (hG := hG) := by
  intro t id a
  wp_start
  wp_auto
  wp_apply wp_string_to_bytes as %sl ⟨Hsl, -⟩
  wp_end

end proof

end Perennial
