/-
The proof of `rpctransport.Transport.DecodePeer`.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.rpctransport.Transport__DecodePeer

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

theorem github_com.hashicorp.raft.examples.hraftnet.rpctransport.Transport.DecodePeer.wp_proof :
    github_com.hashicorp.raft.examples.hraftnet.rpctransport.Transport.DecodePeer.spec (GF := GF) (hG := hG) := by
  intro t buf dq b
  wp_start as Hb
  wp_auto
  wp_apply wp_bytes_to_string $$ [$Hb] as Hb
  wp_end

end proof

end Perennial
