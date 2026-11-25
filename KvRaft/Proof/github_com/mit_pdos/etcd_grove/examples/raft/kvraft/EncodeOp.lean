/-
The proof of `KvRaft/Spec/.../kvraft/EncodeOp.lean`: a call of `encode` (kvdurable's spec, reused).
-/
module

public import KvRaft.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.EncodeOp
public import KvRaft.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.encode

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvraft

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvraft.Assumptions]

theorem EncodeOp.wp_proof (wp_encode : encode.spec (GF := GF) (hG := hG)) :
    EncodeOp.spec (GF := GF) (hG := hG) := by
  intro id kind key val Hk Hv
  wp_start
  wp_auto
  wp_apply wp_encode id kind key val Hk Hv as %b ⟨Hb, Hc⟩
  iapply HΦ
  iframe

end proof

end kvraft
end EtcdGrove
end Perennial
