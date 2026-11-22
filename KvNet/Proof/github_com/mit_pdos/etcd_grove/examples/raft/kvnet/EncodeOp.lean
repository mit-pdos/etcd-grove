/-
The proof of `KvNet/Spec/.../kvnet/EncodeOp.lean`: a call of `encode` (kvdurable's spec, reused).
-/
module

public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.EncodeOp
public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.encode

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace raft_kvnet

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Assumptions]

theorem EncodeOp.wp_proof (wp_encode : encode.spec (GF := GF) (hG := hG)) :
    EncodeOp.spec (GF := GF) (hG := hG) := by
  intro id kind key val Hk Hv
  wp_start
  wp_auto
  wp_apply wp_encode id kind key val Hk Hv as %b ⟨Hb, Hc⟩
  iapply HΦ
  iframe

end proof

end raft_kvnet
end EtcdGrove
end Perennial
