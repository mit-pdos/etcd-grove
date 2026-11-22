/-
The proof of `KvNet/Spec/.../kvnet/EncodeDisrupt.lean`: `putUint64` twice, from `nil`.
-/
module

public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.EncodeDisrupt
public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.putUint64

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

theorem EncodeDisrupt.wp_proof (wp_putUint64 : putUint64.spec (GF := GF) (hG := hG)) :
    EncodeDisrupt.spec (GF := GF) (hG := hG) := by
  intro what to
  wp_start
  wp_auto
  ihave Hn := ownSlice_nil (V := w8) (GF := GF) (DFrac.own 1)
  ihave Hnc := ownSliceCap_nil (V := w8) (GF := GF)
  wp_apply wp_putUint64 slice.nil [] what $$ [$Hn $Hnc] as %s1 ⟨Hs1, Hc1⟩
  try wp_auto
  wp_apply wp_putUint64 s1 _ to $$ [$Hs1 $Hc1] as %s2 ⟨Hs2, Hc2⟩
  try wp_auto
  iapply HΦ
  iframe

end proof

end raft_kvnet
end EtcdGrove
end Perennial
