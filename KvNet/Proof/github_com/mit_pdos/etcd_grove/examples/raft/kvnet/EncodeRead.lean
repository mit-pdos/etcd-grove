/-
The proof of `KvNet/Spec/.../kvnet/EncodeRead.lean`: `putUint64` into `nil`, then `putBytes` of the
key's bytes.
-/
module

public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.EncodeRead
public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.putUint64
public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.putBytes

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

theorem EncodeRead.wp_proof (wp_putUint64 : putUint64.spec (GF := GF) (hG := hG))
    (wp_putBytes : putBytes.spec (GF := GF) (hG := hG)) :
    EncodeRead.spec (GF := GF) (hG := hG) := by
  intro seq key
  wp_start
  wp_auto
  ihave Hn := ownSlice_nil (V := w8) (GF := GF) (DFrac.own 1)
  ihave Hnc := ownSliceCap_nil (V := w8) (GF := GF)
  wp_apply wp_putUint64 slice.nil [] seq $$ [$Hn $Hnc] as %s1 ⟨Hs1, Hc1⟩
  try wp_auto
  wp_apply wp_string_to_bytes key as %kb ⟨Hkb, -⟩
  wp_apply wp_putBytes s1 kb _ key (DFrac.own 1) $$ [$Hs1 $Hc1 $Hkb] as %s2 ⟨Hs2, Hc2, -⟩
  try wp_auto
  iapply HΦ
  iframe

end proof

end raft_kvnet
end EtcdGrove
end Perennial
