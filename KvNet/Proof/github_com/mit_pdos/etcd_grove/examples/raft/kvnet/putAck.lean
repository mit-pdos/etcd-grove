/-
The proof of `KvNet/Spec/.../kvnet/putAck.lean` (kvudp, phase 2: `notes/kvudp-proof-plan.md`).
-/
module

public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.putAck
public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.putHeader

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace raft_kvnet

open Iris Iris.BI Iris.ProofMode Net Udp go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Assumptions]

theorem putAck.wp_proof
    (wp_putHeader : putHeader.spec (GF := GF) (hG := hG)) :
    putAck.spec (GF := GF) (hG := hG) := by
  intro src dst boot seq
  wp_start
  try wp_auto
  wp_apply wp_slice_make3 (V := w8) (W64 0) (W64 37) (by decide) as %buf ⟨Hbuf, Hcap, -⟩
  rw [show List.replicate 0 (zero_val w8) = [] from rfl]
  try wp_auto
  wp_apply wp_putHeader buf [] _ src dst boot seq $$ [$Hbuf $Hcap] as %s ⟨Hs, Hscap⟩
  try wp_auto
  iapply HΦ
  iframe Hscap
  rw [show ackBytes src dst boot seq = [] ++ headerBytes (W8 2) src dst boot seq from rfl]
  iexact Hs

end proof

end raft_kvnet
end EtcdGrove
end Perennial
