/-
The proof of `KvRaft/Spec/.../kvraft/putAck.lean` (kvraft-udp, phase 2: `notes/kvraft-udp-proof-plan.md`).
-/
module

public import KvRaft.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.putAck
public import KvRaft.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.putHeader

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvraft

open Iris Iris.BI Iris.ProofMode Net Udp go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvraft.Assumptions]

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
  unfold ackBytes kindAckB
  rw [List.nil_append]
  iexact Hs

end proof

end kvraft
end EtcdGrove
end Perennial
