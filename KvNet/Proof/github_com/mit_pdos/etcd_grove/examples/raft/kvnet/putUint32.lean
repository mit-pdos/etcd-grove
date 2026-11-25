/-
The proof of `KvNet/Spec/.../kvnet/putUint32.lean` (kvudp, phase 2: `notes/kvudp-proof-plan.md`).
-/
module

public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.putUint32

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

theorem putUint32.wp_proof :
    putUint32.spec (GF := GF) (hG := hG) := by
  intro buf B x
  wp_start as ⟨HB, Hcap⟩
  try wp_auto
  ihave Hn := slice_array (GF := GF) n_ptr _ _ (by decide) $$ n
  rw [show (zero_val (GoArray w8 4)).arr = List.replicate 4 (W8 0) ++ [] from rfl,
    show W64 (4 : Int) = W64 4 from rfl] at *
  simp only [show sint.Z (W64 0) = 0 from rfl, go.arrayIndexRef_0,
    show W64 4 - W64 0 = W64 4 from rfl]
  wp_apply encoding.binary.wp_LittleEndian_PutUint32 _ (List.replicate 4 (W8 0)) [] x rfl
    $$ [$Hn] as Hn
  try wp_auto
  simp only [show sint.Z (W64 0) = 0 from rfl, go.arrayIndexRef_0,
    show W64 4 - W64 0 = W64 4 from rfl, List.append_nil]
  wp_apply wp_slice_append buf B _ (u32Le x) (DFrac.own 1) $$ [$HB $Hcap $Hn] as %s1 ⟨Hs1, Hcap1, -⟩
  iapply HΦ
  iframe

end proof

end raft_kvnet
end EtcdGrove
end Perennial
