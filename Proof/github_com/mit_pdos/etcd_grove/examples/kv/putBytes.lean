/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/kv/putBytes.lean`. Lean-first (no
Rocq counterpart).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.kv.putBytes

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kv

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kv.Assumptions]

theorem putBytes.wp_proof : putBytes.spec (GF := GF) (hG := hG) := by
  intro buf b B bs dq
  wp_start as ⟨HB, Hcap, Hb⟩
  try wp_auto
  ihave %Hbl := ownSlice_len _ _ _ $$ Hb
  ihave Hn := slice_array (GF := GF) n_ptr _ _ (by decide) $$ n
  rw [show (zero_val (GoArray w8 8)).arr = List.replicate 8 (W8 0) ++ [] from rfl,
    show W64 (8 : Int) = W64 8 from rfl] at *
  simp only [show sint.Z (W64 0) = 0 from rfl, go.arrayIndexRef_0,
    show W64 8 - W64 0 = W64 8 from rfl]
  wp_apply encoding.binary.wp_LittleEndian_PutUint64 _ (List.replicate 8 (W8 0)) [] b.len rfl
    $$ [$Hn] as Hn
  try wp_auto
  simp only [show sint.Z (W64 0) = 0 from rfl, go.arrayIndexRef_0,
    show W64 8 - W64 0 = W64 8 from rfl, List.append_nil]
  wp_apply wp_slice_append buf B _ (u64Le b.len) (DFrac.own 1) $$ [$HB $Hcap $Hn] as %s1 ⟨Hs1, Hcap1, -⟩
  try wp_auto
  wp_apply wp_slice_append s1 _ b bs dq $$ [$Hs1 $Hcap1 $Hb] as %s2 ⟨Hs2, Hcap2, Hb⟩
  iapply HΦ
  iframe Hcap2 Hb
  have Hlen : b.len = W64 bs.length := by rw [Hbl.1]; word
  unfold putB
  rw [← Hlen, List.append_assoc]
  iexact Hs2

end proof

end kv
end EtcdGrove
end Perennial
