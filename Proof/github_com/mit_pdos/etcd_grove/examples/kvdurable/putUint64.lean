/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/kvdurable/putUint64.lean`. Lean-first (no
Rocq counterpart): `putBytes`'s first half (Perennial's `LittleEndian.PutUint64` into a fresh array,
appended).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.kvdurable.putUint64

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvdurable

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvdurable.Assumptions]

theorem putUint64.wp_proof : putUint64.spec (GF := GF) (hG := hG) := by
  intro buf B x
  wp_start as ⟨HB, Hcap⟩
  try wp_auto
  ihave Hn := slice_array (GF := GF) n_ptr _ _ (by decide) $$ n
  rw [show (zero_val (GoArray w8 8)).arr = List.replicate 8 (W8 0) ++ [] from rfl,
    show W64 (8 : Int) = W64 8 from rfl] at *
  simp only [show sint.Z (W64 0) = 0 from rfl, go.arrayIndexRef_0,
    show W64 8 - W64 0 = W64 8 from rfl]
  wp_apply encoding.binary.wp_LittleEndian_PutUint64 _ (List.replicate 8 (W8 0)) [] x rfl
    $$ [$Hn] as Hn
  try wp_auto
  simp only [show sint.Z (W64 0) = 0 from rfl, go.arrayIndexRef_0,
    show W64 8 - W64 0 = W64 8 from rfl, List.append_nil]
  wp_apply wp_slice_append buf B _ (u64Le x) (DFrac.own 1) $$ [$HB $Hcap $Hn] as %s1 ⟨Hs1, Hcap1, -⟩
  iapply HΦ
  iframe

end proof

end kvdurable
end EtcdGrove
end Perennial
