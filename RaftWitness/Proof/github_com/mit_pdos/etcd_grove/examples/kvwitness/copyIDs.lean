/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/kvwitness/copyIDs.lean`. Lean-first
(2026-10-20, W4).
-/
module

public import RaftWitness.Spec.github_com.mit_pdos.etcd_grove.examples.kvwitness.copyIDs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvwitness

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvwitness.Assumptions]

theorem copyIDs.wp_proof : copyIDs.spec (GF := GF) (hG := hG) := by
  intro sl l dq
  wp_start as Hsl
  ihave %Hlen := ownSlice_len $$ Hsl
  try wp_auto
  wp_apply wp_slice_make2 (V := w64) sl.len $$ [] as %c ⟨Hc, Hcap⟩
  · ipureintro; exact Hlen.2
  try wp_auto
  wp_apply wp_slice_copy (V := w64) c _ sl l dq $$ [$Hc $Hsl] as %k ⟨-, Hc, Hsl⟩
  have e : l.take (List.replicate (sint.nat sl.len) (zero_val w64)).length ++
      (List.replicate (sint.nat sl.len) (zero_val w64)).drop l.length = l := by
    rw [List.length_replicate, ← Hlen.1, List.take_length, List.drop_replicate, Nat.sub_self,
      List.replicate_zero, List.append_nil]
  rw [e]
  try wp_auto
  iapply HΦ
  iframe

end proof

end kvwitness
end EtcdGrove
end Perennial
