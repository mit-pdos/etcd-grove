/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/kvreconf/readCtx.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.kvreconf.readCtx
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvreconf.encode

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvreconf

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvreconf.Assumptions]

theorem readCtx.wp_proof (wp_encode : encode.spec (GF := GF) (hG := hG)) :
    readCtx.spec (GF := GF) (hG := hG) := by
  intro replica seq key Hk
  wp_start
  wp_auto
  wp_apply wp_slice_make2 (V := w8) $$ [] as %b ⟨Hb, Hbcap⟩
  · ipureintro; decide
  rw [show List.replicate 8 (zero_val w8) = List.replicate 8 (W8 0) ++ [] from rfl]
  wp_apply encoding.binary.wp_LittleEndian_PutUint64 b (List.replicate 8 (W8 0)) [] replica rfl
    $$ [$Hb] as Hb
  try wp_auto
  wp_apply wp_encode seq (W8 3) key [] Hk (by simp) as %e ⟨He, Hecap⟩
  wp_apply wp_slice_append b _ e _ (DFrac.own 1) $$ [$Hb $Hbcap $He] as %b' ⟨Hb', Hb'cap, -⟩
  iapply HΦ
  iframe Hb'cap
  unfold readCtxB opReadB
  simp only [List.append_nil]
  iexact Hb'

end proof

end kvreconf
end EtcdGrove
end Perennial
