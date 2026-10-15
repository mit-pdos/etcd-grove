/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/raftNode__advanceTicks.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.raftNode__advanceTicks
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.raftNode__tick

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

theorem raftNode.advanceTicks.wp_proof (wp_tick : raftNode.tick.spec (GF := GF) (hG := hG)) :
    raftNode.advanceTicks.spec (GF := GF) (hG := hG) := by
  intro E γ r ticks
  wp_start as ⟨#Hr, HT⟩
  wp_auto
  ihave IH : iprop(∃ k : w64, "i" ∷ i_ptr ↦ k ∗
      "HT" ∷ ([∗list] _u ∈ List.replicate ((sint.Z ticks).toNat - sint.nat k) (), E.T) ∗
      "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ max 0 (sint.Z ticks)⌝) $$ [i HT]
  · iexists W64 0
    iframe i
    simp only [show sint.nat (W64 0) = 0 by rfl, Nat.sub_zero]
    iframe HT
    ipureintro; constructor <;> word
  wp_for IH
  wp_if_destruct
  · have Hlt : sint.nat k < (sint.Z ticks).toNat := by word
    rw [show (sint.Z ticks).toNat - sint.nat k = ((sint.Z ticks).toNat - (sint.nat k + 1)) + 1
      by omega, List.replicate_succ]
    icases BigSepL.bigSepL_cons.1 $$ HT with ⟨HT1, HT⟩
    wp_apply wp_tick E γ r $$ [$Hpkg $Hr $HT1]
    wp_for_post
    iframe
    iexists k + W64 1
    rw [show sint.nat (k + W64 1) = sint.nat k + 1 by word]
    iframe
    ipureintro; constructor <;> word
  · iapply HΦ
    itrivial

end proof

end EtcdGrove
end Perennial
