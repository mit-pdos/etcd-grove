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
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

theorem raftNode.advanceTicks.wp_proof (wp_tick : raftNode.tick.spec (GF := GF) (hG := hG)) :
    raftNode.advanceTicks.spec (GF := GF) (hG := hG) := by
  intro E γ r ticks
  wp_start as #Hr
  wp_auto
  ihave IH : iprop(∃ k : w64, "i" ∷ i_ptr ↦ k ∗
      "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ max 0 (sint.Z ticks)⌝) $$ [i]
  · iexists W64 0
    iframe i
    ipureintro; constructor <;> word
  wp_for IH
  wp_if_destruct
  · have Hlt : sint.nat k < (sint.Z ticks).toNat := by word
    wp_apply wp_tick E γ r $$ [$Hpkg $Hr]
    wp_for_post
    iframe
    iexists k + W64 1
    iframe
    ipureintro; constructor <;> word
  · iapply HΦ
    itrivial

end proof

end EtcdGrove
end Perennial
