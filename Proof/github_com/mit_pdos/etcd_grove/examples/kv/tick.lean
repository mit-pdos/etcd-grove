/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/kv/tick.lean`. Lean-first (no
Rocq counterpart).
-/
module

public import Proof.ReceiptTactics
public import Spec.github_com.mit_pdos.etcd_grove.examples.kv.tick
public import Perennial.Proof.time

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kv

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kv.Assumptions]
variable [StorageModel GF]

theorem tick.wp_proof (wp_node_Tick : node.Tick.spec (GF := GF) (hG := hG)) :
    tick.spec (GF := GF) (hG := hG) := by
  intro γ id n
  wp_start as #HisNode
  wp_auto
  ihave IH : iprop(∃ k : w64, "i" ∷ i_ptr ↦ k ∗
      "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ (ticksN : Int)⌝) $$ [i]
  · iexists W64 0
    iframe i
    ipureintro; unfold ticksN; constructor <;> word
  ihave #Hraftinit : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 $$ []
  · iPkgInit
  wp_for IH
  wp_if_destruct
  · have Hlt : sint.nat k < ticksN := by unfold ticksN at *; word
    wp_apply +noauto time.wp_Sleep
    -- the resolution of `Tick`'s receipt (until 2026-10-30 the tick's credit; unused now)
    wp_take_receipt as _Hc1
    wp_apply wp_node_Tick n γ kvRaftN id $$ [$Hraftinit $HisNode]
    wp_for_post
    iframe
    iexists k + W64 1
    iframe
    ipureintro; unfold ticksN at *; constructor <;> word
  · iapply HΦ
    itrivial

end proof

end kv
end EtcdGrove
end Perennial
