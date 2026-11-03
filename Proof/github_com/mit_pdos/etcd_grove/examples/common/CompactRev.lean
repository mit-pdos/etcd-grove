/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/common/CompactRev.lean` (C3's watch side,
2026-11-02). Lean-first (no Rocq counterpart). The channel's first receive (`wp_respChan_receive`):
closed, `0, false`; a response, its compaction revision tested.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.common.CompactRev

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace common

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open go_etcd_io.etcd.server.v3.etcdserver github_com.mit_pdos.etcd_grove.examples.common

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.common.Assumptions]

theorem CompactRev.wp_proof : CompactRev.spec (GF := GF) (hG := hG) := by
  intro CS Ok wch γ c0
  wp_start as ⟨#Hw, Hcons⟩
  (try wp_auto)
  wp_apply (wp_respChan_receive wch γ Ok 0 c0) $$ [Hcons] as %v %ok H
  · iframe #; iframe
  cases ok
  · -- the channel closed
    simp only [Bool.false_eq_true, ↓reduceIte]
    (try wp_auto)
    iapply HΦ
    iintro %h; cases h
  simp only [↓reduceIte]
  imod H with ⟨%r, %c', #Hr, Hok, Hcons⟩
  (try wp_auto)
  wp_if_destruct
  · -- not a compaction's
    (try wp_auto)
    iapply HΦ
    iintro %h; cases h
  · (try wp_auto)
    iapply HΦ
    iintro -
    iexists c', v, r
    iframe Hok
    ipureintro
    exact ⟨rfl, Hif⟩

end proof

end common
end EtcdGrove
end Perennial
