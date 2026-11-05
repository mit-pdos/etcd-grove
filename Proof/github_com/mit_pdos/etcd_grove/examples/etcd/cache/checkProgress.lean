/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/etcd/cache/checkProgress.lean` (2026-11-03):
the last event's revision is `1` plus the number of events. Lean-first (no Rocq counterpart).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.cache.checkProgress

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_cache

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.etcd.cache

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.cache.Assumptions]

theorem checkProgress.wp_proof : checkProgress.spec (GF := GF) (hG := hG) := by
  intro sl evs p hrev hp
  wp_start as #Hs
  ihave %Hl := ownSlice_len $$ Hs
  wp_auto
  wp_if_destruct
  · -- some events: the last one's revision
    have hpos : 0 < evs.length := by word
    list_elem evs (evs.length - 1) as x
    have Hb' : 0 ≤ sint.Z (sl.len - W64 1) ∧ sint.Z (sl.len - W64 1) < sint.Z sl.len := by word
    simp only [Hb', _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index sl (sint.Z (sl.len - W64 1)) evs DFrac.discard x (by word)
      $$ [Hs] as -
    · iframe #; ipureintro
      rw [show (sint.Z (sl.len - W64 1)).toNat = evs.length - 1 by word]; exact Hx_lookup
    have hx := hrev _ x Hx_lookup
    (try wp_auto)
    wp_if_destruct
    · exfalso; omega
    · (try wp_auto); iapply HΦ; itrivial
  · -- none: `1`
    have h0 : evs.length = 0 := by word
    (try wp_auto)
    wp_if_destruct
    · exfalso
      have : sint.Z (W64 1) = 1 := by decide
      omega
    · (try wp_auto); iapply HΦ; itrivial

end proof

end etcd_cache
end EtcdGrove
end Perennial
