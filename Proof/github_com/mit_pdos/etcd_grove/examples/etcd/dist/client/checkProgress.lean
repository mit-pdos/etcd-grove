/- Lean-first (no Rocq counterpart). The proof of `checkProgress`, the dist package's copy of the cache
example's: the cache example's proof (`Proof/github_com/mit_pdos/etcd_grove/examples/etcd/cache/checkProgress.lean`),
adapted to the copy's translation (the last event's `Rev` read through its field, no local `e`). -/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.checkProgress

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_dist_client

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open etcd_cache

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.Assumptions]

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
    -- `evs[len(evs)-1].Rev`: the last event's `Rev` field, read-only
    have Hxl : evs[(sint.Z (sl.len - W64 1)).toNat]? = some x := by
      rw [show (sint.Z (sl.len - W64 1)).toNat = evs.length - 1 by word]; exact Hx_lookup
    icases ownSlice_elem_acc (sint.Z (sl.len - W64 1)) x sl DFrac.discard evs (by word) Hxl $$ Hs
      with ⟨#Hx, -⟩
    icases (github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Event.Event_access_load_Rev
        (sliceIndexRef cev (sint.Z (sl.len - W64 1)) sl) x DFrac.discard).access_strict $$ Hx
      with ⟨#Hxr, -⟩
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

end etcd_dist_client
end EtcdGrove
end Perennial
