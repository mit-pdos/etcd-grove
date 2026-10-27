/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/v3compactor/newPeriodic.lean`. Lean-first (no Rocq
counterpart). The spec-first pilot's phase 1 (`notes/compactor-pilot-plan.md`): the spec is written,
the proof is phase 1's glue.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor.newPeriodic
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor.Periodic__getRetentions
public import Spec.context.WithCancelBackground

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.api v3compactor

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor.Assumptions]

theorem v3compactor.newPeriodic.wp_proof
    (hPeriodic_getRetentions : v3compactor.Periodic.getRetentions.spec (GF := GF) (hG := hG))
    (hWithCancelBackground : context.WithCancelBackground.spec (GF := GF) (hG := hG)) :
    v3compactor.newPeriodic.spec (GF := GF) (hG := hG) := by
  intro lg clk h E H10
  wp_start as ⟨%Hlgnn, #Hclk⟩
  ihave #Pctx : isPkgInit (PROP := IProp GF) pkg_id.context $$ []
  · iPkgInit
  ihave #Psync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  wp_auto
  iStructNamed «$r0»
  -- the run's first sample, unset
  imod dghostVar_alloc (A := Option Int) none with ⟨%γf, Hf⟩
  -- `mu` over `paused`: the writer guard (`Pause`, `Resume`) and one reader slot (`Run`'s goroutine)
  imod sync.init_RWMutex (perPausedInv «$r0_ptr») (structFieldRef v3compactor.Periodic go!"mu" «$r0_ptr»)
    $$ [paused] mu with Hslots
  · inext; iunfold perPausedInv; iexists false; iexact paused
  icases sync.ownRWMutex_slots_guard _ _ $$ Hslots with ⟨Hslots, #Hguard⟩
  obtain ⟨m, hm⟩ : ∃ m, Int.toNat sync.rwmutex.actualMaxReaders = m + 1 :=
    ⟨_, (Nat.succ_pred_eq_of_pos (by have := sync.actualMaxReaders_ge_2; omega)).symm⟩
  rw [hm, List.replicate_succ]
  icases BigSepL.bigSepL_cons.1 $$ Hslots with ⟨Hslot, -⟩
  -- the fields are read-only once stored: persisted under the postcondition's update
  iapply wp_fupd
  wp_apply (hPeriodic_getRetentions «$r0_ptr» h (DFrac.own 1) H10) $$ [$period] as %n ⟨%Hn, period⟩
  have hn : 1 ≤ sint.Z n := by
    rw [Hn]; unfold retentionsOf
    have := retentions_bound (sint.Z h) H10 (by word)
    omega
  wp_apply (wp_slice_make3 (V := w64) (W64 0) n ⟨by word, by word⟩) as %sl ⟨Hsl, Hcap, %Hslc⟩
  (try wp_auto)
  wp_apply _root_.Perennial.context.wp_Background
  wp_apply hWithCancelBackground as %ctx %γctx %cancel ⟨#Hcs, #Hctx⟩
  ipersist lg
  ipersist clock
  ipersist period
  ipersist rg
  ipersist c
  ipersist ctx
  ipersist cancel
  imodintro
  iapply HΦ
  isplitr
  · unfold isPeriodic
    iexists lg, clk, h, ctx, { Values := ∅, Deadline := none, Done_gn := γctx, PDone := iprop(True) },
      γctx, cancel
    iframe
    iframe #
    ipureintro
    exact ⟨Hlgnn, rfl, H10⟩
  · iexists γf
    unfold periodicRunTok firstUnset
    iframe
    first
      | (rw [show sint.nat (W64 0) = 0 from rfl, List.replicate_zero]; iexact Hsl)
      | (rw [List.replicate_zero]; iexact Hsl)

end proof

end EtcdGrove
end Perennial
