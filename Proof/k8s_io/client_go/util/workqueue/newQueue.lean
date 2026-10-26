/-
Proof of `Spec/k8s_io/client_go/util/workqueue/newQueue.lean`. Lean-first.
-/
module

public import Spec.k8s_io.client_go.util.workqueue.newQueue
public import Proof.sync.MutexLitSemantics
public import Proof.k8s_io.client_go.util.workqueue.Lemmas

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace workqueue

open Iris Iris.BI Iris.ProofMode k8s_io.client_go.util.workqueue

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.util.workqueue.Assumptions]

theorem newQueue.wp_proof [EtcdGrove.MutexLitSemantics] : newQueue.spec (GF := GF) (hG := hG) := by
  intro K T _ c l nm period
  wp_start as Hfifo
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  iapply wp_fupd
  wp_auto
  wp_apply wp_map_make1 (K := K) (V := sets.Elem) T k8s_io.apimachinery.pkg.util.sets.Empty.ty
    as %dm Hdm
  wp_apply wp_map_make1 (K := K) (V := sets.Elem) T k8s_io.apimachinery.pkg.util.sets.Empty.ty
    as %pm Hpm
  wp_alloc_anon
  rename_i mu
  irename : (mu ↦ (false : sync.Mutex) : IProp GF) => Hmu
  wp_auto
  wp_apply sync.wp_NewCond as %cv #Hcv
  wp_apply chan.wp_make1 (V := Unit) as %ch %γch ⟨#Hch, %_, Hoc⟩
  (try wp_auto)
  iStructNamed «$r0»
  -- the wait group, its invariant, the shutdown tokens
  imod sync.init_WaitGroup (wqN.@"wg") (structFieldRef (Typed K) go!"wg" «$r0_ptr») $$ wg
    with ⟨%γwg, #Hwg, Hctr, Hwaiters⟩
  imod ownTokAuth_alloc (GF := GF) with ⟨%pool, Hpa⟩
  imod ownTokAuth_add shutdownPool pool 0 $$ Hpa with ⟨Hpa, Htoks⟩
  imod ownToks_0 (GF := GF) pool with H0
  -- the stop channel and its `Once`
  imod alloc_broadcast_chan (E := ⊤) (iprop(True) : IProp GF) γch ch $$ Hch Hoc with Hbc
  imod sync.init_Once (structFieldRef (Typed K) go!"stopOnce" «$r0_ptr»)
    (ownBroadcastChan ch γch iprop(True) .Pending) iprop(True) ⊤ $$ [stopOnce Hbc] with #Honce
  · iframe
  -- the processing set's ghost map, the flag's ghost variable
  imod ghost_map_alloc (GF := GF) (K := K) (V := sets.Elem) ∅ with ⟨%γp, Hpauth, -⟩
  imod dghostVar_alloc (GF := GF) (A := Bool) false with ⟨%γsd, Hsdg⟩
  let γ : QNames := ⟨γp, γsd, pool, γwg, γch⟩
  imod inv_alloc (wqN.@"wginv") ⊤ (wgInv (GF := GF) γ) $$ [Hctr Hwaiters H0 Hpa] with #Hwginv
  · inext; iexists 0; simp only [γ]; iframe
  ipersist queue
  ipersist dirty
  ipersist processing
  ipersist cond
  ipersist metrics
  ipersist stopCh
  let L : QLocs := ⟨l, dm, pm, cv, mu, ch⟩
  imod sync.init_Mutex (qLockInv (K := K) «$r0_ptr» L γ) ⊤ mu $$ Hmu
    [Hfifo Hdm Hpm shuttingDown drain Hpauth Hsdg] with #Hmux
  · inext; iunfold qLockInv
    iexists QState.init, false
    simp only [QState.init, sdGhost, Bool.false_eq_true, ↓reduceIte, γ, L]
    iframe
    ipureintro; exact QState.init_wf
  imodintro
  iapply HΦ
  isplitr
  · iunfold isTyped
    iexists L
    simp only [named, L, γ]
    iframe #
  iunfold shutdownToks
  simp only [γ]
  iexact Htoks

end proof

end workqueue
end EtcdGrove
end Perennial
