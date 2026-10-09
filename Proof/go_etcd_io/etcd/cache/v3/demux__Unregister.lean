/-
Proof of `Spec/demux__Unregister.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.cache.v3.demux__Unregister
public import Spec.go_etcd_io.etcd.cache.v3.watcher__Stop

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.cache.v3 go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

/-- What `Stop` needs to close a registration's watcher (`watcherClosePub`), from the lock's
certificate chain: the closed log's publication if the watcher is still open (mapped). -/
theorem unregister_closePub (C : DemuxCert GF) (c : DemuxCore) (ri : RegInfo) (v : View)
    (pred : Option (GoString → Bool)) (sent : List RespModel)
    (hst : v.phase.mapped = true → StartOk c ri v ∧ v.stream = c.stream)
    (hsr : ri.sr = W64 0 ∨ ri.s = ri.sr) (hD : Delivered pred ri.s v sent) :
    certChain C c.base c.stream ⊢
      watcherClosePub (demuxPub C pred ri.sr) sent none v.phase.toWatcher := by
  cases hph : v.phase with
  | active | lagging =>
    obtain ⟨hso, hstream⟩ := hst (by rw [hph]; rfl)
    simp only [RegPhase.toWatcher, watcherClosePub]
    rw [← hstream]
    exact pub_close pred ri.sr ri.s v sent none c.base hsr hD hso.cond (fun m h => by cases h)
  | closed c0 =>
    simp only [RegPhase.toWatcher, watcherClosePub]
    iintro _
    itrivial

theorem demux.Unregister.wp_proof
    (wp_Stop : watcher.Stop.spec (GF := GF) (hG := hG)) :
    demux.Unregister.spec (GF := GF) (hG := hG) := by
  intro d γd cap C w γ predT s
  wp_start as ⟨#Hd, Hh, Htok⟩
  wp_auto
  wp_apply wp_with_defer as %defer defer
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  unfold demuxHandle
  wp_apply (lc := 2) sync.RWMutex.wp_Lock $$ [$Hh] as ⟨Hlk, HP⟩
  icombine Hlc1 Hlc2 as Hlc
  imod demux_lock_acquire d γd cap $$ [Hd HP Hlc] with ⟨%c, %regs, %views, Hcore, Hl, %Hinv⟩
  · iframe; iframe #
  iunfold demuxRegistered at Htok
  icases Htok with ⟨%pn, %sr, Helem, #HpredT⟩
  iNamed Hl
  icombine Hregs Helem gives %Hlook
  icases (BigSepM.bigSepM_delete (m := regs) Hlook).1 $$ Hres with ⟨Hr, Hres⟩
  iNamed Hr
  icombine Hviews Hview gives %Hvlook
  ihave #Hcp := unregister_closePub C c (RegInfo.mk γ s pn sr) v pred sent
    (fun hm => ⟨Hstart.get Hlook Hvlook hm, (Hok.mapped w v Hvlook hm).1⟩)
    (Hstart.sr_ok w _ Hlook) Hdel $$ Hcerts
  imod ghost_map_delete $$ Hregs Helem with Hregs
  imod ghost_map_delete $$ Hviews Hview with Hviews
  wp_auto
  wp_apply wp_mapDelete $$ Hact as Hact
  wp_apply (lc := 1) wp_mapDelete $$ Hlag as Hlag
  ihave Hl : demuxLocked d γd cap C c c.stream.length (GMap.delete w regs) (GMap.delete w views)
    $$ [Hregs Hviews HminRev HmaxRev HactF HlagF Hact Hlag Hhist Hres]
  · iunfold demuxLocked
    iexists actP, lagP
    rw [actOf_delete, lagOf_delete]
    simp only [named]
    iframe
    iframe #
    ipureintro; exact ⟨Hok.unregister w, Hstart.unregister w⟩
  imod demux_lock_release d γd cap c _ _ $$ [Hd Hcore Hl Hlc1] with HP
  · iframe; iframe #; ipureintro; exact Hinv
  wp_apply (lc := 1) sync.RWMutex.wp_Unlock $$ [$Hlk HP] as Hh
  · inext; iexact HP
  ihave Heq := predIs_agree pn pred predT $$ [Hpred HpredT]
  · iframe #
  imod lc_fupd_elim_later (E := ⊤) $$ Hlc1 Heq with %Heq
  wp_apply wp_Stop $$ [Hwat] as #Hcl
  · iframe; iframe #
  subst Heq
  iapply HΦ
  iframe
  iexists sent, _
  iframe Hcl
  ipureintro
  refine ⟨v, Hdel, ?_⟩
  intro m hm
  apply Hdel.cancel
  cases hph : v.phase <;> simp_all [RegPhase.toWatcher, WatcherPhase.cancelAfter]

end proof

end EtcdGrove
end Perennial
