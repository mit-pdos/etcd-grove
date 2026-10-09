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

theorem demux.Unregister.wp_proof
    (wp_Stop : watcher.Stop.spec (GF := GF) (hG := hG)) :
    demux.Unregister.spec (GF := GF) (hG := hG) := by
  intro d γd cap w γ predT s
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
  icases Htok with ⟨%pn, Helem, #HpredT⟩
  iNamed Hl
  icombine Hregs Helem gives %Hlook
  icases (BigSepM.bigSepM_delete (m := regs) Hlook).1 $$ Hres with ⟨Hr, Hres⟩
  iNamed Hr
  icombine Hviews Hview gives %Hvlook
  imod ghost_map_delete $$ Hregs Helem with Hregs
  imod ghost_map_delete $$ Hviews Hview with Hviews
  wp_auto
  wp_apply wp_mapDelete $$ Hact as Hact
  wp_apply (lc := 1) wp_mapDelete $$ Hlag as Hlag
  ihave Hl : demuxLocked d γd cap c c.stream.length (GMap.delete w regs) (GMap.delete w views)
    $$ [Hregs Hviews HminRev HmaxRev HactF HlagF Hact Hlag Hhist Hres]
  · iunfold demuxLocked
    iexists actP, lagP
    rw [actOf_delete, lagOf_delete]
    simp only [named]
    iframe
    ipureintro; exact Hok.unregister w
  imod demux_lock_release d γd cap c _ _ $$ [Hd Hcore Hl Hlc1] with HP
  · iframe; iframe #; ipureintro; exact Hinv
  wp_apply (lc := 1) sync.RWMutex.wp_Unlock $$ [$Hlk HP] as Hh
  · inext; iexact HP
  ihave Heq := predIs_agree pn pred predT $$ [Hpred HpredT]
  · iframe #
  imod lc_fupd_elim_later (E := ⊤) $$ Hlc1 Heq with %Heq
  wp_apply wp_Stop $$ [Hwat] as #Hcl
  · iframe; iexact Hw
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
