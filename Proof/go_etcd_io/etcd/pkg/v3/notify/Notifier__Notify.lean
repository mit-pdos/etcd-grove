/-
Proof of `Spec/go_etcd_io/etcd/pkg/v3/notify/Notifier__Notify.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.pkg.v3.notify.Notifier__Notify

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.pkg.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.pkg.v3.notify.Assumptions]

theorem notify.Notifier.Notify.wp_proof : notify.Notifier.Notify.spec (GF := GF) (hG := hG) := by
  intro n
  wp_start as #Hn
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  iunfold isNotifier at Hn
  icases Hn with ⟨%γ, #Hg⟩
  (try wp_auto)
  wp_apply chan.wp_make1 (V := Unit) as %ch' %γch' ⟨#Hch', %_, Hoc⟩
  imod alloc_broadcast_chan (E := ⊤) (iprop(True) : IProp GF) γch' ch' $$ Hch' Hoc with Hbc'
  icases ownBroadcastChan_open _ _ _ _ $$ Hbc' with ⟨%γi', #Hint', Hpend'⟩
  (try wp_auto)
  wp_apply +noauto sync.RWMutex.wp_Lock_guard $$ [$Hg] as ⟨Hlk, HP⟩
  wp_auto_lc 1
  imod lc_fupd_elim_later (E := ⊤) $$ Hlc1 HP with HP
  iunfold notifyLockInv at HP
  iNamed HP
  (try wp_auto)
  imod ghostVar_update (NotifyCur.mk ch' γch' γi') γ c $$ Hcur with Hcur
  wp_apply sync.RWMutex.wp_Unlock_guard $$ [$Hlk Hcur Hch Hpend']
  · inext
    iunfold notifyLockInv
    iexists NotifyCur.mk ch' γch' γi'
    simp only [named]
    iframe
    iexact Hint'
  (try wp_auto)
  ihave Hpb := ownBroadcastChan_close c.ch c.γch _ Broadcast.Pending c.γi $$ [Hpend]
  · iframe #; iexact Hpend
  wp_apply wp_broadcast_chan_close c.ch c.γch _ $$ [$Hpb] as -
  · imodintro; itrivial
  (try wp_auto)
  iapply HΦ
  itrivial

end proof

end EtcdGrove
end Perennial
