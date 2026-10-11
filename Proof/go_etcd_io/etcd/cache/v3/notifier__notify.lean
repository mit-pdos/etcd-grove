/-
Proof of `Spec/notifier__notify.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.cache.v3.notifier__notify

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.cache.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

theorem notifier.notify.wp_proof : notifier.notify.spec (GF := GF) (hG := hG) := by
  intro n γ k0
  wp_start as ⟨Hh, #Hlb⟩
  wp_apply wp_with_defer as %defer defer
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  unfold notifierHandle
  wp_apply +noauto sync.RWMutex.wp_Lock $$ [$Hh] as ⟨Hlk, HP⟩
  wp_auto_lc 1
  imod lc_fupd_elim_later (E := ⊤) $$ Hlc1 HP with HP
  unfold notifierLockInv
  iNamed HP
  unfold notifierLb
  ihave %Hle := monoNatLbOwn_valid $$ Hauth Hlb
  wp_auto
  wp_apply chan.wp_make1 (V := Unit) as %ch' %γch' ⟨#Hch', %_, Hoc⟩
  imod mono_nat_own_update (c.k + 1) (by omega) $$ Hauth with ⟨Hauth, #Hlb1⟩
  imod alloc_broadcast_chan (E := ⊤) (notifierLb (GF := GF) γ (c.k + 1 + 1)) γch' ch' $$ Hch' Hoc
    with Hbc'
  icases ownBroadcastChan_open _ _ _ _ $$ Hbc' with ⟨%γi', #Hint', Hpend'⟩
  ihave Hpb := ownBroadcastChan_close c.ch c.γch _ Broadcast.Pending c.γi $$ [Hpend]
  · iframe #; iexact Hpend
  wp_apply wp_broadcast_chan_close c.ch c.γch _ $$ [$Hpb] as -
  · unfold notifierLb; imodintro; iexact Hlb1
  imod ghostVar_update (NotifierCur.mk ch' γch' γi' (c.k + 1)) γ.cur c $$ Hcur with Hcur
  wp_apply sync.RWMutex.wp_Unlock $$ [$Hlk Hcur Hch Hauth Hpend'] as Hh
  · inext
    iexists NotifierCur.mk ch' γch' γi' (c.k + 1)
    simp only [named]
    iframe
    unfold notifierLb
    iexact Hint'
  iapply HΦ
  iframe
  unfold notifierLb
  iapply monoNatLbOwn_le (k0 + 1) (by omega) $$ Hlb1

end proof

end EtcdGrove
end Perennial
