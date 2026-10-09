/-
Proof of `Spec/ready__Reset.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.cache.v3.ready__Reset

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.cache.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

theorem ready.Reset.wp_proof : ready.Reset.spec (GF := GF) (hG := hG) := by
  intro r γ e0
  wp_start as ⟨#Hr, #Hlb⟩
  wp_apply wp_with_defer as %defer defer
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  unfold isReady
  wp_apply sync.Mutex.wp_Lock $$ [$Hr] as ⟨Hlocked, Hinv⟩
  unfold readyLockInv
  iNamed Hinv
  unfold readyEpochLb
  ihave %Hle := monoNatLbOwn_valid $$ Hauth Hlb
  wp_auto
  cases b
  · -- already not ready
    wp_auto
    ihave #Hlb' := monoNatLbOwn_get $$ Hauth
    wp_apply sync.Mutex.wp_Unlock $$ [$Hr $Hlocked HisReady HstateCh Hch Hauth]
    · inext; iexists false, ch, γch, e; simp only [named]; iframe; ipureintro; exact Hb
    iapply HΦ
    unfold readySeen readyEpochLb
    iexists e
    iframe Hlb'
    ipureintro; exact ⟨Hle.2, Hb.symm⟩
  · -- ready: flip, broadcast on the old channel, install a fresh one
    wp_auto
    imod mono_nat_own_update (e + 1) (by omega) $$ Hauth with ⟨Hauth, #Hlb1⟩
    wp_apply wp_broadcast_chan_close ch γch _ $$ [$Hch] as -
    · imodintro; iexact Hlb1
    wp_apply chan.wp_make1 (V := Unit) as %ch' %γch' ⟨#Hch', %_, Hoc⟩
    imod alloc_broadcast_chan (E := ⊤) (monoNatLbOwn (GF := GF) γ.epoch (e + 1 + 1)) γch' ch'
      $$ Hch' Hoc with Hbc
    wp_apply sync.Mutex.wp_Unlock $$ [$Hr $Hlocked HisReady HstateCh Hbc Hauth]
    · inext; iexists false, ch', γch', e + 1; simp only [named]; iframe
      ipureintro; rw [readyParity_succ, ← Hb]; rfl
    iapply HΦ
    unfold readySeen readyEpochLb
    iexists e + 1
    iframe Hlb1
    ipureintro; refine ⟨by omega, ?_⟩; rw [readyParity_succ, ← Hb]; rfl

end proof

end EtcdGrove
end Perennial
