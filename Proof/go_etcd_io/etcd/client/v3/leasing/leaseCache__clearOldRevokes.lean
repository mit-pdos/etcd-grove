/-
Proof of `Spec/go_etcd_io/etcd/client/v3/leasing/leaseCache__clearOldRevokes.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.leasing.leaseCache__clearOldRevokes
public import Proof.go_etcd_io.etcd.client.v3.leasing.InvLeaseCacheWrite
public import Spec.time.Time__Add

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace leasing

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.client.v3.leasing go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.leasing.Assumptions]

theorem leaseCache.clearOldRevokes.wp_proof
    (hAdd : EtcdGrove.time.Time.Add.spec (GF := GF) (hG := hG)) :
    leaseCache.clearOldRevokes.spec (GF := GF) (hG := hG) := by
  intro lc γ pfx X ctx cs
  wp_start as ⟨#Hlc, #Hctx, #Hstep⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  unfold isLeaseCache
  icases Hlc with ⟨#Hguard, #Hcl⟩
  unfold context.isContext context.isContextDef
  iNamed Hctx
  wp_auto
  ipersist lc
  ipersist ctx
  wp_for
  wp_apply +noauto HDone as %ch1 %γ1 #Hdone
  wp_auto
  wp_apply +noauto time.wp_After as %tch %γt #Htch
  wp_auto_lc 2
  wp_apply_core chan.wp_select_blocking
  iapply BigAndL.bigAndL_cons.2
  isplit
  · simp only [chan.blockingClausePre]
    iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, ch1, γ1
    isplit
    · ipureintro; rfl
    isplit
    · iapply context.isContextDone_is_chan $$ Hdone
    iapply context.isContextDone_receive _ _ _ _ $$ Hdone
    iintro -
    wp_auto
    wp_for_post
    iapply HΦ
    itrivial
  iapply BigAndL.bigAndL_cons.2
  isplit
  · simp only [chan.blockingClausePre]
    iexists time.Time, inferInstance, inferInstance, inferInstance, inferInstance, tch, γt
    isplitr
    · ipureintro; rfl
    isplitr
    · iapply is_bag_is_chan $$ Htch
    iapply bag_recv_au $$ [$Hlc1 $Hlc2] Htch
    inext
    iintro %tm -
    wp_auto
    wp_apply sync.RWMutex.wp_Lock_guard $$ [$Hguard] as ⟨Hwl, HP⟩
    icases leaseCacheInv_open_w $$ HP with ⟨%st, Hown, HX, Hinst, Hready, #Hfacts, %Hwf, Hclose⟩
    icases lcOwn_emap_revokes_acc $$ Hown with ⟨Hentries, Hemap, Hrv, Hrmap, Hown⟩
    wp_auto
    wp_func_lits
    wp_bind (App (App (Val (map.forRange _ _)) _) _)
    iapply wp_map_for_range_mut (fun (i : Nat) (m' : GMap GoString time.Time) =>
        iprop(∃ (t0 : time.Time) (kv : GoString),
        "Hrv" ∷ structFieldRef leaseCache go!"revokes" lc ↦ st.rmap ∗
        "lr" ∷ lr_ptr ↦ t0 ∗ "k" ∷ k_ptr ↦ kv ∗ "%Hsub" ∷ ⌜RevokesSub m' st.revokes⌝))
      _ _ _ st.rmap st.revokes $$ Hrmap
    iintro %keys ⟨%Hkset, %Hklen, %Hknodup⟩
    isplitl [Hrv lr k]
    · iexists _, _
      simp only [named]
      iframe
      ipureintro; intro k t h; exact h
    isplitr
    · imodintro
      iintro %i %key %v %m' ⟨%Hki, %Hmv, %Hagree⟩ HP Hm
      iNamed HP
      wp_auto
      wp_apply hAdd $$ [$lr] as %t1 lr
      wp_apply time.wp_Since as %d -
      wp_if_destruct
      · wp_apply wp_mapDelete $$ [$Hm] as Hm
        unfold forMapPostcondition
        iright; ileft
        isplitr
        · ipureintro; rfl
        iexists _
        iframe Hm
        isplitl
        · iexists v, key
          simp only [named]
          iframe
          ipureintro
          intro k t h
          rw [ldel] at h
          exact Hsub k t h.2
        ipureintro
        intro k hk
        rw [GMap.lookup_delete_ne _ (Ne.symm hk)]
      · unfold forMapPostcondition
        iright; ileft
        isplitr
        · ipureintro; rfl
        iexists m'
        iframe Hm
        isplitl
        · iexists v, key
          simp only [named]
          iframe
          ipureintro; exact Hsub
        ipureintro; intro k _; rfl
    iintro %m' HP Hm
    iNamed HP
    wp_auto
    ihave Hown := Hown $$ %m' Hentries Hemap Hrv Hm
    imod Hstep $$ %st %m' %Hsub HX with HX
    have hwf' : LeaseCacheWf { st with revokes := m' } :=
      ⟨Hwf.li_inj, Hwf.li_not_frozen, Hwf.installed, Hwf.entries_installed, Hwf.li_ne,
        Hwf.empty_if_nil⟩
    ihave #Hfacts' := lcFacts_same pfx st ({ st with revokes := m' } : LeaseCacheSt)
      ⟨fun k e' h => ⟨e', h, rfl, rfl, rfl⟩, fun f hf => Or.inl hf⟩ $$ Hfacts
    ihave Hready : monoNatAuthOwn γ.ready 1 ({ st with revokes := m' } : LeaseCacheSt).readyN
      $$ [Hready]
    · rw [show ({ st with revokes := m' } : LeaseCacheSt).readyN = st.readyN from rfl]
      iexact Hready
    ihave Hinst : monoListAuthOwn γ.inst 1 ({ st with revokes := m' } : LeaseCacheSt).installed
      $$ [Hinst]
    · rw [show ({ st with revokes := m' } : LeaseCacheSt).installed = st.installed from rfl]
      iexact Hinst
    imod Hclose $$ %_ %hwf' Hfacts' Hinst Hready Hown HX with HP
    wp_apply sync.RWMutex.wp_Unlock_guard $$ [$Hwl $HP]
    wp_for_post
    iframe
  iapply BigAndL.bigAndL_nil.2
  itrivial

end proof

end leasing
end EtcdGrove
end Perennial
