/-
Proof of `Spec/go_etcd_io/etcd/client/v3/leasing/leaseCache__Lock.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.leasing.leaseCache__Lock
public import Proof.go_etcd_io.etcd.client.v3.leasing.InvLeaseCacheWrite

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

theorem leaseCache.Lock.wp_proof : leaseCache.Lock.spec (GF := GF) (hG := hG) := by
  intro lc γ pfx X Qr key
  wp_start as ⟨#Hlc, #Hpeek, #Hstep⟩
  wp_apply wp_with_defer as %defer defer
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  unfold isLeaseCache
  icases Hlc with ⟨#Hguard, #Hcl⟩
  wp_apply sync.RWMutex.wp_Lock_guard $$ [$Hguard] as ⟨Hwl, HP⟩
  icases leaseCacheInv_open_w $$ HP with ⟨%st, Hown, HX, Hinst, Hready, #Hfacts, %Hwf, Hclose⟩
  unfold lcPeek
  icases Hpeek $$ %st %_ HX with ⟨HX, #HQr⟩
  icases lcOwn_emap_acc $$ Hown with ⟨Hentries, Hemap, Hown⟩
  wp_auto
  wp_apply wp_emap_lookup st key _ Hwf $$ [$Hemap] as Hemap
  ihave Hown := Hown $$ Hentries Hemap
  cases hk : st.entries !! key with
  | none =>
    simp only [Option.map_none, Option.getD_none]
    wp_auto
    imod Hclose $$ %st %Hwf [] Hinst Hready Hown HX with HP
    · iexact Hfacts
    wp_apply sync.RWMutex.wp_Unlock_guard $$ [$Hwl $HP]
    iapply HΦ
    iexists st
    simp only [entryFactsAt, LeaseCacheSt.revOf, hk]
    iframe #
    isplitr
    · ipureintro; rfl
    ileft; ipureintro; exact ⟨trivial, rfl⟩
  | some e =>
    have hli : e.li ≠ null := Hwf.li_ne key e hk
    simp only [Option.map_some, Option.getD_some]
    rw [decide_eq_false hli]
    wp_auto
    wp_apply chan.wp_make1 (V := Unit) as %ch %γch ⟨#Hch, %_, Hoc⟩
    imod alloc_broadcast_chan waitQ γch ch $$ Hch Hoc with Hpend
    icases pending_unknown $$ Hpend with ⟨Hpend, #Hunk⟩
    icases lcOwn_entry_acc lc st _ key e hk $$ Hown with ⟨He, Hown⟩
    unfold entryOwn
    icases He with ⟨%-, Hr, Hrev, Hwc, Hresp, #Hw⟩
    wp_auto
    have hresp : respOwn (GF := GF) { e with waitc := ch } (DFrac.own 1) = respOwn e (DFrac.own 1) :=
      rfl
    ihave Hown := Hown $$ %{ e with waitc := ch } %rfl [Hr Hrev Hwc Hresp]
    · simp only [hresp]
      iframe
      isplitl
      · ipureintro; exact hli
      unfold waitcOk; iexists γch; iexact Hunk
    have hst : st.setWaitc key ch =
        { st with entries := GMap.insert key { e with waitc := ch } st.entries } := by
      simp [LeaseCacheSt.setWaitc, hk]
    have hwo := waitcOnly_setWaitc st key ch
    rw [hst] at hwo
    unfold lcWaitcStep
    imod Hstep $$ %st %_ %hwo HX with HX
    have hwf' := wf_sameLis Hwf (sameLis_insert st key e { e with waitc := ch } hk rfl) rfl rfl rfl
    ihave #Hfacts' := lcFacts_same pfx st _ (sameFacts_insert st key e { e with waitc := ch } hk rfl rfl rfl) $$ Hfacts
    ihave Hready : monoNatAuthOwn γ.ready 1
        ({ st with entries := GMap.insert key { e with waitc := ch } st.entries } :
          LeaseCacheSt).readyN $$ [Hready]
    · rw [show ({ st with entries := GMap.insert key { e with waitc := ch } st.entries } :
          LeaseCacheSt).readyN = st.readyN from rfl]
      iexact Hready
    ihave Hinst : monoListAuthOwn γ.inst 1
        ({ st with entries := GMap.insert key { e with waitc := ch } st.entries } :
          LeaseCacheSt).installed $$ [Hinst]
    · rw [show ({ st with entries := GMap.insert key { e with waitc := ch } st.entries } :
          LeaseCacheSt).installed = st.installed from rfl]
      iexact Hinst
    imod Hclose $$ %_ %hwf' Hfacts' Hinst Hready Hown HX with HP
    wp_apply sync.RWMutex.wp_Unlock_guard $$ [$Hwl $HP]
    iapply HΦ
    iexists st
    simp only [entryFactsAt, LeaseCacheSt.revOf, hk]
    iframe #
    isplitr
    · ipureintro; rfl
    isplitr
    · unfold lcFacts
      icases Hfacts with ⟨#Hf, -⟩
      iapply (BigSepM.bigSepM_lookup hk) $$ Hf
    iright
    isplitr
    · ipureintro; rfl
    unfold waitcClose; iexists γch; iexact Hpend

end proof

end leasing
end EtcdGrove
end Perennial
