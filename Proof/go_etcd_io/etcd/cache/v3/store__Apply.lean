/-
Proof of `Spec/store__Apply.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.cache.v3.store__Apply
public import Spec.go_etcd_io.etcd.cache.v3.validateRevisions
public import Spec.go_etcd_io.etcd.client.v3.WatchResponse__IsProgressNotify
public import Spec.go_etcd_io.etcd.cache.v3.store__applyProgressNotifyLocked
public import Spec.go_etcd_io.etcd.cache.v3.store__applyEventsLocked

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.cache.v3 go_etcd_io.etcd.api.v3

/-! ## `applyResp`, by the code's branches -/

theorem Apply_progress {cap : Nat} {st : StoreState} {r : RespModel}
    (hc : r.canceled = false) (hv : validRevisions r st.latestRev = true)
    (hpn : r.isProgressNotify = true) (hinv : StoreInv cap st) (st' : StoreState)
    (hst' : st' = if st.latestRev = W64 0 then st else { st with latestRev := r.hdrRev }) :
    applyResp cap st r = (st', true) ∧ StoreInv cap st' ∧
      sint.Z st.latestRev ≤ sint.Z st'.latestRev := by
  have hle : sint.Z st.latestRev ≤ sint.Z r.hdrRev := by
    simp only [validRevisions, hpn, ↓reduceIte, Bool.not_eq_true', decide_eq_false_iff_not] at hv
    omega
  refine ⟨by simp [applyResp, hc, hv, hpn, hst'], ?_, ?_⟩
  · subst hst'
    split
    · exact hinv
    · exact { cap_pos := hinv.cap_pos, cap_le := hinv.cap_le
              rev_nonneg := by have := hinv.rev_nonneg; simp only; omega
              latest_sorted := hinv.latest_sorted, hist_len := hinv.hist_len
              hist_sorted := hinv.hist_sorted
              hist_le := fun h hh => by have := hinv.hist_le h hh; simp only; omega
              hist_maps_sorted := hinv.hist_maps_sorted }
  · subst hst'
    split
    · exact Int.le_refl _
    · exact hle

theorem Apply_events {cap : Nat} {st : StoreState} {r : RespModel}
    (hc : r.canceled = false) (hv : validRevisions r st.latestRev = true)
    (hpn : r.isProgressNotify = false) (hne : r.events ≠ []) :
    applyResp cap st r = applyEvents cap st r.events ∧
      ∀ e ∈ r.events, sint.Z st.latestRev < sint.Z e.rev := by
  have hne' : r.events.isEmpty = false := by simpa using hne
  refine ⟨by simp [applyResp, hc, hv, hpn, hne'], ?_⟩
  simp only [validRevisions, hpn, Bool.false_eq_true, ↓reduceIte, List.all_eq_true,
    decide_eq_true_eq] at hv
  exact hv

theorem Apply_empty {cap : Nat} {st : StoreState} {r : RespModel}
    (hc : r.canceled = false) (hv : validRevisions r st.latestRev = true)
    (hpn : r.isProgressNotify = false) (he : r.events = []) :
    applyResp cap st r = (st, true) := by
  simp [applyResp, hc, hv, hpn, he]

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

theorem store.Apply.wp_proof
    (wp_validateRevisions : validateRevisions.spec (GF := GF) (hG := hG))
    (wp_IsProgressNotify : WatchResponse.IsProgressNotify.spec (GF := GF) (hG := hG))
    (wp_applyProgressNotifyLocked : store.applyProgressNotifyLocked.spec (GF := GF) (hG := hG))
    (wp_applyEventsLocked : store.applyEventsLocked.spec (GF := GF) (hG := hG)) :
    store.Apply.spec (GF := GF) (hG := hG) := by
  intro s γ cap E st resp r
  wp_start as ⟨#Hs, Hw, #Hresp, %Hsorted, #Hcerts⟩
  wp_apply wp_with_defer as %defer defer
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  ihave #Hresp' := Hresp
  iunfold respAt at Hresp'
  icases Hresp' with ⟨#HevsAt, #Hhdr, % ⟨Hcomp, Hcanc, Hcre⟩⟩
  unfold storeWriter
  icases Hw with ⟨Hgw, Hmu, Htr, #Hlbw, %Hinv⟩
  iunfold storeRevLb at Hlbw
  rw [Hcanc]
  cases hc : r.canceled
  · wp_auto
    wp_apply sync.RWMutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, HP⟩
    iunfold storeLockInv at HP
    iNamed HP
    icombine Hst Hgw gives % ⟨_, Heq⟩
    subst Heq
    wp_auto
    wp_apply wp_validateRevisions resp r st.latestRev $$ [] as %verr %Hval
    · iexact Hresp
    ihave #Hlb0 := monoNatLbOwn_get $$ Hrev
    cases hv : validRevisions r st.latestRev
    · -- `validateRevisions` failed: nothing changes
      simp only [hv, Bool.false_eq_true, ↓reduceIte] at Hval
      obtain ⟨e, rfl⟩ := Hval
      wp_auto
      wp_apply sync.RWMutex.wp_Unlock $$ [$Hlocked Hst Hrev HlatestRev Hhist] as Hmu
      · iunfold storeLockInv; iexists st; simp only [named]; iframe; ipureintro; exact Hinv
      have Happ : applyResp cap st r = (st, false) := by simp [applyResp, hc, hv]
      iapply HΦ
      rw [Happ]
      dsimp only
      iunfold storeRevLb
      iframe
      iframe Hlb0
      ipureintro; exact ⟨Hinv, ⟨e, rfl⟩⟩
    · simp only [hv, ↓reduceIte] at Hval
      subst Hval
      wp_auto
      wp_apply wp_IsProgressNotify resp_ptr resp r (DFrac.own 1) $$ [resp] as resp
      · iframe resp; iexact Hresp
      cases hpn : r.isProgressNotify
      · -- not a progress notification
        ihave #HevsAt' := HevsAt
        iunfold eventsAt at HevsAt'
        icases HevsAt' with ⟨%ls, #Hls, %Hlslen, #-⟩
        ihave %Hsllen := ownSlice_len _ _ _ $$ Hls
        wp_auto
        by_cases he : r.events = []
        · -- no events: nothing changes
          have Hlen0 : resp.Events'.len = W64 0 := by
            have h0 : ls.length = 0 := by rw [Hlslen, he]; rfl
            have h1 := Hsllen.1; have h2 := Hsllen.2
            word
          simp only [Hlen0, _root_.decide_true, Bool.not_true, Bool.true_eq_false, _root_.decide_false]
          wp_auto
          wp_apply sync.RWMutex.wp_Unlock $$ [$Hlocked Hst Hrev HlatestRev Hhist] as Hmu
          · iunfold storeLockInv; iexists st; simp only [named]; iframe; ipureintro; exact Hinv
          have Happ := Apply_empty (cap := cap) hc hv hpn he
          iapply HΦ
          rw [Happ]
          dsimp only
          isplitl [Hgw Hmu Htr]
          · iunfold storeRevLb; iframe; iframe #; ipureintro; exact Hinv
          iunfold storeRevLb
          iframe Hlb0
          ipureintro; rfl
        · -- events: `applyEventsLocked`
          have Hlen0 : resp.Events'.len ≠ W64 0 := by
            intro h; apply he
            apply List.eq_nil_of_length_eq_zero
            have h1 := Hsllen.1
            rw [h] at h1
            have : sint.nat (W64 0) = 0 := by word
            omega
          simp only [Hlen0, _root_.decide_false, Bool.not_false, _root_.decide_true]
          wp_auto
          obtain ⟨Happ, Habove⟩ := Apply_events (cap := cap) hc hv hpn he
          have Hsnaps : applyRespSnaps st r = applyEventsSnaps st.latest r.events := by
            simp [applyRespSnaps, hc, hv, hpn, he]
          rw [Hsnaps] at *
          wp_apply wp_applyEventsLocked s γ cap E st resp.Events' r.events
            $$ [HlatestRev Hhist Htr] as %err ⟨Hphys, % ⟨Hinv', Hmono'⟩, %Herr⟩
          · iunfold storeLockedPhys; iframe; iframe Hs HevsAt Hcerts; ipureintro
            exact ⟨Hinv, Hsorted, Habove⟩
          generalize applyEvents cap st r.events = res at Happ Hinv' Hmono' Herr ⊢
          obtain ⟨st', ok⟩ := res
          dsimp only at Hinv' Hmono' Herr
          iunfold storeLockedPhys at Hphys
          icases Hphys with ⟨HlatestRev, Hhist, Htr⟩
          have Hle : sint.nat st.latestRev ≤ sint.nat st'.latestRev := by
            first | exact Int.toNat_le_toNat Hmono' | word
          imod ghostVar_update_halves st' γ.state st st $$ Hst Hgw with ⟨Hst, Hgw⟩
          imod mono_nat_own_update (sint.nat st'.latestRev) Hle $$ Hrev with ⟨Hrev, #Hlb⟩
          wp_apply sync.RWMutex.wp_Unlock $$ [$Hlocked Hst Hrev HlatestRev Hhist] as Hmu
          · iunfold storeLockInv; iexists st'; simp only [named]; iframe; ipureintro; exact Hinv'
          iapply HΦ
          rw [Happ]
          dsimp only
          isplitl [Hgw Hmu Htr]
          · iunfold storeRevLb; iframe; iframe #; ipureintro; exact Hinv'
          iunfold storeRevLb
          iframe Hlb
          ipureintro; exact Herr
      · -- a progress notification
        simp only [_root_.decide_true]
        have hhr : r.hdrRev ≠ W64 0 := by
          simp only [RespModel.isProgressNotify, Bool.and_eq_true, Bool.not_eq_true',
            decide_eq_false_iff_not] at hpn
          exact hpn.2
        iunfold hdrAt at Hhdr
        icases Hhdr with (%Hnil | ⟨%Hnn, #Hh⟩)
        · exact absurd Hnil.2 hhr
        wp_auto
        wp_apply wp_applyProgressNotifyLocked s γ cap st.latestRev r.hdrRev $$ [HlatestRev]
          as HlatestRev
        · iframe HlatestRev; iexact Hs
        obtain ⟨Happ, Hinv', Hmono'⟩ := Apply_progress hc hv hpn Hinv
          (if st.latestRev = W64 0 then st else { st with latestRev := r.hdrRev }) rfl
        have Hlr : (if st.latestRev = W64 0 then st.latestRev else r.hdrRev) =
            (if st.latestRev = W64 0 then st else { st with latestRev := r.hdrRev }).latestRev := by
          split <;> rfl
        have Hhs : (if st.latestRev = W64 0 then st
            else { st with latestRev := r.hdrRev }).history = st.history := by split <;> rfl
        have Hlt : (if st.latestRev = W64 0 then st
            else { st with latestRev := r.hdrRev }).latest = st.latest := by split <;> rfl
        rw [Hlr]
        generalize (if st.latestRev = W64 0 then st else { st with latestRev := r.hdrRev }) = st'
          at Happ Hinv' Hmono' Hhs Hlt
        rw [← Hhs]
        have Hle : sint.nat st.latestRev ≤ sint.nat st'.latestRev := by
          first | exact Int.toNat_le_toNat Hmono' | word
        imod ghostVar_update_halves st' γ.state st st $$ Hst Hgw with ⟨Hst, Hgw⟩
        imod mono_nat_own_update (sint.nat st'.latestRev) Hle $$ Hrev with ⟨Hrev, #Hlb⟩
        wp_apply sync.RWMutex.wp_Unlock $$ [$Hlocked Hst Hrev HlatestRev Hhist] as Hmu
        · iunfold storeLockInv; iexists st'; simp only [named]; iframe; ipureintro; exact Hinv'
        iapply HΦ
        rw [Happ]
        dsimp only
        rw [Hlt]
        isplitl [Hgw Hmu Htr]
        · iunfold storeRevLb; iframe; iframe #; ipureintro; exact Hinv'
        iunfold storeRevLb
        iframe Hlb
        ipureintro; rfl
  · -- canceled: `errors.New("canceled")`, nothing changes
    wp_auto
    wp_apply errors.wp_New as %e -
    have Happ : applyResp cap st r = (st, false) := by simp [applyResp, hc]
    iapply HΦ
    rw [Happ]
    dsimp only
    isplitl [Hgw Hmu Htr]
    · iunfold storeRevLb; iframe; iframe #; ipureintro; exact Hinv
    isplitl []
    · iunfold storeRevLb; iexact Hlbw
    ipureintro; exact ⟨e, rfl⟩

end proof

end EtcdGrove
end Perennial
