/-
Proof of the spec of the same name: `WatchStream.Watch.contract` at `*watchStream` (stage 2 of the
mvcc API, 2026-11-05). Lean-first (no Rocq counterpart).

The empty range returns the update untouched. Under the stream's lock, a closed stream fires the
update with no event (the client's state closed, `-1`); an open one picks the first free id from
`nextID` and registers the watcher with the store, whose registration callback (built from the
update, `Api/StreamHandle.watch_regCb`) fires the update at the registration, with the store's
state in hand and the stream's history open. The store's reader slot and the registration's watch
token come from the handle's pools (a thread token's loan, a time receipt).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.watchStream__Watch
public import Spec.go_opentelemetry_io.otel.trace.SpanFromContext
public import Proof.ReceiptTactics
import all Spec.go_etcd_io.etcd.server.v3.storage.mvcc.Api
import all Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Api.StreamHandle

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc go_opentelemetry_io.otel

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

theorem mvcc.watchStream.Watch.wp_proof (hspan : trace.SpanFromContext.spec (GF := GF) (hG := hG)) :
    mvcc.watchStream.Watch.spec (GF := GF) (hG := hG) := by
  intro w γ ι ctx cd key endk fcs kk e fs startRev Q
  wp_start as ⟨Hws, Htt, Hrt, #Hctx, #Hk, #He, #Hfi, %Hsr, Hau⟩
  icases mvcc.api.isMvccWatchStream_open w γ ι $$ Hws with
    ⟨%γw, %γc, %s, %st, %γo, %γp, %hι, #Hinv, #Hws, #Htp, #Hrp, -⟩
  obtain ⟨hι, hγ⟩ := hι
  generalize hch : (ι : api.WsAbs).ch = ch at hι
  have hι' : ι = (mvcc.wsAbsOf γw ch γc : api.WsAbs) := hι
  subst hι'
  have hγ' : γ = (γw.st : api.MvccName) := hγ.symm
  subst hγ'
  iunfold mvcc.isWatchStreamAt at Hws
  iNamed Hws
  ihave Hmi : (mvccInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hmi with ⟨-, -, -, -, -, -, -, -, -, -, -, -, ⟨%eer, #Heer⟩, ⟨%edu, #Hedu⟩, -⟩
  ihave Hwable2 := Hwable
  iunfold mvcc.isWatchable at Hwable2
  icases Hwable2 with ⟨%wi, %hwa, #Hwatch, #Hprog, #HprogAll, #Hrev⟩
  wp_auto
  wp_apply wp_with_defer as %defer defer
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  ihave %Helen := ownSlice_len $$ He
  by_cases hlen : endk.len = W64 0
  -- the single-key case: no comparison
  have hne0 : e = [] := by
    have h := Helen.1
    rw [hlen] at h
    exact List.eq_nil_of_length_eq_zero (by rw [h]; rfl)
  rw [decide_eq_true hlen]
  wp_auto
  rotate_left
  rw [decide_eq_false hlen]
  wp_auto
  wp_apply bytes.wp_Compare key endk DFrac.discard DFrac.discard kk e $$ [$Hk $He] as ⟨-, -⟩
  wp_if_destruct
  -- `key < end`: on to the lock
  have hne : e = [] ∨ go.GoStringLt kk e := by
    right
    unfold bytes.compareResult at Hif
    split at Hif
    · assumption
    · split at Hif <;> exact absurd Hif (by decide)
  rotate_left
  -- `key ≥ end`: the empty range, the update untouched
  iapply HΦ
  iframe Htt Hrt
  ileft
  iframe Heer Hau
  ipureintro
  have hl : ¬ endk.len = W64 0 := by intro h0; simp [h0] at hlen
  have hc : ¬ bytes.compareResult kk e = W64 (-1) := by intro h0; simp [h0] at Hif
  refine ⟨fun h => hl ?_, fun h => hc ?_, rfl⟩
  · have h1 := Helen.1; rw [h] at h1; have h2 := Helen.2; simp at h1; word
  · unfold bytes.compareResult; rw [if_pos h]
  -- the single-key case
  have hne : e = [] ∨ go.GoStringLt kk e := Or.inl hne0
  all_goals
    irename : (end_ptr ↦ endk : IProp GF) => Hendp
    wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, HR⟩
    iunfold mvcc.watchStreamInv at HR
    iNamed HR
    icases Hacl with ⟨%lm, %CS, Hm, Hcs, %Hrel⟩
    cases closed
    rotate_left
    -- closed: the update fired with no event
    wp_auto
    iapply fupd_wp
    imod mvcc.api.watch_fire_closed γw ch γc kk e endk startRev fs Q nextID CM CS lm Hrel
      $$ [$Hm $Hau] with ⟨Hm, %σ, %S, HQ, %HSc⟩
    imodintro
    wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked HnextID Hclosed Hcf Hwf Hcm Hwm Hids Hm Hcs Hcl]
    · inext
      iunfold mvcc.watchStreamInv
      iexists nextID, true, cm, wm, CM, WM
      simp only [named]
      iframe HnextID Hclosed Hcf Hwf Hcm Hwm Hids
      iframe #
      isplitr
      · ipureintro; exact Hdom
      isplitr
      · ipureintro; exact Hnn
      isplitl [Hm Hcs]
      · iexists lm, CS
        iframe Hm Hcs
        ipureintro; exact Hrel
      iexact Hcl
    iapply HΦ
    iframe Htt Hrt
    iright
    isplitr
    · ipureintro; exact hne
    iexists σ, S
    iframe HQ
    rw [HSc]
    simp only [↓reduceIte]
    iexact Heer
    -- open
    simp only [Bool.false_eq_true, ↓reduceIte]
    icases Hcl with ⟨%L, HCR, #HL, %Hcnt⟩
    iunfold mvcc.idsInv at Hids
    icases Hids with ⟨%IDS, Hida, Hidf, %Hidb⟩
    wp_auto_lc 1
    -- the store's reader slot, from the handle's pool (given back after the registration)
    iapply fupd_wp
    ihave Hrt : ownToks (GF := GF) γw.st.tk 1 $$ [Hrt]
    · iunfold mvcc.api.mvccReaders at Hrt; (try rw [hγ]); iexact Hrt
    imod mvcc.watchReader_lend s st γw γp $$ [$Hlc1 $Hrp $Htt $Hrt] with ⟨HPR, Hloan⟩
    imodintro
    -- `AutoWatchID`: the first free id from `nextID`
    ihave IH : iprop(∃ n : w64, "HnextID" ∷ w.[watchStream, go!"nextID"] ↦ n ∗
        "Hwm" ∷ wm ↦$ WM ∗
        "%Hn" ∷ ⌜sint.Z nextID ≤ sint.Z n ∧ sint.Z n + mvcc.aboveCnt n WM ≤ L.length⌝)
        $$ [HnextID Hwm]
    · iexists nextID
      iframe
      ipureintro; exact ⟨Int.le_refl _, Hcnt.1⟩
    wp_for IH
    wp_apply wp_map_lookup1 $$ [$Hwm] as Hwm
    wp_if_destruct
    · have hsome : ∃ w0, WM !! n = some w0 := by
        cases h : WM !! n with
        | none =>
          exfalso
          have hz : (zero_val Loc) = null := rfl
          rw [h] at Hif
          simp [hz] at Hif
          have := go.intoVal_inj Hif
          cases this
        | some w0 => exact ⟨w0, rfl⟩
      obtain ⟨w0, hw0⟩ := hsome
      have hpos : 1 ≤ mvcc.aboveCnt n WM := by
        rw [mvcc.aboveCnt_skip n w0 WM hw0 (by omega)]; omega
      have hsk := mvcc.aboveCnt_skip n w0 WM hw0 (by omega)
      have hs1 : sint.Z (n + W64 1) = sint.Z n + 1 := by word
      wp_for_post
      iframe
      iexists _
      iframe
      ipureintro
      constructor <;> omega
    have hfree : (WM !! n).getD (zero_val Loc) = null := by
      exact Classical.byContradiction fun h => Hif (by simp [h])
    have hnone : WM !! n = none := by
      cases h : WM !! n with
      | none => rfl
      | some w => simp only [h, Option.getD_some] at hfree; exact absurd hfree (Hnn n w h)
    have hnb : sint.Z n < 2 ^ 63 - 1 := by omega
    have hs1 : sint.Z (n + W64 1) = sint.Z n + 1 := by word
    have hIDS : ∀ i, (IDS !! i).isSome → 0 ≤ sint.Z i ∧ sint.Z i < sint.Z n := fun i hi => by
      have := Hidb.2 i hi; omega
    have hcntF : ∀ w : Loc, sint.Z (n + W64 1) + mvcc.aboveCnt (n + W64 1) (<[n := w]> WM) ≤
        L.length + 1 := fun w => by
      have := mvcc.aboveCnt_assign n w WM hnb
      rw [hs1]; omega
    rw [ite_eq_left (by simp [hfree])]
    -- the registration's watch token: a receipt of the step resolving `watch`
    wp_take_receipt as Hrc
    -- the id chosen: named `id` as in the other case (the parameter is `AutoWatchID` here)
    generalize n = id at hnone hcntF hIDS hnb hs1 Hn ⊢
    all_goals
      have hid0 : 0 ≤ sint.Z id := by omega
      have hidm : id ≠ W64 (-1) := by intro h; rw [h] at hid0; revert hid0; decide
      -- the registration callback, from the update
      ihave Hreg := mvcc.api.watch_regCb γw ch γc γo kk e endk startRev id fs Q nextID CM CS lm IDS
        Hγc.1 Hrel hid0 Hn.1 hnb hIDS $$ [$Hm $Hida $Hidf $Hau]
      have hwi : wi = ⟨go.GoType.PointerType watchableStore.ty, #s⟩ := by
        simp only [interface.mkOk, GoInterface.ok.injEq] at hwa; exact hwa.symm
      subst hwi
      iapply fupd_wp
      imod mvcc.watchTokPool_take γw $$ Htp Hrc with HPT
      imodintro
      wp_apply Hwatch $$ [HCR HPR HPT Hreg] as %w' %c
        ⟨%hwnn, #HIW, #HOC, #Hcspec, HCR, HPR, ⟨%lo, #HIWF⟩, %Hbnd, #HWS, HBack⟩
      · simp only [mvcc.storeWatchParams]
        iframe HCR HPR HPT Hreg
        iframe #
        ipureintro; exact ⟨Hsr, hidm⟩
      iapply fupd_wp
      imod Hloan $$ HPR with ⟨Htt, Hrt⟩
      ihave Hrt : mvcc.api.mvccReaders (GF := GF) γw.st 1 $$ [Hrt]
      · iunfold mvcc.api.mvccReaders; (try rw [← hγ]); iexact Hrt
      imodintro
      iunfold mvcc.api.watchBack at HBack
      icases HBack with ⟨⟨%σ, %S, HQ, %HSc⟩, Hids, %lm', Hm, %Hrep⟩
      wp_auto
      wp_apply hspan $$ [$Hctx] as %sp #Hsp
      iunfold trace.isSpan at Hsp
      icases Hsp with ⟨%si, %hsi, #HEnd, -⟩
      subst hsi
      ipersist c
      ipersist span
      wp_apply wp_mapInsert $$ [$Hcm] as Hcm
      wp_apply wp_mapInsert $$ [$Hwm] as Hwm
      wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked HnextID Hclosed Hcf Hwf Hcm Hwm Hids HCR Hm Hcs]
      · inext
        iunfold mvcc.watchStreamInv
        iexists _, false, cm, wm, _, _
        simp only [named, Bool.false_eq_true, ↓reduceIte]
        iframe HnextID Hclosed Hcf Hwf Hcm Hwm Hids
        isplitr
        · ipureintro
          intro i
          simp only [GMap.lookup_insert_eq_iff]
          split
          · rfl
          · exact Hdom i
        isplitr
        · ipureintro
          intro i w0 h
          simp only [GMap.lookup_insert_eq_iff] at h
          split at h
          · cases h; exact hwnn
          · exact Hnn i w0 h
        isplitr
        · imodintro
          iintro %i %w0 %h
          simp only [GMap.lookup_insert_eq_iff] at h
          split at h
          · cases h
            simp only [mvcc.storeWatchParams]
            iframe HIW HOC
            iexists _, _, lo
            iframe HIWF
            rename_i hii
            ipureintro; first | exact hii | exact hii.symm
          · iapply Hws $$ %i %w0 %h
        isplitr
        · imodintro
          iintro %i %c0 %w0 %h1 %h2
          by_cases hii : id = i
          · subst hii
            simp only [GMap.lookup_insert_eq_iff, ↓reduceIte, Option.some.injEq] at h1 h2
            subst h1 h2
            iunfold mvcc.cancelSpec at Hcspec
            unfold mvcc.cancelSpec
            imodintro
            imodintro
            iintro %Φ' - HΦ'
            wp_apply wp_with_defer as %defer2 Hdefer2
            wp_bind (App (Val #c) (Val #()))
            iapply Hcspec
            · itrivial
            inext
            iintro #Hwc
            wp_auto
            wp_bind (App (Val #(methods si.ty go!"End" si.v)) (Val #slice.nil))
            iapply HEnd $$ %slice.nil
            · itrivial
            inext
            iintro -
            wp_auto
            iapply HΦ' $$ Hwc
          · simp only [GMap.lookup_insert_eq_iff, hii, ↓reduceIte] at h1 h2
            iapply Hcs $$ %i %c0 %w0 %h1 %h2
        isplitl [Hm Hcs]
        · iexists lm', CS
          iframe Hm Hcs
          ipureintro
          intro d
          obtain ⟨wi, hwi, hr⟩ := Hrep d
          rw [hr]
          exact mvcc.wsRel_register (Hrel d) id _ wi hwi hid0 Hn.1 hnb
        iexists (w' :: L)
        simp only [mvcc.storeWatchParams]
        iframe HCR
        isplitr
        rotate_left
        · ipureintro
          refine ⟨?_, Hbnd⟩
          have := hcntF w'
          simp only [List.length_cons]
          exact this
        imodintro
        iintro %w0 %hin
        simp only [List.mem_cons] at hin
        rcases hin with rfl | hin
        · ileft
          iexists id
          ipureintro
          simp
        · icases HL $$ %w0 %hin with (⟨%i, %hi⟩ | #Hc0)
          · ileft
            iexists i
            ipureintro
            simp only [GMap.lookup_insert_eq_iff]
            split
            · rename_i hii; subst hii; rw [hnone] at hi; cases hi
            · exact hi
          · iright
            iexact Hc0
      iapply HΦ
      iframe Htt Hrt
      iright
      isplitr
      · ipureintro; exact hne
      iexists σ, S
      iframe HQ
      rw [HSc]
      simp only [Bool.false_eq_true, ↓reduceIte]
      first | (ipureintro; rfl) | itrivial | (ipureintro; trivial)

end proof

end EtcdGrove
end Perennial
