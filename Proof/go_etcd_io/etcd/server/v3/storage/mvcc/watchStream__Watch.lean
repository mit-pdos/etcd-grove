/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.watchStream__Watch
public import Spec.go_opentelemetry_io.otel.trace.SpanFromContext

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc go_opentelemetry_io.otel

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

theorem mvcc.watchStream.Watch.wp_proof (hspan : trace.SpanFromContext.spec (GF := GF) (hG := hG)) :
    mvcc.watchStream.Watch.spec (GF := GF) (hG := hG) := by
  intro ws wa P γ ctx cd id key endk fcs k e fs startRev sr
  wp_start as ⟨Hws, #Hctx, #Hk, #He, #Hfcs, #Hfs, HPR, HPT, %Hsr0, #Hsrp⟩
  obtain ⟨Hsr, Hid0⟩ := Hsr0
  iunfold mvcc.isWatchStream at Hws
  iNamed Hws
  ihave Hmi : (mvccInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hmi with ⟨-, -, -, -, -, -, -, -, -, -, -, -, ⟨%eer, #Heer⟩, ⟨%edu, #Hedu⟩, -⟩
  iunfold mvcc.isWatchable at Hwable
  icases Hwable with ⟨%wi, %hwa, #Hwatch, #Hprog, #HprogAll, #Hrev⟩
  subst hwa
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
  wp_apply bytes.wp_Compare key endk DFrac.discard DFrac.discard k e $$ [$Hk $He] as ⟨-, -⟩
  wp_if_destruct
  -- `key < end`: on to the lock
  have hne : e = [] ∨ go.GoStringLt k e := by
    right
    unfold bytes.compareResult at Hif
    split at Hif
    · assumption
    · split at Hif <;> exact absurd Hif (by decide)
  rotate_left
  -- `key ≥ end`: the empty range
  iapply HΦ
  iframe HPR
  iright
  isplitr
  · ipureintro; rfl
  iexact Heer
  -- the single-key case
  have hne : e = [] ∨ go.GoStringLt k e := Or.inl hne0
  all_goals
    irename : (end_ptr ↦ endk : IProp GF) => Hendp
    wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, HR⟩
    iunfold mvcc.watchStreamInv at HR
    iNamed HR
    cases closed
    rotate_left
    -- closed: `ErrEmptyWatcherRange`
    wp_auto
    wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked HnextID Hclosed Hcf Hwf Hcm Hwm Hids Hcl]
    · inext
      iunfold mvcc.watchStreamInv
      iexists nextID, true, cm, wm, CM, WM
      simp only [named]
      iframe
      iframe #
      ipureintro; exact ⟨Hdom, Hnn⟩
    iapply HΦ
    iframe HPR
    iright
    isplitr
    · ipureintro; rfl
    iexact Heer
    -- open
    simp only [Bool.false_eq_true, ↓reduceIte]
    icases Hcl with ⟨%L, HCR, #HL, %Hcnt⟩
    iunfold mvcc.idsInv at Hids
    icases Hids with ⟨%IDS, Hida, Hidf, %Hidb⟩
    wp_auto
    wp_if_destruct
    -- `AutoWatchID`: the first free id from `nextID`
    ihave IH : iprop(∃ n : w64, "HnextID" ∷ ws.[watchStream, go!"nextID"] ↦ n ∗
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
    -- the id `n` was never assigned: every assigned id is below `nextID`
    have hstep : (W64 0 ≠ W64 0 ∧ 0 ≤ sint.Z (n + W64 1) ∧
          ∀ i, (IDS !! i).isSome → 0 ≤ sint.Z i ∧ sint.Z i < sint.Z (n + W64 1)) ∨
        (0 ≤ sint.Z n ∧ sint.Z n < sint.Z (n + W64 1) ∧
          ∀ i, (IDS !! i).isSome → 0 ≤ sint.Z i ∧ sint.Z i < sint.Z n) := by
      right
      refine ⟨by omega, by omega, fun i hi => ?_⟩
      have := Hidb.2 i hi; omega
    have hcntF : ∀ w : Loc, sint.Z (n + W64 1) + mvcc.aboveCnt (n + W64 1) (<[n := w]> WM) ≤
        L.length + 1 := fun w => by
      have := mvcc.aboveCnt_assign n w WM hnb
      rw [hs1]; omega
    rw [ite_eq_left (by simp [hfree])]
    wp_auto
    -- the id chosen: named `id` as in the other case (the parameter is `AutoWatchID` here)
    generalize n = id at hnone hcntF hstep ⊢
    rotate_left
    -- an explicit id: excluded (`id = 0`)
    exfalso; exact Hif Hid0
    all_goals
      -- the registration callback: the id recorded in the channel's id map at the registration
      ihave Hreg : iprop(∀ w : Loc, ⌜w ≠ null⌝ -∗ |==> (mvcc.chanIdAssigned γc id w ∗
          (mvcc.idsInv γ (id + W64 1) ∗ mvcc.idAssigned γ id w ∗ mvcc.idTok γ id)))
          $$ [Hida Hidf]
      · iintro %w0 -
        rcases hstep with ⟨h0, -⟩ | hstep
        · exact absurd rfl h0
        iapply mvcc.idsInv_assign γ γc Hγc.1 IDS _ id w0 hstep $$ [$Hida $Hidf]
      have hidm : id ≠ W64 (-1) := by
        rcases hstep with ⟨h0, -⟩ | ⟨h0, -⟩
        · exact absurd rfl h0
        · intro h; rw [h] at h0; revert h0; decide
      wp_apply Hwatch $$ [$HCR $HPR $HPT $Hreg $Hsrp] as %w %c
        ⟨%hwnn, #HIW, #HOC, #Hcspec, HCR, HPR, ⟨%lo, #HIWF⟩, %Hbnd, #HWS, ⟨Hids, #Hia, Hit⟩⟩
      · iframe #
        ipureintro; exact ⟨Hsr, hidm⟩
      wp_auto
      wp_apply hspan $$ [$Hctx] as %sp #Hsp
      iunfold trace.isSpan at Hsp
      icases Hsp with ⟨%si, %hsi, #HEnd, -⟩
      subst hsi
      ipersist c
      ipersist span
      wp_apply wp_mapInsert $$ [$Hcm] as Hcm
      wp_apply wp_mapInsert $$ [$Hwm] as Hwm
      wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked HnextID Hclosed Hcf Hwf Hcm Hwm Hids HCR]
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
            wp_bind (App (Val #(methods si.ty go!"End" si.v)) (Val #()))
            iapply HEnd
            · itrivial
            inext
            iintro -
            wp_auto
            iapply HΦ' $$ Hwc
          · simp only [GMap.lookup_insert_eq_iff, hii, ↓reduceIte] at h1 h2
            iapply Hcs $$ %i %c0 %w0 %h1 %h2
        iexists (w :: L)
        iframe HCR
        isplitr
        rotate_left
        · ipureintro
          refine ⟨?_, Hbnd⟩
          have := hcntF w
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
      iframe HPR
      ileft
      isplitr
      · ipureintro; rfl
      isplitr
      · ipureintro; exact hne
      iexists w, lo
      iframe HIW HIWF Hia Hit
      isplitr
      · iexists γc
        iframe HOC
        ipureintro; exact Hγc.2.2.2.2
      iexact HWS

end proof

end EtcdGrove
end Perennial
