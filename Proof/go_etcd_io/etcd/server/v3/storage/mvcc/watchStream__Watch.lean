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
  intro ws wa P γ ctx cd id key endk fcs k e fs startRev
  wp_start as ⟨Hws, #Hctx, #Hk, #He, #Hfcs, #Hfs, HPR, %Hsr⟩
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
  ileft
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
    wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked HnextID Hclosed Hcf Hwf Hcm Hwm Hcl]
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
    ileft
    iexact Heer
    -- open
    simp only [Bool.false_eq_true, ↓reduceIte]
    icases Hcl with ⟨%L, HCR, #HL⟩
    wp_auto
    wp_if_destruct
    -- `AutoWatchID`: the first free id from `nextID`
    ihave IH : iprop(∃ n : w64, "HnextID" ∷ ws.[watchStream, go!"nextID"] ↦ n ∗
        "Hwm" ∷ wm ↦$ WM) $$ [HnextID Hwm]
    · iexists nextID
      iframe
    wp_for IH
    wp_apply wp_map_lookup1 $$ [$Hwm] as Hwm
    wp_if_destruct
    · wp_for_post
      iframe
      iexists _
      iframe
    have hfree : (WM !! n).getD (zero_val Loc) = null := by
      exact Classical.byContradiction fun h => Hif (by simp [h])
    have hnone : WM !! n = none := by
      cases h : WM !! n with
      | none => rfl
      | some w => simp only [h, Option.getD_some] at hfree; exact absurd hfree (Hnn n w h)
    rw [ite_eq_left (by simp [hfree])]
    wp_auto
    -- the id chosen: named `id` as in the other case (the parameter is `AutoWatchID` here)
    generalize n = id at hnone ⊢
    rotate_left
    -- an explicit id: refused if in use
    wp_apply wp_map_lookup2 $$ [$Hwm] as Hwm
    cases hnone : WM !! id
    rotate_left
    -- in use: `ErrWatcherDuplicateID`
    simp only [Option.isSome_some]
    wp_auto
    wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked HnextID Hclosed Hcf Hwf Hcm Hwm HCR]
    · inext
      iunfold mvcc.watchStreamInv
      iexists nextID, false, cm, wm, CM, WM
      simp only [named, Bool.false_eq_true, ↓reduceIte]
      iframe
      iframe #
      isplitr
      · ipureintro; exact Hdom
      ipureintro; exact Hnn
    iapply HΦ
    iframe HPR
    iright
    isplitr
    · ipureintro; rfl
    iright
    isplitr
    · ipureintro; exact Hif
    iexact Hedu
    -- free: on to the watch, as `AutoWatchID`
    rotate_left
    simp only [Option.isSome_none]
    wp_auto
    all_goals
      wp_apply Hwatch $$ [$HCR $HPR] as %w %c ⟨%hwnn, #HIW, #Hcspec, HCR, HPR⟩
      · iframe #
        try (ipureintro; exact Hsr)
      wp_apply hspan $$ [$Hctx] as %sp #Hsp
      iunfold trace.isSpan at Hsp
      icases Hsp with ⟨%si, %hsi, #HEnd⟩
      subst hsi
      ipersist c
      ipersist span
      wp_apply wp_mapInsert $$ [$Hcm] as Hcm
      wp_apply wp_mapInsert $$ [$Hwm] as Hwm
      wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked HnextID Hclosed Hcf Hwf Hcm Hwm HCR]
      · inext
        iunfold mvcc.watchStreamInv
        iexists _, false, cm, wm, _, _
        simp only [named, Bool.false_eq_true, ↓reduceIte]
        iframe HnextID Hclosed Hcf Hwf Hcm Hwm
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
          · cases h; iexact HIW
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
      ipureintro
      first | (intro h; exact absurd rfl h) | (intro _; rfl)

end proof

end EtcdGrove
end Perennial
