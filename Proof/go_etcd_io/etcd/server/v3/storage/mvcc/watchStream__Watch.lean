/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.watchStream__Watch
public import Spec.go_opentelemetry_io.otel.trace.SpanFromContext
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.Api
public import Proof.ReceiptTactics

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
  intro ws wa P γ ctx cd id key endk fcs k e fs startRev
  wp_start as ⟨Hws, #Hctx, #Hk, #He, #Hfcs, #Hfs, HPR, HPT, %Hsr0⟩
  obtain ⟨Hsr, Hid0⟩ := Hsr0
  iunfold mvcc.isWatchStream at Hws
  iNamed Hws
  ihave Hmi : (mvccInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hmi with ⟨-, -, -, -, -, -, -, -, -, -, -, -, ⟨%eer, #Heer⟩, ⟨%edu, #Hedu⟩, -⟩
  iunfold mvcc.isWatchable at Hwable
  icases Hwable with ⟨%wi, %hwa, #Hwatch, #Hprog, #HprogAll, #Hrev⟩
  subst hwa
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
      wp_apply Hwatch $$ [$HCR $HPR $HPT $Hreg] as %w %c
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
            wp_bind (App (Val #(methods si.ty go!"End" si.v)) (Val #slice.nil))
            iapply HEnd $$ %slice.nil
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

/-- Filters implementing predicates are the store's (`storeWatchParams`' `F`). -/
theorem mvcc.filters_F (s st : Loc) (γ : mvcc.WsNames) :
    ∀ (fns : List GoFunc) (fs : List (mvcc.EvM → Bool)), fns.length = fs.length →
      ([∗list] x ∈ fns.zip fs, mvcc.filterSpec (GF := GF) x.1 x.2) ⊢
        [∗list] f ∈ fns, (mvcc.storeWatchParams (GF := GF) s st γ).F f
  | [], _, _ => by iintro _; iapply BigSepL.bigSepL_nil_intro; iempintro
  | _ :: _, [], h => by simp at h
  | f :: fns, p :: fs, h => by
    simp only [List.zip_cons_cons]
    iintro H
    icases BigSepL.bigSepL_cons.1 $$ H with ⟨#Hf, H⟩
    iapply BigSepL.bigSepL_cons.2
    isplitr
    · simp only [mvcc.storeWatchParams]; iexists p; iexact Hf
    iapply mvcc.filters_F s st γ fns fs (by simpa using h)
    iexact H

/-- **A closed stream refutes a share of the open token** (`Watch`'s closed arm): with the old
stream's open token (the closed lock state's), the open invariant holds the whole token and the
persistent closed mark. -/
theorem mvcc.wsClosed (st : Loc) (γ : mvcc.MvccImpl) (ι : mvcc.WsNameI) :
    mvcc.isMvccWatchStreamI (GF := GF) st γ ι ∗ mvcc.watchStreamOpen ι.o ={⊤}=∗
      mvcc.watchStreamOpen ι.o ∗ □ (∀ q : Qp, mvcc.wsOpen ι q ={⊤}=∗ False) := by
  iintro ⟨#Hst, Ho⟩
  iunfold mvcc.isMvccWatchStreamI at Hst
  icases Hst with ⟨-, -, -, -, -, -, -, #Hoi, -⟩
  iinv Hoi with Hi Hclose
  icases Hi with (⟨Ht, >#Hcl⟩ | ⟨>Ho', -⟩)
  · imod Hclose $$ [Ht] with _
    · inext; ileft; iframe Ht Hcl
    imodintro
    iframe Ho
    iintro !> %q Hq
    iunfold mvcc.wsOpen at Hq
    iunfold mvcc.wsOpenI at Hq
    iinv Hoi with Hi Hclose
    icases Hi with (⟨>Ht, -⟩ | ⟨-, >Hc1⟩)
    · ihave %Hv := ghostVar_valid_2 ι.op _ _ _ _ $$ Hq Ht
      exfalso
      have h1 : q.val + (1 : Qp).val ≤ 1 := Hv.1
      have := q.2
      grind
    · ihave %Hv := dghostVar_valid_2 ι.cl _ _ _ _ $$ Hcl Hc1
      exfalso
      exact absurd (DFrac.valid_op_own Hv.1) (by simp)
  · iunfold mvcc.watchStreamOpen at Ho
    iunfold mvcc.watchStreamOpen at Ho'
    iexfalso
    iapply (token_exclusive ι.o.tok) $$ Ho Ho'

/-- **The candidate `Watch`** (`specC`): `spec`'s, at a positive start revision, the watchable
store's reader borrowed from the readers' pool (a credit of the call's steps) and the watch token
taken from the pool (the receipt of the store's `watch`'s resolution); the caller's update fired
once the store's `watch` returned (the watcher, under the id the stream assigned, a fresh one: the
registrar's view holds its ids' tokens). -/
theorem mvcc.watchStream.Watch.wp_proofC (hspan : trace.SpanFromContext.spec (GF := GF) (hG := hG)) :
    mvcc.watchStream.Watch.specC (GF := GF) (hG := hG) := by
  intro ws γ' ι ctx cd key endk fcs k e fsp startRev Q
  wp_start as ⟨#Hstr, Htt, #Hctx, #Hk, #He, #Hfi, %Hsr1, Hau⟩
  have Hsr : 0 ≤ sint.Z startRev := by omega
  have Hid0 : (W64 0 : w64) = W64 0 := rfl
  ihave #Hstr0 := Hstr
  iunfold mvcc.isMvccWatchStream at Hstr0
  iunfold mvcc.isMvccWatchStreamI at Hstr0
  icases Hstr0 with ⟨%Hn, #Hws, -, -, -, -, -, -, #Hwm⟩
  obtain ⟨hmv, hw, -⟩ := Hn
  ihave #Hwm0 := Hwm
  iunfold mvcc.isWatchableMvccI at Hwm0
  icases Hwm0 with ⟨-, %s, -, #Hmv⟩
  ihave %Hsl := mvcc.isMvccI_loc s γ' $$ Hmv
  ihave #Hmv1 := Hmv
  iunfold mvcc.isMvccI at Hmv1
  icases Hmv1 with ⟨-, -, -, -, -, -, -, #Hwtp, -⟩
  isimp only [hw, ↓reduceIte] at Hwtp
  iunfold mvcc.wtPool at Hwtp
  icases Hwtp with ⟨#Hwtp, #Hnc⟩
  ihave #Hfi0 := Hfi
  iunfold mvcc.filtersImpl at Hfi0
  icases Hfi0 with ⟨%fs, #Hfcs, %Hfl, #Hfz⟩
  ihave #Hfs := mvcc.filters_F γ'.wl γ'.sl γ'.ws fs fsp Hfl $$ Hfz
  have hcl := mvcc.wsClosed (GF := GF) ws γ' ι
  generalize (interface.mkOk (go.GoType.PointerType watchableStore.ty) #γ'.wl : GoInterface) = wa
  generalize hP : (mvcc.storeWatchParams (GF := GF) γ'.wl γ'.sl γ'.ws) = P
  generalize hγ : ι.o = γ at hcl
  iunfold mvcc.isWatchStream at Hws
  iNamed Hws
  ihave Hmi : (mvccInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hmi with ⟨-, -, -, -, -, -, -, -, -, -, -, -, ⟨%eer, #Heer⟩, ⟨%edu, #Hedu⟩, -⟩
  iunfold mvcc.isWatchable at Hwable
  icases Hwable with ⟨%wi, %hwa, #Hwatch, #Hprog, #HprogAll, #Hrev⟩
  subst hwa
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
  iframe Htt
  iright
  isplitr
  · ipureintro; rfl
  iframe Heer Hau
  ileft
  ipureintro
  constructor
  · intro h
    apply hlen
    rw [h] at Helen
    have h1 := Helen.1
    have h2 := Helen.2
    simp only [List.length_nil] at h1
    word
  · intro hlt
    apply Hif
    unfold bytes.compareResult
    rw [if_pos hlt]
  -- the single-key case
  have hne : e = [] ∨ go.GoStringLt k e := Or.inl hne0
  all_goals
    irename : (end_ptr ↦ endk : IProp GF) => Hendp
    wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, HR⟩
    iunfold mvcc.watchStreamInv at HR
    iNamed HR
    cases closed
    rotate_left
    -- closed: `ErrEmptyWatcherRange`; the open token's share refuted
    wp_auto
    try isimp only [↓reduceIte] at Hcl
    icases Hcl with ⟨Hop, #Hall⟩
    subst hγ
    imod hcl $$ [Hop] with ⟨Hop, #Hclf⟩
    · iframe Hop; iunfold mvcc.isMvccWatchStream at Hstr; iexact Hstr
    wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked HnextID Hclosed Hcf Hwf Hcm Hwm Hids Hop]
    · inext
      iunfold mvcc.watchStreamInv
      iexists nextID, true, cm, wm, CM, WM
      simp only [named, if_true, ite_true, ↓reduceIte]
      iframe
      iframe #
      ipureintro; exact ⟨Hdom, Hnn⟩
    iapply HΦ
    iframe Htt
    iright
    isplitr
    · ipureintro; rfl
    iframe Heer Hau
    iright
    iexact Hclf
    -- open
    simp only [Bool.false_eq_true, ↓reduceIte]
    icases Hcl with ⟨%L, HCR, #HL, %Hcnt⟩
    iunfold mvcc.idsInv at Hids
    icases Hids with ⟨%IDS, Hida, Hidf, %Hidb⟩
    wp_auto_lc 1
    imod mvcc.mvccBorrowW s γ' hw $$ [$Hlc1 $Hmv $Htt] with ⟨HPR, Hback⟩
    ihave HPR : P.R $$ [HPR]
    · rw [← hP]; simp only [mvcc.storeWatchParams]; rw [Hsl]; iexact HPR
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
    -- the store's `watch`'s resolution: its receipt pays the watch token
    wp_take_receipt as Hrw
    imod mvcc.watchTokPool_take γ'.ws $$ Hwtp Hrw with Htok
    wp_auto
    -- the id chosen: named `id` as in the other case (the parameter is `AutoWatchID` here)
    generalize n = id at hnone hcntF hstep ⊢
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
      ihave HPT : P.T $$ [Htok]
      · rw [← hP]; simp only [mvcc.storeWatchParams]; iframe Htok Hnc
      wp_apply Hwatch $$ [$HCR $HPR $HPT $Hreg] as %w %c
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
      iapply wp_fupd
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
            wp_bind (App (Val #(methods si.ty go!"End" si.v)) (Val #slice.nil))
            iapply HEnd $$ %slice.nil
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
      -- the reader back
      imod Hback $$ [HPR] with Htt
      · subst hP; rw [← Hsl]; simp only [mvcc.storeWatchParams]; iexact HPR
      subst hγ hP
      ihave #HIWF' : mvcc.watcherIs γ'.ws w (mvcc.watchRangeOf k e endk startRev id) fcs lo $$ []
      · isimp only [mvcc.storeWatchParams] at HIWF; iexact HIWF
      ihave #Hw0 := HIWF'
      iunfold mvcc.watcherIs at Hw0
      icases Hw0 with ⟨%γw, %C, -, -, -, ⟨%nreg, -⟩, %Hlo⟩
      have hsr0 : startRev ≠ W64 0 := by intro h; rw [h] at Hsr1; simp at Hsr1
      have hlo : lo = sint.nat startRev := by
        have h2 := Hlo.2
        simp only [mvcc.watchRangeOf, hsr0, ↓reduceIte] at h2
        exact h2
      -- the caller's update: the watcher registered, under its fresh id
      ihave Hau := atomic_update_mask_weaken (Eo1 := ⊤ \ ↑mvcc.mvccN) (Eo2 := ⊤) (by simp) $$ Hau
      ihave Hacc := aupd_aacc $$ Hau
      unfold atomic_acc
      imod Hacc with Hacc
      isimp only [texist_cons, texist_nil, Std.Tele.app, ULift.down] at Hacc
      icases Hacc with ⟨%σ, %W, ⟨Hσ, HW⟩, Hucl⟩
      iunfold mvcc.wsWatchers at HW
      iunfold mvcc.wsWatchersI at HW
      icases HW with ⟨Hreg, Htoks, #Hinfo⟩
      cases hWid : W !! id with
      | some wi0 =>
        icases (BigSepM.bigSepM_lookup_acc hWid).1 $$ Htoks with ⟨Ht2, -⟩
        iexfalso
        iapply (mvcc.idTok_excl ι.o id)
        iframe Hit Ht2
      | none =>
        icases Hucl with ⟨-, Hcommit⟩
        isimp only [tforall_cons, tforall_nil, Std.Tele.app, ULift.down] at Hcommit
        imod Hcommit $$ %id %nreg [Hσ Hreg Htoks Hit] with HQ
        · iframe Hσ
          isplitr
          · ipureintro; exact hWid
          iunfold mvcc.wsWatchers
          iunfold mvcc.wsWatchersI
          iframe Hreg
          isplitl [Htoks Hit]
          · iapply (BigSepM.bigSepM_insert hWid).2
            iframe Hit Htoks
          iintro !>
          iapply (BigSepM.bigSepM_insert hWid).2
          iframe Hinfo
          iunfold mvcc.wInfoOk
          iexists w, fcs
          simp only [hmv, ← hlo]
          iframe Hia HIWF' Hfi
          ipureintro
          have h5 : sint.nat startRev = (sint.Z startRev).toNat := rfl
          exact ⟨rfl, hidm, by omega⟩
        imodintro
        (try wp_auto)
        iapply HΦ
        iframe Htt
        ileft
        isplitr
        · ipureintro; exact ⟨rfl, hne⟩
        iexists σ, W
        iexact HQ

end proof

end EtcdGrove
end Perennial
