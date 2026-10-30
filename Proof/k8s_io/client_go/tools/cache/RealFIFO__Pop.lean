/-
Proof of `Spec/k8s_io/client_go/tools/cache/RealFIFO__Pop.lean`. Lean-first.
-/
module

public import Spec.k8s_io.client_go.tools.cache.RealFIFO__Pop
public import Spec.k8s_io.client_go.tools.cache.RealFIFO__checkSynced_locked
public import Spec.k8s_io.client_go.tools.cache.RealFIFO__hasSynced_locked
public import Spec.k8s_io.client_go.tools.cache.RealFIFO__keyOf
public import Spec.k8s_io.client_go.tools.cache.InformerNameAndResource__Name_ptr
public import Spec.k8s_io.client_go.tools.cache.InformerNameAndResource__GroupVersionResource_ptr
public import Spec.k8s_io.apimachinery.pkg.runtime.schema.GroupVersionResource__Empty_ptr
public import Spec.k8s_io.utils.trace.New
public import Spec.k8s_io.utils.trace.Trace__LogIfLong
public import Spec.k8s_io.client_go.tools.cache.RealFIFO__whileProcessing_locked

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.iris.dupNamespace false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace cache

open Iris Iris.BI Iris.ProofMode k8s_io.client_go.tools.cache

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.tools.cache.Assumptions]

/-- A queued delta can be keyed (its object is not a tombstone). -/
theorem fdAt_keyOfArg (OK : GoInterface → IProp GF) (d : FD) (v : Delta) :
    fdAt OK d v ⊢ ⌜keyOfArg (interface.mkOk Delta.ty #v)⌝ := by
  iintro Hd
  cases d with
  | obj t o =>
    iunfold fdAt at Hd
    icases Hd with ⟨%h, -⟩
    obtain ⟨rfl, ty, w, rfl⟩ := h
    ipureintro
    refine Or.inr ⟨_, _, _, rfl, rfl, ?_⟩
    intro h; unfold DeletedFinalStateUnknown.ty at h; cases h
  | replaced objs rv =>
    iunfold fdAt at Hd
    icases Hd with ⟨%sl, %h, -⟩
    subst h
    ipureintro
    refine Or.inr ⟨_, _, _, rfl, rfl, ?_⟩
    intro h; unfold DeletedFinalStateUnknown.ty ReplacedAllInfo.ty at h; simp at h
  | bookmark rv =>
    iunfold fdAt at Hd
    icases Hd with %h
    subst h
    ipureintro
    refine Or.inr ⟨_, _, _, rfl, rfl, ?_⟩
    intro h; unfold DeletedFinalStateUnknown.ty BookmarkInfo.ty at h; simp at h

theorem RealFIFO.Pop.wp_proof
    (wp_check : RealFIFO.checkSynced_locked.spec (GF := GF) (hG := hG))
    (wp_hsl : RealFIFO.hasSynced_locked.spec (GF := GF) (hG := hG))
    (wp_keyOf : RealFIFO.keyOf.spec (GF := GF) (hG := hG))
    (wp_iname : InformerNameAndResource.Name_ptr.spec (GF := GF) (hG := hG))
    (wp_igvr : InformerNameAndResource.GroupVersionResource_ptr.spec (GF := GF) (hG := hG))
    (wp_empty : EtcdGrove.schema.GroupVersionResource.Empty_ptr.spec (GF := GF) (hG := hG))
    (wp_tnew : EtcdGrove.trace.New.spec (GF := GF) (hG := hG))
    (wp_tlog : EtcdGrove.trace.Trace.LogIfLong.spec (GF := GF) (hG := hG))
    (wp_wpl : RealFIFO.whileProcessing_locked.spec (GF := GF) (hG := hG)) :
    RealFIFO.Pop.spec (GF := GF) (hG := hG) := by
  intro f γ OK process Ψ Ψ' Ω
  wp_start as ⟨#Hf, Hproc, HAU1, HAU2⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  iunfold isFIFO at Hf
  icases Hf with ⟨%ch, %kf, %mp, %g, %h, %uwp, %idn, #Hkf, #Hkey, #Htr, #Hae, #Hbm, #Huwp, #Hbs,
    #Hch, #Hmp, #Hg, #Hgok, #Hh, #Hhok, #Hguard, #Hcond, #Hinv, #Hid, #Hkany⟩
  ihave #Hlocker := fifo_locker _ (fifoTok γ) $$ [$Hsync $Hguard]
  (try wp_auto)
  wp_apply wp_with_defer as %defer defer
  wp_apply (lc := 2) sync.RWMutex.wp_Lock_guard $$ [$Hguard] as ⟨Hlk, Htok⟩
  (try wp_auto)
  ihave HI : iprop(sync.ownRWMutexWLocked (f.[RealFIFO, go!"lock"]) (fifoTok γ) ∗
      ▷ fifoTok γ 1 ∗ £ 1 ∗ £ 1 ∗ popAU γ Ψ Ω) $$ [Hlk Htok Hlc1 Hlc2 HAU1]
  · iframe
  wp_for HI
  icases HI with ⟨Hlk, Htok, Hlca, Hlcb, HAU1⟩
  imod fifo_acquire f γ OK ch $$ Hinv Hlca Hlcb Htok with HR
  iunfold fifoRes at HR
  icases HR with ⟨%q, %sl, %vs, Hex, Hst, Hsy, Hitems, Hsl, Hcap, Hds, Hpop, Hinit, %Hic,
    Hsc, Hcl, Hbc⟩
  ihave %Hlen := ownSlice_len _ _ _ $$ Hsl
  ihave %Hlen2 := (BigSepL2.bigSepL2_length (Φ := fun _ x y => fdAt OK x y)) $$ Hds
  wp_auto_lc 3
  rcases hq : q.items with _ | ⟨d, ds⟩
  · -- empty: closed, or wait
    rw [hq] at Hlen2
    have hsl0 : sl.len = W64 0 := by
      have h1 := Hlen.1; rw [← Hlen2] at h1; simp at h1; word
    simp only [hsl0, decide_true, ↓reduceIte]
    cases hcl : q.closed with
    | false =>
      (try wp_auto)
      imod fifo_release f γ OK ch $$ Hinv Hlc1 [Hex Hst Hsy Hitems Hsl Hcap Hds Hpop Hinit Hsc Hcl Hbc]
        with Htok
      · iunfold fifoRes
        iexists q, sl, vs
        rw [hq, hcl]
        iframe
        ipureintro; exact Hic
      wp_apply (sync.Cond.wp_Wait (f.[RealFIFO, go!"cond"])
          ⟨go.GoType.PointerType _root_.Perennial.sync.RWMutex.ty, #(f.[RealFIFO, go!"lock"])⟩
          iprop(sync.ownRWMutexWLocked (f.[RealFIFO, go!"lock"]) (fifoTok γ) ∗ ▷ fifoTok γ 1))
        $$ [$Hcond $Hlocker Hlk Htok] as ⟨Hlk, Htok⟩
      · iframe
      wp_for_post
      simp only [named]
      iframe
    | true =>
      ihave #Hm : (k8s_io.apiserver.pkg.storage.cacher.k8sCacheInit : IProp GF) $$ []
      · iapply isPkgInit_access $$ Hpkg
      icases Hm with ⟨%e1, %e2, #He1, #He2⟩
      (try wp_auto)
      wp_for_post
      iunfold popAU at HAU1
      imod (lc_fupd_elim_later (E := ⊤)) $$ Hlc2 HAU1 with HAU1
      imod (fifo_commit γ q id rfl iprop(∀ (x e : GoInterface), Ω (PairV #x #e)))
        $$ [Hst HAU1] with ⟨Hst, HΩ⟩
      · iframe Hst
        imod HAU1 with ⟨%q', Hst', HAU1⟩
        imodintro
        iexists q'
        iframe Hst'
        iintro %heq Hst'
        subst heq
        simp only [id]
        icases HAU1 with ⟨HAUc, -⟩
        iapply HAUc $$ %(⟨hq, hcl⟩) Hst'
      imod fifo_release f γ OK ch $$ Hinv Hlc1 [Hex Hst Hsy Hitems Hsl Hcap Hds Hpop Hinit Hsc Hcl Hbc]
        with Htok
      · iunfold fifoRes
        iexists q, sl, vs
        rw [hq, hcl]
        iframe
        ipureintro; exact Hic
      wp_apply sync.RWMutex.wp_Unlock_guard $$ [$Hsync $Hlk $Htok]
      (try wp_auto)
      iapply HΦ; iapply HΩ
  · -- a delta first: the loop ends
    rw [hq] at Hlen2
    obtain ⟨v, vs', hvs⟩ : ∃ v vs', vs = v :: vs' := by
      cases vs with
      | nil => simp at Hlen2
      | cons v vs' => exact ⟨v, vs', rfl⟩
    subst hvs
    have hne : sl.len ≠ W64 0 := by
      intro h; have h1 := Hlen.1; rw [h, show sint.nat (W64 0) = 0 from rfl] at h1; simp at h1
    simp only [decide_eq_false hne]
    (try wp_auto)
    have hft : (#false : val) ≠ #true := fun h => by
      have := GoGlobalContext.intoVal_inj_bool h; cases this
    simp only [decide_eq_false hft, Bool.false_eq_true, ↓reduceIte]
    (try wp_auto)
    simp only [decide_true, ↓reduceIte]
    (try wp_auto)
    wp_apply (wp_hsl f q.synced) $$ [$Hsc] as Hsc
    (try wp_auto)
    have hlen1 : 0 < sint.Z sl.len := by
      have h1 := Hlen.1; simp at h1; word
    simp only [show 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z sl.len from ⟨by word, by word⟩,
      ↓reduceIte]
    wp_apply (wp_load_slice_index sl (sint.Z (W64 0)) (v :: vs') (DFrac.own 1) v (by word))
      $$ [$Hsl] as Hsl
    · ipureintro; rfl
    (try wp_auto)
    simp only [show 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z sl.len from ⟨by word, by word⟩,
      ↓reduceIte]
    wp_apply (wp_store_slice_index sl (sint.Z (W64 0)) (v :: vs') (zero_val Delta)) $$ [$Hsl] as Hsl
    · ipureintro; (try simp); (try word)
    (try wp_auto)
    ihave %Hcapw := ownSliceCap_wf _ _ $$ Hcap
    have hb1 : 0 ≤ sint.Z (W64 1) ∧ sint.Z (W64 1) ≤ sint.Z sl.len ∧ sint.Z sl.len ≤ sint.Z sl.cap :=
      ⟨by word, by word, Hcapw.2⟩
    simp only [hb1, ↓reduceIte]
    icases (ownSlice_slice_with_cap (W64 1) sl.len sl (zero_val Delta :: vs') ⟨by word, by word, by word⟩)
      $$ [$Hsl $Hcap] with ⟨-, Hsl, Hcap⟩
    have hsub : subslice (sint.nat (W64 1)) (sint.nat sl.len) (zero_val Delta :: vs') = vs' := by
      have h1 := Hlen.1
      simp only [List.length_cons] at h1
      rw [show sint.nat (W64 1) = 1 from rfl, ← h1]
      simp [subslice]
    rw [hsub]
    (try wp_auto)
    wp_if_destruct
    · -- the slow-queue trace
      icases Hds with ⟨Hd, Hds⟩
      ihave %hka := fdAt_keyOfArg OK d v $$ Hd
      wp_apply (wp_keyOf f OK kf (interface.mkOk Delta.ty #v)) $$ [$Hkf $Hkey $Hkany]
      · isplitr
        · ipureintro; exact hka
        iintro %h
        exfalso
        obtain ⟨t', v', h⟩ := h
        have h1 := congrArg GoInterfaceOk.ty (GoInterface.ok.inj h)
        simp only at h1
        unfold Delta.ty at h1
        cases h1
      iintro %kid %kerr -
      (try wp_auto)
      wp_apply wp_slice_literal
      isplitr
      · ipureintro; rfl
      iintro %fl ⟨Hfl, Hflc⟩
      simp only [go.arrayLiteralSize, List.foldl]
      (try wp_auto)
      wp_apply (wp_iname (f.[RealFIFO, go!"identifier"]) DFrac.discard idn) $$ [$Hid] as -
      (try wp_auto)
      ihave Hfields : iprop(∃ (fs : GoSlice) (fv : List k8s_io.utils.trace.Field),
          fields_ptr ↦ fs ∗ fs ↦* fv ∗ ownSliceCap k8s_io.utils.trace.Field fs (DFrac.own 1))
        $$ [fields Hfl Hflc]
      · iexists _, _; iframe
      wp_bind (If _ _ _)
      iapply (wp_wand_r (Φ := fun v => iprop(⌜v = executeVal⌝ ∗
          ∃ (fs : GoSlice) (fv : List k8s_io.utils.trace.Field),
          fields_ptr ↦ fs ∗ fs ↦* fv ∗ ownSliceCap k8s_io.utils.trace.Field fs (DFrac.own 1))))
      isplitl [Hfields name]
      · (try wp_auto)
        icases Hfields with ⟨%fs, %fv, Hfp, Hfs, Hfc⟩
        (try wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %-)
        (try wp_auto)
        wp_if_destruct
        all_goals
          (try wp_auto)
          (try (wp_apply wp_slice_literal
                isplitr
                · ipureintro; first | rfl | trivial
                iintro %l1 ⟨Hl1, -⟩
                simp only [go.arrayLiteralSize, List.foldl]
                (try wp_auto)
                wp_apply wp_slice_append $$ [$Hfs $Hfc $Hl1] as %fs' ⟨Hfs, Hfc, -⟩
                (try wp_auto)))
          isplitr
          · ipureintro; first | rfl | trivial
          iexists _, _; iframe
      iintro %v1 ⟨%hv1, Hfields⟩
      subst hv1
      (try wp_auto)
      wp_apply (wp_igvr (f.[RealFIFO, go!"identifier"]) DFrac.discard idn) $$ [$Hid] as -
      (try wp_auto)
      wp_bind (If _ _ _)
      iapply (wp_wand_r (Φ := fun v => iprop(⌜v = executeVal⌝ ∗
          ∃ (fs : GoSlice) (fv : List k8s_io.utils.trace.Field),
          fields_ptr ↦ fs ∗ fs ↦* fv ∗ ownSliceCap k8s_io.utils.trace.Field fs (DFrac.own 1))))
      isplitl [Hfields gvr]
      · (try wp_auto)
        wp_apply (wp_empty gvr_ptr (DFrac.own 1) idn.gvr') $$ [$gvr] as %be gvr
        (try wp_auto)
        icases Hfields with ⟨%fs, %fv, Hfp, Hfs, Hfc⟩
        generalize (!be) = c
        (try wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %-)
        (try wp_auto)
        wp_if_destruct
        all_goals
          (try wp_auto)
          (try (wp_apply wp_slice_literal
                isplitr
                · ipureintro; first | rfl | trivial
                iintro %l1 ⟨Hl1, -⟩
                simp only [go.arrayLiteralSize, List.foldl]
                (try wp_auto)
                wp_apply wp_slice_append $$ [$Hfs $Hfc $Hl1] as %fs' ⟨Hfs, Hfc, -⟩
                (try wp_auto)))
          isplitr
          · ipureintro; first | rfl | trivial
          iexists _, _; iframe
      iintro %v2 ⟨%hv2, Hfields⟩
      subst hv2
      icases Hfields with ⟨%fs, %fv, Hfp, Hfs, Hfc⟩
      (try wp_auto)
      wp_apply wp_tnew as %tr -
      (try wp_auto)
      iunfold popAU at HAU1
      imod (lc_fupd_elim_later (E := ⊤)) $$ Hlc2 HAU1 with HAU1
      imod (fifo_commit γ q (fun q => { q with items := ds }) rfl iprop(Ψ d (!q.synced)))
        $$ [Hst HAU1] with ⟨Hst, HΨ⟩
      · iframe Hst
        imod HAU1 with ⟨%q', Hst', HAU1⟩
        imodintro
        iexists q'
        iframe Hst'
        iintro %heq Hst'
        subst heq
        icases HAU1 with ⟨-, HAUd⟩
        iapply HAUd $$ %d %ds %hq Hst'
      cases g with
      | nil => iunfold gaugeOk at Hgok; icases Hgok with ⟨⟩
      | ok gi =>
      iunfold gaugeOk at Hgok
      (try wp_auto)
      wp_apply Hgok
      (try wp_auto)
      wp_apply (wp_wpl f γ OK ch uwp mp h _ (fun err => iprop(Ψ' d err ∗ item_ptr ↦ v ∗
          isInInitialList_ptr ↦ !q.synced ∗ process_ptr ↦ process)))
        $$ [$Hpkg $Hguard $Hinv $Huwp $Hbs $Hmp $Hh $Hhok $Hlk Hex Hst Hsy Hitems Hsl Hcap Hds Hpop Hinit Hsc Hcl
          Hbc item isInInitialList process Hproc Hd HΨ] as %err ⟨Hlk, HR, HΨ', item, isInInitialList, process⟩
      · isplitl [Hex Hst Hsy Hitems Hsl Hcap Hds Hpop Hinit Hsc Hcl Hbc]
        · iunfold fifoRes
          iexists { q with items := ds }, _, vs'
          iframe
          ipureintro; exact Hic
        (try wp_call)
        (try wp_auto)
        wp_apply wp_slice_literal
        isplitr
        · ipureintro; rfl
        iintro %dsl ⟨Hdsl, -⟩
        simp only [go.arrayLiteralSize, List.foldl]
        (try wp_auto)
        iunfold processOk at Hproc
        wp_apply_core wp_wand $$ (Hproc $$ %d %(!q.synced) %v %_ Hd Hdsl HΨ)
        iintro %r ⟨%e, %hr, HΨ'⟩
        subst hr
        (try wp_auto)
        iexists e
        iframe
        ipureintro; rfl
      (try wp_auto)
      wp_apply wp_slice_literal
      isplitr
      · ipureintro; rfl
      iintro %rsl -
      simp only [go.arrayLiteralSize, List.foldl]
      (try wp_auto)
      wp_apply wp_tlog
      (try wp_auto)
      iunfold fifoRes at HR
      icases HR with ⟨%q2, %sl2, %vs2, Hex, Hst, Hsy, Hitems, Hsl, Hcap, Hds, Hpop, Hinit, %Hic2,
        Hsc, Hcl, Hbc⟩
      iunfold doneAU at HAU2
      ispecialize HAU2 $$ %d %err HΨ'
      imod (lc_fupd_elim_later (E := ⊤)) $$ Hlc3 HAU2 with HAU
      ihave HAU' : iprop(|={⊤ \ ∅, ∅}=> ∃ q', fifoSt γ q' ∗
          (fifoSt γ q'.popDone ={∅, ⊤ \ ∅}=∗ ∀ x : GoInterface, Ω (PairV #x #err))) $$ [HAU]
      · rw [Iris.Std.LawfulSet.diff_empty]; iexact HAU
      imod fifoSt_update_sy γ q2 FQ.popDone
        (fun h => by unfold FQ.popDone; split <;> simp [h])
        (fun _ => iprop(∀ x : GoInterface, Ω (PairV #x #err))) $$ [$Hst $Hsy $HAU']
        with ⟨Hst, Hsy, Hlb, HK⟩
      (try wp_auto)
      wp_if_destruct
      · have hpos : 0 < q2.initCount := by
          have h1 := Hif; have h2 := Hic2
          rw [show sint.Z (W64 (q2.initCount : Int)) = (q2.initCount : Int) by word] at h1
          simp at h1; omega
        have hw : W64 (q2.initCount : Int) - W64 1 = W64 ((q2.initCount - 1 : Nat) : Int) := by
          rw [show ((q2.initCount - 1 : Nat) : Int) = (q2.initCount : Int) - 1 by omega]; word
        rw [hw]
        (try wp_auto)
        wp_apply (wp_check f ch γ.ch (fifoSyncedLb γ) q2.populated (q2.initCount - 1) q2.synced)
          $$ [$Hpop $Hinit $Hsc $Hch $Hbc Hlb] as ⟨Hpop, Hinit, Hsc, Hbc⟩
        · isplitr
          · ipureintro; omega
          iintro %hs
          have : q2.popDone.synced = true := by
            simp only [syncsNow, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hs
            simp [FQ.popDone, hpos, hs.1.1, hs.1.2]
          rw [this]; simp only [↓reduceIte]
          icases Hlb with #Hlb
          imodintro; iexact Hlb
        (try wp_auto)
        have hsy : (q2.synced || syncsNow q2.populated (q2.initCount - 1) q2.synced) =
            q2.popDone.synced := by
          unfold FQ.popDone syncsNow; simp only [hpos, ↓reduceIte]
          cases q2.synced <;> cases q2.populated <;> simp
        rw [hsy]
        imod fifo_release f γ OK ch $$ Hinv Hlc1 [Hex Hst Hsy Hitems Hsl Hcap Hds Hpop Hinit Hsc Hcl Hbc]
          with Htok
        · iunfold fifoRes
          iexists q2.popDone, sl2, vs2
          have hpi : q2.popDone.initCount = q2.initCount - 1 := by simp [FQ.popDone, hpos]
          have hpp : q2.popDone.populated = q2.populated := by unfold FQ.popDone; split <;> rfl
          have hpc : q2.popDone.closed = q2.closed := by unfold FQ.popDone; split <;> rfl
          have hpt : q2.popDone.items = q2.items := by unfold FQ.popDone; split <;> rfl
          rw [hpi, hpp, hpc, hpt]
          iframe
          ipureintro; omega
        wp_apply sync.RWMutex.wp_Unlock_guard $$ [$Hsync $Hlk $Htok]
        (try wp_auto)
        iapply HΦ; iapply HK
      · have h0 : q2.initCount = 0 := by
          have h1 := Hif; have h2 := Hic2
          rw [show sint.Z (W64 (q2.initCount : Int)) = (q2.initCount : Int) by word] at h1
          simp at h1; omega
        have hpd : q2.popDone = q2 := by unfold FQ.popDone; simp [h0]
        rw [hpd]
        (try wp_auto)
        imod fifo_release f γ OK ch $$ Hinv Hlc1 [Hex Hst Hsy Hitems Hsl Hcap Hds Hpop Hinit Hsc Hcl Hbc]
          with Htok
        · iunfold fifoRes
          iexists q2, sl2, vs2
          iframe
          ipureintro; exact Hic2
        wp_apply sync.RWMutex.wp_Unlock_guard $$ [$Hsync $Hlk $Htok]
        (try wp_auto)
        iapply HΦ; iapply HK
    · icases Hds with ⟨Hd, Hds⟩
      (try wp_auto)
      iunfold popAU at HAU1
      imod (lc_fupd_elim_later (E := ⊤)) $$ Hlc2 HAU1 with HAU1
      imod (fifo_commit γ q (fun q => { q with items := ds }) rfl iprop(Ψ d (!q.synced)))
        $$ [Hst HAU1] with ⟨Hst, HΨ⟩
      · iframe Hst
        imod HAU1 with ⟨%q', Hst', HAU1⟩
        imodintro
        iexists q'
        iframe Hst'
        iintro %heq Hst'
        subst heq
        icases HAU1 with ⟨-, HAUd⟩
        iapply HAUd $$ %d %ds %hq Hst'
      cases g with
      | nil => iunfold gaugeOk at Hgok; icases Hgok with ⟨⟩
      | ok gi =>
      iunfold gaugeOk at Hgok
      (try wp_auto)
      wp_apply Hgok
      (try wp_auto)
      wp_apply (wp_wpl f γ OK ch uwp mp h _ (fun err => iprop(Ψ' d err ∗ item_ptr ↦ v ∗
          isInInitialList_ptr ↦ !q.synced ∗ process_ptr ↦ process)))
        $$ [$Hpkg $Hguard $Hinv $Huwp $Hbs $Hmp $Hh $Hhok $Hlk Hex Hst Hsy Hitems Hsl Hcap Hds Hpop Hinit Hsc Hcl
          Hbc item isInInitialList process Hproc Hd HΨ] as %err ⟨Hlk, HR, HΨ', item, isInInitialList, process⟩
      · isplitl [Hex Hst Hsy Hitems Hsl Hcap Hds Hpop Hinit Hsc Hcl Hbc]
        · iunfold fifoRes
          iexists { q with items := ds }, _, vs'
          iframe
          ipureintro; exact Hic
        (try wp_call)
        (try wp_auto)
        wp_apply wp_slice_literal
        isplitr
        · ipureintro; rfl
        iintro %dsl ⟨Hdsl, -⟩
        simp only [go.arrayLiteralSize, List.foldl]
        (try wp_auto)
        iunfold processOk at Hproc
        wp_apply_core wp_wand $$ (Hproc $$ %d %(!q.synced) %v %_ Hd Hdsl HΨ)
        iintro %r ⟨%e, %hr, HΨ'⟩
        subst hr
        (try wp_auto)
        iexists e
        iframe
        ipureintro; rfl
      (try wp_auto)
      wp_apply wp_slice_literal
      isplitr
      · ipureintro; rfl
      iintro %rsl -
      simp only [go.arrayLiteralSize, List.foldl]
      (try wp_auto)
      iunfold fifoRes at HR
      icases HR with ⟨%q2, %sl2, %vs2, Hex, Hst, Hsy, Hitems, Hsl, Hcap, Hds, Hpop, Hinit, %Hic2,
        Hsc, Hcl, Hbc⟩
      iunfold doneAU at HAU2
      ispecialize HAU2 $$ %d %err HΨ'
      imod (lc_fupd_elim_later (E := ⊤)) $$ Hlc3 HAU2 with HAU
      ihave HAU' : iprop(|={⊤ \ ∅, ∅}=> ∃ q', fifoSt γ q' ∗
          (fifoSt γ q'.popDone ={∅, ⊤ \ ∅}=∗ ∀ x : GoInterface, Ω (PairV #x #err))) $$ [HAU]
      · rw [Iris.Std.LawfulSet.diff_empty]; iexact HAU
      imod fifoSt_update_sy γ q2 FQ.popDone
        (fun h => by unfold FQ.popDone; split <;> simp [h])
        (fun _ => iprop(∀ x : GoInterface, Ω (PairV #x #err))) $$ [$Hst $Hsy $HAU']
        with ⟨Hst, Hsy, Hlb, HK⟩
      (try wp_auto)
      wp_if_destruct
      · have hpos : 0 < q2.initCount := by
          have h1 := Hif; have h2 := Hic2
          rw [show sint.Z (W64 (q2.initCount : Int)) = (q2.initCount : Int) by word] at h1
          simp at h1; omega
        have hw : W64 (q2.initCount : Int) - W64 1 = W64 ((q2.initCount - 1 : Nat) : Int) := by
          rw [show ((q2.initCount - 1 : Nat) : Int) = (q2.initCount : Int) - 1 by omega]; word
        rw [hw]
        (try wp_auto)
        wp_apply (wp_check f ch γ.ch (fifoSyncedLb γ) q2.populated (q2.initCount - 1) q2.synced)
          $$ [$Hpop $Hinit $Hsc $Hch $Hbc Hlb] as ⟨Hpop, Hinit, Hsc, Hbc⟩
        · isplitr
          · ipureintro; omega
          iintro %hs
          have : q2.popDone.synced = true := by
            simp only [syncsNow, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hs
            simp [FQ.popDone, hpos, hs.1.1, hs.1.2]
          rw [this]; simp only [↓reduceIte]
          icases Hlb with #Hlb
          imodintro; iexact Hlb
        (try wp_auto)
        have hsy : (q2.synced || syncsNow q2.populated (q2.initCount - 1) q2.synced) =
            q2.popDone.synced := by
          unfold FQ.popDone syncsNow; simp only [hpos, ↓reduceIte]
          cases q2.synced <;> cases q2.populated <;> simp
        rw [hsy]
        imod fifo_release f γ OK ch $$ Hinv Hlc1 [Hex Hst Hsy Hitems Hsl Hcap Hds Hpop Hinit Hsc Hcl Hbc]
          with Htok
        · iunfold fifoRes
          iexists q2.popDone, sl2, vs2
          have hpi : q2.popDone.initCount = q2.initCount - 1 := by simp [FQ.popDone, hpos]
          have hpp : q2.popDone.populated = q2.populated := by unfold FQ.popDone; split <;> rfl
          have hpc : q2.popDone.closed = q2.closed := by unfold FQ.popDone; split <;> rfl
          have hpt : q2.popDone.items = q2.items := by unfold FQ.popDone; split <;> rfl
          rw [hpi, hpp, hpc, hpt]
          iframe
          ipureintro; omega
        wp_apply sync.RWMutex.wp_Unlock_guard $$ [$Hsync $Hlk $Htok]
        (try wp_auto)
        iapply HΦ; iapply HK
      · have h0 : q2.initCount = 0 := by
          have h1 := Hif; have h2 := Hic2
          rw [show sint.Z (W64 (q2.initCount : Int)) = (q2.initCount : Int) by word] at h1
          simp at h1; omega
        have hpd : q2.popDone = q2 := by unfold FQ.popDone; simp [h0]
        rw [hpd]
        (try wp_auto)
        imod fifo_release f γ OK ch $$ Hinv Hlc1 [Hex Hst Hsy Hitems Hsl Hcap Hds Hpop Hinit Hsc Hcl Hbc]
          with Htok
        · iunfold fifoRes
          iexists q2, sl2, vs2
          iframe
          ipureintro; exact Hic2
        wp_apply sync.RWMutex.wp_Unlock_guard $$ [$Hsync $Hlk $Htok]
        (try wp_auto)
        iapply HΦ; iapply HK

end proof

end cache
end EtcdGrove
end Perennial
