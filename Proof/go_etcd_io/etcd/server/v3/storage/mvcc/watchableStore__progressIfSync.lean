/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.watchableStore__progressIfSync
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.watchableStore__rev
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.watcher__send

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- The group's all-watchers set at a fraction, lent: the group's struct and the set at `q`,
and the group back from them. -/
theorem mvcc.ownWatcherGroup_watchers_frac (wg : Loc) (W : GMap Loc mvcc.WatchRange) (q : Qp) :
    mvcc.ownWatcherGroup (GF := GF) wg W q ⊢
      ∃ v : watcherGroup, typedPointsto wg v (DFrac.own q) ∗
        mvcc.ownWatcherSet v.watchers' (domSet W) q ∗
        (typedPointsto wg v (DFrac.own q) -∗ mvcc.ownWatcherSet v.watchers' (domSet W) q -∗
          mvcc.ownWatcherGroup wg W q) := by
  iintro Hg
  unfold mvcc.ownWatcherGroup
  icases Hg with ⟨%km, %ws, %t, %KM, %L, Hg⟩
  iNamed Hg
  iexists _
  iframe Hwg Hws
  iintro Hwg Hws
  iexists km, ws, t, KM, L
  simp only [named]
  iframe Hwg Hws Hfixed Hkm Hivt Hranges
  ipureintro; exact HL

theorem mvcc.watchableStore.progressIfSync.wp_proof
    (hrev : mvcc.watchableStore.rev.spec (GF := GF) (hG := hG))
    (hsend : mvcc.watcher.send.spec (GF := GF) (hG := hG)) :
    mvcc.watchableStore.progressIfSync.spec (GF := GF) (hG := hG) := by
  intro s st γ m dq M rid
  wp_start as ⟨#Hws, Hm, #HM, HR⟩
  iunfold mvcc.watchReader at HR
  icases HR with ⟨Hrd, Hslot⟩
  ihave #Hws0 := Hws
  iunfold mvcc.isWatchableStore at Hws0
  iNamedSuffix Hws0 "W"
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_apply +noauto sync.RWMutex.wp_RLock $$ [$Hslot] as ⟨Hrl, HP⟩
  wp_auto_lc 1
  imod (lc_fupd_elim_later (E := ⊤) (P := mvcc.watchStoreInv s γ sync.rfrac)) $$ Hlc1 HP with HP
  wp_apply hrev $$ [$Hws $Hrd] as %r ⟨Hrd, -⟩
  (try wp_auto)
  ihave Hdx : (defer ↦ func.mk BAnon BAnon
      (Seq (App (Val #(methods (go.GoType.PointerType sync.RWMutex.ty) go!"RUnlock" #(mvcc.wsMuAddr s)))
        (Val #())) (App (Val #(func.mk BAnon BAnon (Val #()))) (Val #()))) : IProp GF) $$ [defer]
  · iexact defer
  iunfold mvcc.watchStoreInv at HP
  icases HP with ⟨%σ, HP⟩
  wp_func_lits
  wp_bind (App (App (Val (map.forRange _ _)) _) _)
  iapply wp_map_for_range (fun (keys : List w64) (i : Int) => iprop(∃ wv : Loc,
      "w" ∷ w_ptr ↦ wv ∗ "s" ∷ s_ptr ↦ s ∗ "responseWatchID" ∷ responseWatchID_ptr ↦ rid ∗
      "watchers" ∷ watchers_ptr ↦ m ∗ "Hrl" ∷ sync.ownRWMutexRLocked (mvcc.wsMuAddr s) (mvcc.watchStoreInv s γ) ∗
      "Hdx" ∷ (defer ↦ func.mk BAnon BAnon
        (Seq (App (Val #(methods (go.GoType.PointerType sync.RWMutex.ty) go!"RUnlock" #(mvcc.wsMuAddr s)))
          (Val #())) (App (Val #(func.mk BAnon BAnon (Val #()))) (Val #()))) : IProp GF) ∗
      "HP" ∷ mvcc.watchStoreBody s γ sync.rfrac σ ∗ "Hrd" ∷ mvcc.storeReader st γ.st ∗ "rev" ∷ rev_ptr ↦ r ∗
      "HΦ" ∷ (∀ b : Bool, m ↦${dq} M ∗ mvcc.watchReader s st γ -∗ Φ #b) ∗
      "%Hi" ∷ ⌜0 ≤ i ∧ ∀ (j : Nat) (id : w64) (w : Loc), j < i.toNat → keys[j]? = some id →
        M !! id = some w → (σ.Ws !! w).isSome⌝)) $$ Hm
  iintro %keys ⟨%Hkset, %Hklen, %Hknodup⟩
  isplitl [w s responseWatchID watchers Hrl Hdx HP Hrd rev HΦ]
  · iexists _
    simp only [named]
    iframe
    ipureintro
    exact ⟨Int.le_refl _, fun j _ _ hj => by simp at hj⟩
  isplitr
  · imodintro
    iintro %i %key %u ⟨%Hkey, %Hu⟩ HP'
    iNamed HP'
    wp_auto
    iunfold mvcc.watchStoreBody at HP
    iNamed HP
    icases mvcc.ownWatcherGroup_watchers_frac _ _ _ $$ Hsynced with ⟨%gv, Hwg, Hwset, Hgback⟩
    iunfold mvcc.ownWatcherSet at Hwset
    ihave %Hgnn := typedPointsto_not_null _ _ _ $$ Hwg
    icases typedPointsto_split _ _ _ $$ Hwg with Hwg
    simp only [TypedPointsto.typedPointstoDef]
    iNamed Hwg
    wp_auto
    wp_apply wp_map_lookup2 $$ [$Hwset] as Hwset
    ihave Hwg : typedPointsto (mvcc.syncedAddr s) gv (DFrac.own sync.rfrac) $$ [keyWatchers ranges watchers]
    · iapply typedPointsto_combine _ _ _ Hgnn
      simp only [TypedPointsto.typedPointstoDef]
      iframe
    ihave Hwset : mvcc.ownWatcherSet gv.watchers' (domSet σ.Ws) sync.rfrac $$ [Hwset]
    · iunfold mvcc.ownWatcherSet; iexact Hwset
    ihave Hsynced := Hgback $$ Hwg Hwset
    ihave HP : mvcc.watchStoreBody s γ sync.rfrac σ $$
        [Hσ Hwlog Hsynced Hunsynced Hvf Hvs Hvcap Hvbs Hst Hwo Hmeta Hwt Hmem]
    · iunfold mvcc.watchStoreBody; simp only [named]; iframe; iframe #; ipureintro; exact ⟨Hvlen, Hok⟩
    cases hsy : (σ.Ws !! u).isSome
    · simp only [Option.isSome_map, hsy]
      wp_auto
      unfold forMapPostcondition
      iright; iright; iright
      iexists _
      isplitr
      · ipureintro; rfl
      iintro Hm
      wp_auto
      wp_apply +noauto sync.RWMutex.wp_RUnlock $$ [$Hrl HP] as Hslot
      · iframe #; inext; iunfold mvcc.watchStoreInv; iexists σ; iexact HP
      wp_auto
      iapply HΦ
      iframe Hm
      iunfold mvcc.watchReader
      iframe
    · simp only [Option.isSome_map, hsy]
      ihave #Hiw := HM $$ %key %u %Hu
      simp only [mvcc.storeWatchParams]
      icases Hiw with ⟨%γw, %rr, %fcs, #Hmeta, #Hfix, %Hsr⟩
      ihave #Hfix' := Hfix
      iunfold mvcc.watcherFixed at Hfix'
      icases Hfix' with ⟨%Hnn, %ks, %es, -, -, -, -, #HsR, -, -⟩
      wp_auto
      wp_if_destruct
      · (try wp_auto)
        unfold forMapPostcondition
        iright; iright; iright
        iexists _
        isplitr
        · ipureintro; rfl
        iintro Hm
        wp_auto
        wp_apply +noauto sync.RWMutex.wp_RUnlock $$ [$Hrl HP] as Hslot
        · iframe #; inext; iunfold mvcc.watchStoreInv; iexists σ; iexact HP
        wp_auto
        iapply HΦ
        iframe Hm
        iunfold mvcc.watchReader
        iframe
      · (try wp_auto)
        unfold forMapPostcondition
        iright; ileft
        isplitr
        · ipureintro; rfl
        iexists _
        simp only [named]
        iframe
        ipureintro
        refine ⟨by omega, fun j id w hj hk hm => ?_⟩
        by_cases hji : j < i.toNat
        · exact Hi.2 j id w hji hk hm
        · have : j = i.toNat := by omega
          subst this
          rw [Hkey] at hk; cases hk
          rw [Hu] at hm; cases hm
          exact hsy
  iintro HP' Hm
  iNamed HP'
  have hall : ∀ id w, M !! id = some w → (σ.Ws !! w).isSome := by
    intro id w hw
    obtain ⟨j, hj⟩ := List.getElem?_of_mem ((Hkset id).2 (by rw [hw]; rfl))
    have hjl : j < keys.length := (List.getElem?_eq_some_iff.1 hj).1
    exact Hi.2 j id w (by omega) hj hw
  wp_auto
  wp_func_lits
  wp_bind (App (App (Val (map.forRange _ _)) _) _)
  iapply wp_map_for_range (fun (keys : List w64) (i : Int) => iprop(∃ wv : Loc,
      "w" ∷ w_ptr ↦ wv ∗ "responseWatchID" ∷ responseWatchID_ptr ↦ rid ∗
      "Hrl" ∷ sync.ownRWMutexRLocked (mvcc.wsMuAddr s) (mvcc.watchStoreInv s γ) ∗
      "Hdx" ∷ (defer ↦ func.mk BAnon BAnon
        (Seq (App (Val #(methods (go.GoType.PointerType sync.RWMutex.ty) go!"RUnlock" #(mvcc.wsMuAddr s)))
          (Val #())) (App (Val #(func.mk BAnon BAnon (Val #()))) (Val #()))) : IProp GF) ∗
      "HP" ∷ mvcc.watchStoreBody s γ sync.rfrac σ ∗ "Hrd" ∷ mvcc.storeReader st γ.st ∗ "rev" ∷ rev_ptr ↦ r ∗
      "HΦ" ∷ (∀ b : Bool, m ↦${dq} M ∗ mvcc.watchReader s st γ -∗ Φ #b))) $$ Hm
  iintro %keys2 -
  isplitl [w responseWatchID Hrl Hdx HP Hrd rev HΦ]
  · iexists _
    simp only [named]
    iframe
  isplitr
  · imodintro
    iintro %i %key %u ⟨%Hkey, %Hu⟩ HP'
    iNamed HP'
    wp_auto
    have hsy := hall key u Hu
    iunfold mvcc.watchStoreBody at HP
    iNamed HP
    have hlive : σ.live u := Or.inl hsy
    obtain ⟨st0, hst0⟩ := Option.isSome_iff_exists.1 (Hok.live_st u hlive)
    icases (BigSepM.bigSepM_lookup_acc hst0).1 $$ Hmem with ⟨Hmu, Hmem⟩
    icases (BigSepM.bigSepM_lookup_acc hst0).1 $$ Hst with ⟨Hwu, Hst⟩
    iunfold mvcc.memberRes at Hmu
    icases Hmu with ⟨%γw, %rr, %fcs, %HMw, #HmetaW, #HfixW, Hmu⟩
    rw [if_pos hlive]
    icases Hmu with ⟨#Hchan, #Hfok, %Hsr, %evsw, %d, %HE, Hevs, Hlv, #Hpop⟩
    iunfold mvcc.watcherOwn at Hwu
    icases Hwu with ⟨Hmin, Hvic, Hcomp, Hres, Hch⟩
    ihave #Hnil := ownSlice_nil (V := Loc) (GF := GF) DFrac.discard
    wp_apply (hsend γ u γw rr fcs st0.ch sync.rfrac sync.rfrac.half [] d _ [] [] DFrac.discard)
      $$ [$Hch $Hlv] as %b ⟨Hch, Hlv, -, -⟩
    · iframe #
      simp only [↓reduceIte, List.zip_nil_left]
      isplitr
      · itrivial
      isplitr
      · iapply BigSepL.bigSepL_nil.2; iempintro
      ipureintro
      simp
    ihave Hmu : mvcc.memberRes γ sync.rfrac σ u st0 $$ [Hevs Hlv]
    · iunfold mvcc.memberRes
      iexists γw, rr, fcs
      iframe %HMw
      iframe #
      rw [if_pos hlive]
      iframe #
      try (isplitr; · ipureintro; exact Hsr)
      try iexists evsw, d
      iframe
      try (ipureintro; exact HE)
    ihave Hmem := Hmem $$ Hmu
    ihave Hst := Hst $$ [Hmin Hvic Hcomp Hres Hch]
    · iunfold mvcc.watcherOwn; iframe
    ihave HP : mvcc.watchStoreBody s γ sync.rfrac σ $$
        [Hσ Hwlog Hsynced Hunsynced Hvf Hvs Hvcap Hvbs Hst Hwo Hmeta Hwt Hmem]
    · iunfold mvcc.watchStoreBody; simp only [named]; iframe; iframe #; ipureintro; exact ⟨Hvlen, Hok⟩
    (try wp_auto)
    unfold forMapPostcondition
    iright; iright; iright
    iexists _
    isplitr
    · ipureintro; rfl
    iintro Hm
    wp_auto
    wp_apply +noauto sync.RWMutex.wp_RUnlock $$ [$Hrl HP] as Hslot
    · iframe #; inext; iunfold mvcc.watchStoreInv; iexists σ; iexact HP
    wp_auto
    iapply HΦ
    iframe Hm
    iunfold mvcc.watchReader
    iframe
  iintro HP' Hm
  iNamed HP'
  wp_auto
  wp_apply +noauto sync.RWMutex.wp_RUnlock $$ [$Hrl HP] as Hslot
  · iframe #; inext; iunfold mvcc.watchStoreInv; iexists σ; iexact HP
  wp_auto
  iapply HΦ
  iframe Hm
  iunfold mvcc.watchReader
  iframe

end proof

end EtcdGrove
end Perennial
