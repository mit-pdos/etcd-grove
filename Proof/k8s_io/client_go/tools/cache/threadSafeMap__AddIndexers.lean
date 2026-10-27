/-
Proof of `Spec/k8s_io/client_go/tools/cache/threadSafeMap__AddIndexers.lean`. Lean-first.

The re-indexing loop (`for key, item := range c.items { for name := range newIndexers {
updateSingleIndex(name, nil, item, key) } }`): after the items `keys.take p` and, of the next
item, the new indexers `done`, each new indexer's index is exact for the items visited
(`newOk`); the old indexers' indices are untouched (no name clashes).
-/
module

public import Spec.k8s_io.client_go.tools.cache.threadSafeMap__AddIndexers
public import Spec.k8s_io.client_go.tools.cache.storeIndex__updateSingleIndex

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace cache

open Iris Iris.BI Iris.ProofMode k8s_io.client_go.tools.cache

section model
variable [FfiSyntax]

/-- The new indexers' indices: exact for the items `it'` for the indexers `done`, for `it` for the
others. -/
def newOk (fnsNew : GMap GoString Fn) (it it' : Items) (done : List GoString) (ix : Ix) : Prop :=
  ∀ n F, fnsNew !! n = some F → nameOk F (if n ∈ done then it' else it) (ixAt ix n)

theorem newOk_step {fnsNew : GMap GoString Fn} {it it' : Items} {done : List GoString}
    {ix ix' : Ix} {name key : GoString} {F : Fn}
    (h : newOk fnsNew it it' done ix) (hF : fnsNew !! name = some F) (hnd : name ∉ done)
    (hsame : ∀ k, k ≠ key → objAt it' k = objAt it k)
    (hother : ∀ n, n ≠ name → ix' !! n = ix !! n)
    (hupd : updNPost F (objAt it key) (objAt it' key) key (viewN (ixAt ix name))
      (viewN (ixAt ix' name))) :
    newOk fnsNew it it' (done ++ [name]) ix' := by
  intro n G hG
  by_cases hnn : n = name
  · subst hnn
    rw [hF] at hG; cases hG
    have h0 := h n F hF
    simp only [hnd, ↓reduceIte] at h0
    simp only [List.mem_append, List.mem_singleton, or_true, ↓reduceIte]
    exact nameOk_upd h0 hsame hupd
  · have hx : ixAt ix' n = ixAt ix n := by unfold ixAt; rw [hother n hnn]
    rw [hx]
    have hm : (n ∈ done ++ [name]) ↔ n ∈ done := by simp [hnn]
    simp only [hm]
    exact h n G hG

/-- Every name is `done`: exact for `it'`. -/
theorem newOk_all {fnsNew : GMap GoString Fn} {it it' : Items} {done : List GoString} {ix : Ix}
    (h : newOk fnsNew it it' done ix) (hall : ∀ n, (fnsNew !! n).isSome → n ∈ done) :
    newOk fnsNew it' it' [] ix := by
  intro n F hF
  have := h n F hF
  simp only [hall n (by rw [hF]; rfl), ↓reduceIte] at this
  simpa using this

/-- No index is exact for no items. -/
theorem nameOk_empty (F : Fn) : nameOk F ∅ ∅ := by
  intro v k
  unfold viewN inIdx objAt valsOf
  simp [GMap.mem_iff]

theorem fmap_union {V W : Type} (f : V → W) (a b : GMap GoString V) :
    GMap.fmap f (a ∪ b) = GMap.fmap f a ∪ GMap.fmap f b := by
  ext k; simp only [GMap.lookup_fmap, GMap.lookup_union]; cases a !! k <;> rfl

/-- **The store's indices after `AddIndexers`**: the old indexers' untouched, the new ones exact. -/
theorem ixOk_add {old fnsNew : GMap GoString Fn} {it : Items} {ix0 ix : Ix}
    (h0 : ixOk old it ix0) (hnc : ∀ n, (fnsNew !! n).isSome → old !! n = none)
    (hdom : ∀ n, n ∈ ix → n ∈ old ∨ n ∈ fnsNew)
    (hold : ∀ n, n ∉ fnsNew → ix !! n = ix0 !! n) (hnew : newOk fnsNew it it [] ix) :
    ixOk (fnsNew ∪ old) it ix := by
  refine ⟨fun n hn => ?_, fun n F hF => ?_⟩
  · show ((fnsNew ∪ old) !! n).isSome
    rw [GMap.lookup_union]
    rcases hdom n hn with h | h <;> rw [GMap.mem_iff] at h <;> cases hf : fnsNew !! n <;> simp_all
  · rw [GMap.lookup_union] at hF
    cases hf : fnsNew !! n with
    | some G =>
      rw [hf] at hF
      have hGF : G = F := Option.some.inj hF
      subst hGF
      have := hnew n G hf; simpa using this
    | none =>
      rw [hf] at hF; change old !! n = some F at hF
      have hx : ixAt ix n = ixAt ix0 n := by
        unfold ixAt; rw [hold n (by rw [GMap.mem_iff, hf]; simp)]
      rw [hx]; exact h0.2 n F hF

/-- The new indexers have no index before `AddIndexers` (no name clash). -/
theorem newOk_init {old fnsNew : GMap GoString Fn} {it : Items} {ix0 : Ix}
    (h0 : ixOk old it ix0) (hnc : ∀ n, (fnsNew !! n).isSome → old !! n = none) :
    newOk fnsNew ∅ ∅ [] ix0 := by
  intro n F hF
  simp only [List.not_mem_nil, ↓reduceIte]
  have hn : n ∉ ix0 := by
    intro hm
    have := h0.1 n hm
    rw [GMap.mem_iff, hnc n (by rw [hF]; rfl)] at this
    simp at this
  have : ixAt ix0 n = ∅ := by
    unfold ixAt; rw [GMap.mem_iff] at hn; cases h : ix0 !! n <;> simp_all
  rw [this]; exact nameOk_empty F

end model

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.tools.cache.Assumptions]

/-- The indexers' contracts of two maps without a common name. -/
theorem fnsOk_union (OK : GoInterface → IProp GF) (nfv fv : GMap GoString GoFunc)
    (fnsNew old : GMap GoString Fn) (hd : ∀ n, (nfv !! n).isSome → fv !! n = none) :
    fnsOk OK nfv fnsNew ∗ fnsOk OK fv old ⊢ fnsOk OK (nfv ∪ fv) (fnsNew ∪ old) := by
  iintro ⟨#H1, #H2⟩
  unfold fnsOk
  icases H1 with ⟨%h1, #H1⟩
  icases H2 with ⟨%h2, #H2⟩
  isplitr
  · ipureintro
    intro n
    simp only [GMap.mem_iff, GMap.lookup_union] at h1 h2 ⊢
    have a := h1 n; have b := h2 n
    cases e1 : fnsNew !! n <;> cases e2 : nfv !! n <;> simp_all
  iapply (BigSepM.bigSepM_intro (P := iprop(□ (([∗map] n ↦ f ∈ nfv, ∃ F, ⌜fnsNew !! n = some F⌝ ∗
      fnOk OK f F) ∗ ([∗map] n ↦ f ∈ fv, ∃ F, ⌜old !! n = some F⌝ ∗ fnOk OK f F))))
      (fun {k f} hk => ?_)) $$ [H1 H2]
  · iintro #⟨H1, H2⟩
    change ((nfv !! k).or (fv !! k)) = some f at hk
    cases e : nfv !! k with
    | some g =>
      rw [e] at hk
      have hgf : g = f := Option.some.inj hk
      subst hgf
      icases (BigSepM.bigSepM_lookup e) $$ H1 with ⟨%F, %hF, #Hf⟩
      iexists F
      iframe #
      ipureintro
      show (fnsNew !! k).or (old !! k) = some F
      rw [hF]; rfl
    | none =>
      rw [e] at hk
      change fv !! k = some f at hk
      icases (BigSepM.bigSepM_lookup hk) $$ H2 with ⟨%F, %hF, #Hf⟩
      iexists F
      iframe #
      ipureintro
      show (fnsNew !! k).or (old !! k) = some F
      have : fnsNew !! k = none := by
        have := (h1 k); rw [GMap.mem_iff, GMap.mem_iff, e] at this
        cases h : fnsNew !! k <;> simp_all
      rw [this]; exact hF
  · iframe #

end proof

section proof2
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.tools.cache.Assumptions]

theorem threadSafeMap.AddIndexers.wp_proof
    (wp_add : storeIndex.addIndexers.spec (GF := GF) (hG := hG))
    (wp_upd : storeIndex.updateSingleIndex.spec (GF := GF) (hG := hG)) :
    threadSafeMap.AddIndexers.spec (GF := GF) (hG := hG) := by
  intro c γ OK Fam nm dn nfv nids hsz
  iintro %Φ ⟨#Hpkg, #Hc, Hnm, #Hnfns⟩ HAU
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  iunfold isTS at Hc
  icases Hc with ⟨%mp, %g, #Hidx, #Him, #Hmp, #Hg, #Hgok, #Hguard⟩
  wp_method_call
  wp_call
  wp_auto
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_apply (lc := 2) sync.RWMutex.wp_Lock_guard $$ [$Hguard] as ⟨Hwl, HP⟩
  iunfold tsP at HP
  icases HP with ⟨%σ, %ph, Hst, Hgp, Hph, #Hpers, %Hok⟩
  iunfold tsPhys at Hph
  icases Hph with ⟨Hitems, Hil, Hrvf, Hind, Hix, Hfv⟩
  iunfold tsPers at Hpers
  icases Hpers with ⟨#Hfns, #Hits⟩
  iunfold fnsOk at Hfns Hnfns
  icases Hfns with ⟨%Hdom, #Hfs⟩
  icases Hnfns with ⟨%Hndom, #Hnfs⟩
  have hclash : nameClash ph.fv nfv ↔ nameClash σ.fnIds nids := by
    unfold nameClash
    constructor
    · rintro ⟨n, h1, h2⟩
      refine ⟨n, ?_, ?_⟩
      · have := (Hdom n).2 h1; unfold St.fns at this; simpa [GMap.mem_iff] using this
      · have := (Hndom n).2 h2; simpa [GMap.mem_iff] using this
    · rintro ⟨n, h1, h2⟩
      refine ⟨n, (Hdom n).1 ?_, (Hndom n).1 ?_⟩
      · unfold St.fns; simpa [GMap.mem_iff] using h1
      · simpa [GMap.mem_iff] using h2
  (try wp_auto)
  wp_apply (wp_add γ.idx γ.im nm DFrac.discard dn ph.fv nfv hsz) $$ [$Him $Hfv $Hnm]
    as %err ⟨-, Hnm, Hres⟩
  icases Hres with (⟨%Hc1, Hfv⟩ | ⟨%Hc1, Hfv⟩)
  · have hcl : nameClash σ.fnIds nids := hclash.1 Hc1.1
    cases err with
    | nil => exact absurd rfl Hc1.2
    | ok e =>
    (try wp_auto)
    imod storeSt_update γ σ (fun σ => σ.addIx nids) _ $$ [$Hst $HAU] with ⟨Hst, HK⟩
    have hσ : σ.addIx nids = σ := by simp [St.addIx, hcl]
    rw [hσ]
    wp_apply sync.RWMutex.wp_Unlock_guard $$ [$Hwl Hst Hgp Hitems Hil Hind Hix Hfv Hrvf]
    · inext
      iunfold tsP
      iexists σ, ph
      iframe
      isplitl
      · iunfold tsPhys; iframe
      isplitr
      · iunfold tsPers
        isplitr
        · iunfold fnsOk; iframe #; ipureintro; exact Hdom
        · iexact Hits
      · ipureintro; exact Hok
    (try wp_auto)
    iapply HK
    iframe
    ipureintro
    exact Or.inl ⟨hcl, fun h => by cases h⟩
  · obtain ⟨Hnc1, rfl⟩ := Hc1
    have hncl : ¬ nameClash σ.fnIds nids := fun h => Hnc1 (hclash.2 h)
    have hnc : ∀ n, ((GMap.fmap Fam nids) !! n).isSome → (St.fns Fam σ) !! n = none := by
      intro n hn
      unfold St.fns
      rw [GMap.lookup_fmap]
      cases h : σ.fnIds !! n with
      | none => rfl
      | some _ =>
        exfalso; apply hncl
        refine ⟨n, by rw [h]; rfl, ?_⟩
        rw [GMap.lookup_fmap] at hn; cases h' : nids !! n <;> simp_all
    have hdisj : ∀ n, (nfv !! n).isSome → ph.fv !! n = none := by
      intro n hn
      cases h : ph.fv !! n with
      | none => rfl
      | some _ => exact absurd ⟨n, by rw [h]; rfl, hn⟩ Hnc1
    (try wp_auto)
    wp_func_lits
    wp_bind (App (App (Val (map.forRange _ _)) _) _)
    iapply wp_map_for_range (fun (keys : List GoString) (p : Int) => iprop(∃ (x : GoInterface)
        (y : GoString) (ix : Ix),
        "%Hp" ∷ ⌜0 ≤ p⌝ ∗
        "%Hnew" ∷ ⌜newOk (GMap.fmap Fam nids) (restrictK σ.items (keys.take p.toNat))
          (restrictK σ.items (keys.take p.toNat)) [] ix⌝ ∗
        "%Hdomix" ∷ ⌜∀ n, n ∈ ix → n ∈ St.fns Fam σ ∨ n ∈ GMap.fmap Fam nids⌝ ∗
        "%Hold" ∷ ⌜∀ n, n ∉ GMap.fmap Fam nids → ix !! n = ph.ix !! n⌝ ∗
        "item" ∷ item_ptr ↦ x ∗ "key" ∷ key_ptr ↦ y ∗ "c" ∷ c_ptr ↦ c ∗
        "newIndexers" ∷ newIndexers_ptr ↦ nm ∗ "Hnm" ∷ nm ↦${dn} nfv ∗
        "Hind" ∷ structFieldRef storeIndex go!"indices" γ.idx ↦ ph.ip ∗
        "Hix" ∷ ownIx ph.ip (DFrac.own 1) ix ∗
        "Hfv" ∷ γ.im ↦$ (nfv ∪ ph.fv))) $$ Hil
    iintro %keys ⟨%Hkset, %Hklen, %Hknodup⟩
    isplitl [item key c newIndexers Hnm Hind Hix Hfv]
    · iexists _, _, ph.ix
      simp only [named]
      iframe
      ipureintro
      refine ⟨Int.le_refl _, ?_, ?_, ?_⟩
      · simp only [Int.toNat_zero, List.take_zero, restrictK_nil]
        exact newOk_init Hok hnc
      · intro n hn; exact Or.inl (Hok.1 n hn)
      · intro _ _; trivial
    isplitr
    · imodintro
      iintro %p %k %o ⟨%Hkey, %Ho⟩ HP
      iNamed HP
      ihave #Hoko : okNil OK o $$ []
      · iapply BigSepM.bigSepM_lookup Ho $$ Hits
      ihave #Hnil : okNil OK GoInterface.nil $$ []
      · iunfold okNil; ileft; ipureintro; rfl
      have hnd : k ∉ keys.take p.toNat := by
        intro hm
        have hd : k ∈ keys.drop p.toNat := by
          rw [List.mem_iff_getElem?]
          exact ⟨0, by rw [List.getElem?_drop]; simpa using Hkey⟩
        have hnod := List.nodup_append.1 ((List.take_append_drop p.toNat keys).symm ▸ Hknodup)
        exact hnod.2.2 k hm k hd rfl
      have Htake : keys.take (p + 1).toNat = keys.take p.toNat ++ [k] := by
        rw [show (p + 1).toNat = p.toNat + 1 by omega]
        rw [List.take_add_one, Hkey]; rfl
      have hold0 : objAt (restrictK σ.items (keys.take p.toNat)) k = GoInterface.nil := by
        rw [objAt_restrictK]; simp [hnd]
      have hnew0 : objAt (restrictK σ.items (keys.take p.toNat ++ [k])) k = o := by
        rw [objAt_restrictK, ite_eq_left_of_eq_true _ _ (by simp)]
        unfold objAt; rw [Ho]; rfl
      have hsame : ∀ k', k' ≠ k → objAt (restrictK σ.items (keys.take p.toNat ++ [k])) k' =
          objAt (restrictK σ.items (keys.take p.toNat)) k' := by
        intro k' hk'; rw [objAt_restrictK, objAt_restrictK]; simp [hk']
      (try wp_auto)
      wp_func_lits
      wp_bind (App (App (Val (map.forRange _ _)) _) _)
      iapply wp_map_for_range (fun (names : List GoString) (j : Int) => iprop(∃ (z : GoString)
          (ix : Ix),
          "%Hj" ∷ ⌜0 ≤ j⌝ ∗
          "%Hnew" ∷ ⌜newOk (GMap.fmap Fam nids) (restrictK σ.items (keys.take p.toNat))
            (restrictK σ.items (keys.take p.toNat ++ [k])) (names.take j.toNat) ix⌝ ∗
          "%Hdomix" ∷ ⌜∀ n, n ∈ ix → n ∈ St.fns Fam σ ∨ n ∈ GMap.fmap Fam nids⌝ ∗
          "%Hold" ∷ ⌜∀ n, n ∉ GMap.fmap Fam nids → ix !! n = ph.ix !! n⌝ ∗
          "name" ∷ name_ptr ↦ z ∗ "item" ∷ item_ptr ↦ o ∗ "key" ∷ key_ptr ↦ k ∗
          "c" ∷ c_ptr ↦ c ∗
          "Hind" ∷ structFieldRef storeIndex go!"indices" γ.idx ↦ ph.ip ∗
          "Hix" ∷ ownIx ph.ip (DFrac.own 1) ix ∗
          "Hfv" ∷ γ.im ↦$ (nfv ∪ ph.fv))) $$ Hnm
      iintro %names ⟨%Hnset, %Hnlen, %Hnnodup⟩
      isplitl [name item key c Hind Hix Hfv]
      · iexists _, ix
        simp only [named]
        iframe
        ipureintro
        refine ⟨Int.le_refl _, ?_, Hdomix, Hold⟩
        simp only [Int.toNat_zero, List.take_zero]
        intro n F hF
        simp only [List.not_mem_nil, ↓reduceIte]
        have := Hnew n F hF
        simpa using this
      isplitr
      · imodintro
        iintro %j %name %f ⟨%Hname, %Hf⟩ HQ
        iNamed HQ
        icases (BigSepM.bigSepM_lookup Hf) $$ Hnfs with ⟨%F, %hF, #HfOk⟩
        have hndn : name ∉ names.take j.toNat := by
          intro hm
          have hd : name ∈ names.drop j.toNat := by
            rw [List.mem_iff_getElem?]
            exact ⟨0, by rw [List.getElem?_drop]; simpa using Hname⟩
          have hnod := List.nodup_append.1 ((List.take_append_drop j.toNat names).symm ▸ Hnnodup)
          exact hnod.2.2 name hm name hd rfl
        have Htakej : names.take (j + 1).toNat = names.take j.toNat ++ [name] := by
          rw [show (j + 1).toNat = j.toNat + 1 by omega]
          rw [List.take_add_one, Hname]; rfl
        (try wp_auto)
        wp_apply (wp_upd γ.idx γ.im ph.ip DFrac.discard (DFrac.own 1) (nfv ∪ ph.fv) ix OK F f name k
            GoInterface.nil o) $$ [$Him $Hfv $HfOk $Hnil $Hoko $Hind $Hix]
          as ⟨%ix', -, Hfv, Hind, Hix, %Hupd⟩
        · ipureintro
          show (nfv !! name).or (ph.fv !! name) = some f
          rw [Hf]; rfl
        (try wp_auto)
        unfold forMapPostcondition
        iright; ileft
        isplitr
        · ipureintro; rfl
        iexists name, ix'
        simp only [named]
        iframe
        ipureintro
        refine ⟨by omega, ?_, ?_, ?_⟩
        · rw [Htakej]
          refine newOk_step Hnew hF hndn hsame Hupd.1 ?_
          rw [hold0, hnew0]; exact Hupd.2
        · intro n hn
          by_cases hnn : n = name
          · subst hnn; right; rw [GMap.mem_iff, hF]; rfl
          · apply Hdomix n; rw [GMap.mem_iff] at hn ⊢; rwa [Hupd.1 n hnn] at hn
        · intro n hn
          have hnn : n ≠ name := by rintro rfl; rw [GMap.mem_iff, hF] at hn; exact hn rfl
          rw [Hupd.1 n hnn]; exact Hold n hn
      · iintro HQ Hnm
        iNamed HQ
        rw [← Hnlen, Int.toNat_natCast, List.take_length] at Hnew
        (try wp_auto)
        unfold forMapPostcondition
        iright; ileft
        isplitr
        · ipureintro; rfl
        iexists o, k, ix
        simp only [named]
        iframe
        ipureintro
        refine ⟨by omega, ?_, Hdomix, Hold⟩
        rw [Htake]
        refine newOk_all Hnew (fun n hn => ?_)
        rw [Hnset]
        have := (Hndom n).1 (by rw [GMap.mem_iff]; exact hn)
        exact this
    · iintro HP Hil
      iNamed HP
      rw [← Hklen, Int.toNat_natCast, List.take_length,
        restrictK_all σ.items keys (fun k hk => (Hkset k).2 hk)] at Hnew
      (try wp_auto)
      imod storeSt_update γ σ (fun σ => σ.addIx nids) _ $$ [$Hst $HAU] with ⟨Hst, HK⟩
      have hσ : σ.addIx nids = { σ with fnIds := nids ∪ σ.fnIds } := by
        simp [St.addIx, hncl]
      rw [hσ]
      imod ghostVar_update (⟨ph.il, ph.ip, ix, nfv ∪ ph.fv⟩ : Ph) $$ Hgp with Hgp
      ihave #Hfns' : fnsOk OK ph.fv (St.fns Fam σ) $$ []
      · iunfold fnsOk; iframe #; ipureintro; exact Hdom
      ihave #Hnfns' : fnsOk OK nfv (GMap.fmap Fam nids) $$ []
      · iunfold fnsOk; iframe #; ipureintro; exact Hndom
      have hfns : St.fns Fam { σ with fnIds := nids ∪ σ.fnIds } =
          GMap.fmap Fam nids ∪ St.fns Fam σ := by
        unfold St.fns; exact fmap_union Fam nids σ.fnIds
      wp_apply sync.RWMutex.wp_Unlock_guard $$ [$Hwl Hst Hgp Hitems Hil Hind Hix Hfv Hrvf]
      · inext
        iunfold tsP
        iexists { σ with fnIds := nids ∪ σ.fnIds }, ⟨ph.il, ph.ip, ix, nfv ∪ ph.fv⟩
        iframe
        isplitl
        · iunfold tsPhys; iframe
        isplitr
        · iunfold tsPers
          rw [hfns]
          isplitr
          · iapply (fnsOk_union OK nfv ph.fv _ _ hdisj) $$ [$Hnfns' $Hfns']
          · iexact Hits
        · ipureintro
          rw [hfns]
          exact ixOk_add Hok hnc Hdomix Hold Hnew
      (try wp_auto)
      iapply HK
      iframe
      ipureintro
      exact Or.inr ⟨hncl, rfl⟩

end proof2

end cache
end EtcdGrove
end Perennial
