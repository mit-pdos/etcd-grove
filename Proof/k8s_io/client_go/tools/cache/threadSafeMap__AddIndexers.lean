/-
Proof of `Spec/k8s_io/client_go/tools/cache/threadSafeMap__AddIndexers.lean`. Lean-first.

The re-indexing loop (`for key, item := range c.items { for name := range newIndexers {
updateSingleIndex(name, nil, item, key) } }`): the recorded index values `ivc` agree with the old
ones under the other names; under the new indexers they are recorded (`itemsIv`) for the items
visited (`keys.take p`) and none for the others; the indices stay exact for them throughout (a new
indexer starts with no index and no values, there being no name clash).
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

theorem mem_union {V : Type _} (a b : GMap GoString V) (n : GoString) :
    n ∈ a ∪ b ↔ n ∈ a ∨ n ∈ b := by
  simp only [GMap.mem_iff, GMap.lookup_union]
  cases a !! n <;> cases b !! n <;> simp

theorem fmap_union {V W : Type _} (f : V → W) (a b : GMap GoString V) :
    GMap.fmap f (a ∪ b) = GMap.fmap f a ∪ GMap.fmap f b := by
  ext k; simp only [GMap.lookup_fmap, GMap.lookup_union]; cases a !! k <;> rfl

/-- **The indices before re-indexing**: exact for the new indexers too (no index, no values). -/
theorem ixOk_add_init {R : Type _} {old new : GMap GoString R} {it : Items} {iv : IV} {ix : Ix}
    (h : ixOk old iv ix) (hwf : ivWf old it iv) :
    ixOk (new ∪ old) iv ix := by
  refine ⟨fun n hn => (mem_union _ _ n).2 (Or.inr (h.1 n hn)), fun n hn => ?_⟩
  by_cases ho : n ∈ old
  · exact h.2 n ho
  · have hnix : n ∉ ix := fun hm => ho (h.1 n hm)
    have hx : ixAt ix n = ∅ := by
      unfold ixAt; rw [GMap.mem_iff] at hnix; cases e : ix !! n <;> simp_all
    intro v k
    rw [hx]
    unfold inIdx
    rw [hwf k n (Or.inr ho)]
    unfold viewN
    simp [GMap.mem_iff]

/-- **The recorded values after re-indexing**: `ivWf` for the old and new indexers. -/
theorem ivWf_add {R : Type _} {old new : GMap GoString R} {it : Items} {iv ivc : IV}
    (hwf : ivWf old it iv) (hold : ∀ n k, n ∉ new → ivAt ivc n k = ivAt iv n k)
    (hnew : ∀ n k, n ∈ new → objAt it k = interface.nil → ivAt ivc n k = []) :
    ivWf (new ∪ old) it ivc := by
  intro k n h
  by_cases hn : n ∈ new
  · rcases h with h | h
    · exact hnew n k hn h
    · exact absurd ((mem_union _ _ n).2 (Or.inl hn)) h
  · rw [hold n k hn]
    refine hwf k n ?_
    rcases h with h | h
    · exact Or.inl h
    · exact Or.inr (fun ho => h ((mem_union _ _ n).2 (Or.inr ho)))

end model

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.tools.cache.Assumptions]

/-- The indexers' contracts of two maps without a common name. -/
theorem fnsOk_union (OK : GoInterface → IProp GF) (nfv fv : GMap GoString GoFunc)
    (fnsNew old : GMap GoString (Fn GF)) (hd : ∀ n, (nfv !! n).isSome → fv !! n = none) :
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

open Iris.ProofMode in
/-- The recorded values of the old and new indexers. -/
theorem itemsIv_union (new old : GMap GoString (Fn GF)) (it : Items) (iv ivc : IV)
    (hold : ∀ n k, n ∉ new → ivAt ivc n k = ivAt iv n k) :
    itemsIv new it ivc ∗ itemsIv old it iv ⊢ itemsIv (new ∪ old) it ivc := by
  iintro ⟨#H1, #H2⟩
  unfold itemsIv
  iapply (BigSepM.bigSepM_forall (Φ := fun k o => valsOk (new ∪ old) o (ivOf ivc k))).2
  iintro %k %o %hk
  ihave #Hv1 := (BigSepM.bigSepM_lookup hk) $$ H1
  ihave #Hv2 := (BigSepM.bigSepM_lookup hk) $$ H2
  unfold valsOk
  iapply (BigSepM.bigSepM_forall (Φ := fun n F => objVals F o (vsAt (ivOf ivc k) n))).2
  iintro %n %F %hn
  change (new ∪ old) !! n = some F at hn
  rw [GMap.lookup_union] at hn
  cases e : new !! n with
  | some G =>
    rw [e] at hn
    cases hn
    iapply (BigSepM.bigSepM_lookup e) $$ Hv1
  | none =>
    rw [e] at hn
    change old !! n = some F at hn
    have hnn : n ∉ new := by rw [GMap.mem_iff, e]; simp
    have := hold n k hnn
    unfold ivAt at this
    rw [this]
    iapply (BigSepM.bigSepM_lookup hn) $$ Hv2

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
  icases HP with ⟨%σ, %ph, %iv, Hst, Hgp, Hph, #Hpers, %Hok⟩
  iunfold tsPhys at Hph
  icases Hph with ⟨Hitems, Hil, Hrvf, Hind, Hix, Hfv⟩
  iunfold tsPers at Hpers
  icases Hpers with ⟨#Hfns, #Hits, #Hiv⟩
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
      iexists σ, ph, iv
      iframe
      isplitl
      · iunfold tsPhys; iframe
      isplitr
      · iunfold tsPers
        isplitr
        · iunfold fnsOk; iframe #; ipureintro; exact Hdom
        · iframe #
      · ipureintro; exact Hok
    (try wp_auto)
    iapply HK
    iframe
    ipureintro
    exact Or.inl ⟨hcl, fun h => by cases h⟩
  · obtain ⟨Hnc1, rfl⟩ := Hc1
    have hncl : ¬ nameClash σ.fnIds nids := fun h => Hnc1 (hclash.2 h)
    have hnc : ∀ n, n ∈ GMap.fmap Fam nids → n ∉ St.fns Fam σ := by
      intro n hn ho
      apply hncl
      refine ⟨n, ?_, ?_⟩
      · unfold St.fns at ho; rw [GMap.mem_iff, GMap.lookup_fmap] at ho
        cases h : σ.fnIds !! n <;> simp_all
      · rw [GMap.mem_iff, GMap.lookup_fmap] at hn
        cases h : nids !! n <;> simp_all
    have hdisj : ∀ n, (nfv !! n).isSome → ph.fv !! n = none := by
      intro n hn
      cases h : ph.fv !! n with
      | none => rfl
      | some _ => exact absurd ⟨n, by rw [h]; rfl, hn⟩ Hnc1
    (try wp_auto)
    wp_func_lits
    wp_bind (App (App (Val (map.forRange _ _)) _) _)
    iapply wp_map_for_range (fun (keys : List GoString) (p : Int) => iprop(∃ (x : GoInterface)
        (y : GoString) (ixc : Ix) (ivc : IV),
        "%Hp" ∷ ⌜0 ≤ p⌝ ∗
        "%Hokc" ∷ ⌜ixOk (GMap.fmap Fam nids ∪ St.fns Fam σ) ivc ixc⌝ ∗
        "%Holdv" ∷ ⌜∀ n k, n ∉ GMap.fmap Fam nids → ivAt ivc n k = ivAt iv n k⌝ ∗
        "%Hnewv" ∷ ⌜∀ n k, n ∈ GMap.fmap Fam nids →
          objAt (restrictK σ.items (keys.take p.toNat)) k = GoInterface.nil → ivAt ivc n k = []⌝ ∗
        "#Hivc" ∷ itemsIv (GMap.fmap Fam nids) (restrictK σ.items (keys.take p.toNat)) ivc ∗
        "item" ∷ item_ptr ↦ x ∗ "key" ∷ key_ptr ↦ y ∗ "c" ∷ c_ptr ↦ c ∗
        "newIndexers" ∷ newIndexers_ptr ↦ nm ∗ "Hnm" ∷ nm ↦${dn} nfv ∗
        "Hind" ∷ structFieldRef storeIndex go!"indices" γ.idx ↦ ph.ip ∗
        "Hix" ∷ ownIx ph.ip (DFrac.own 1) ixc ∗
        "Hfv" ∷ γ.im ↦$ (nfv ∪ ph.fv))) $$ Hil
    iintro %keys ⟨%Hkset, %Hklen, %Hknodup⟩
    isplitl [item key c newIndexers Hnm Hind Hix Hfv]
    · iexists _, _, ph.ix, iv
      simp only [named, Int.toNat_zero, List.take_zero, restrictK_nil]
      iframe
      isplitr
      · ipureintro; exact Int.le_refl _
      isplitr
      · ipureintro; exact ixOk_add_init Hok.1 Hok.2
      isplitr
      · ipureintro; intro _ _ _; trivial
      isplitr
      · ipureintro
        intro n k hn _
        exact Hok.2 k n (Or.inr (hnc n hn))
      · iunfold itemsIv; iapply BigSepM.bigSepM_empty.2; itrivial
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
      (try wp_auto)
      wp_func_lits
      wp_bind (App (App (Val (map.forRange _ _)) _) _)
      iapply wp_map_for_range (fun (names : List GoString) (j : Int) => iprop(∃ (z : GoString)
          (ixj : Ix) (vsc : Vals),
          "%Hj" ∷ ⌜0 ≤ j⌝ ∗
          "%Hokj" ∷ ⌜ixOk (GMap.fmap Fam nids ∪ St.fns Fam σ) (<[k := vsc]> ivc) ixj⌝ ∗
          "%Hrest" ∷ ⌜∀ n, n ∉ names.take j.toNat → vsAt vsc n = ivAt ivc n k⌝ ∗
          "#Hdone" ∷ □ (∀ (n : GoString) (F : Fn GF),
            ⌜(GMap.fmap Fam nids) !! n = some F ∧ n ∈ names.take j.toNat⌝ -∗
            objVals F o (vsAt vsc n)) ∗
          "name" ∷ name_ptr ↦ z ∗ "item" ∷ item_ptr ↦ o ∗ "key" ∷ key_ptr ↦ k ∗
          "c" ∷ c_ptr ↦ c ∗
          "Hind" ∷ structFieldRef storeIndex go!"indices" γ.idx ↦ ph.ip ∗
          "Hix" ∷ ownIx ph.ip (DFrac.own 1) ixj ∗
          "Hfv" ∷ γ.im ↦$ (nfv ∪ ph.fv))) $$ Hnm
      iintro %names ⟨%Hnset, %Hnlen, %Hnnodup⟩
      isplitl [name item key c Hind Hix Hfv]
      · iexists _, ixc, ivOf ivc k
        simp only [named]
        iframe
        isplitr
        · ipureintro; exact Int.le_refl _
        isplitr
        · ipureintro; exact ixOk_congr Hokc (fun n _ k' => ivAt_insert_self ivc k n k')
        isplitr
        · ipureintro; exact fun n _ => rfl
        · imodintro
          iintro %n %F %h
          simp at h
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
        have hnamenew : name ∈ GMap.fmap Fam nids := by rw [GMap.mem_iff, hF]; rfl
        have hovs : vsAt vsc name = [] := by
          rw [Hrest name hndn]; exact Hnewv name k hnamenew hold0
        ihave #Hovs : objVals F GoInterface.nil (vsAt vsc name) $$ []
        · rw [hovs]; iunfold objVals; ileft; ipureintro; exact ⟨rfl, rfl⟩
        (try wp_auto)
        wp_apply (wp_upd γ.idx γ.im ph.ip DFrac.discard (DFrac.own 1) (nfv ∪ ph.fv) ixj OK F f
            name k GoInterface.nil o (vsAt vsc name))
          $$ [$Him $Hfv $HfOk $Hnil $Hoko $Hovs $Hind $Hix]
          as ⟨%ix', %nvs, -, Hfv, Hind, Hix, #Hnvs, %Hupd⟩
        · ipureintro
          show (nfv !! name).or (ph.fv !! name) = some f
          rw [Hf]; rfl
        (try wp_auto)
        unfold forMapPostcondition
        iright; ileft
        isplitr
        · ipureintro; rfl
        iexists name, ix', <[name := nvs]> vsc
        simp only [named]
        iframe
        isplitr
        · ipureintro; omega
        isplitr
        · ipureintro
          exact ixOk_step Hokj ((mem_union _ _ name).2 (Or.inl hnamenew)) Hupd.1 Hupd.2
        isplitr
        · ipureintro
          intro n hn
          rw [Htakej] at hn
          have hn1 : n ≠ name := by intro h; subst h; simp at hn
          rw [vsAt_insert]; simp only [hn1, ↓reduceIte]
          exact Hrest n (fun h => hn (List.mem_append_left _ h))
        · imodintro
          iintro %n %G ⟨%hG, %hn⟩
          rw [Htakej] at hn
          rw [vsAt_insert]
          by_cases hnn : n = name
          · subst hnn
            rw [hF] at hG; cases hG
            simp only [↓reduceIte]
            iexact Hnvs
          · simp only [hnn, ↓reduceIte]
            have hn' : n ∈ names.take j.toNat := by simpa [hnn] using hn
            iapply Hdone $$ %n %G
            ipureintro; exact ⟨hG, hn'⟩
      · iintro HQ Hnm
        iNamed HQ
        have hallj : names.take (GMap.size nfv : Int).toNat = names := by
          rw [Int.toNat_natCast, ← Hnlen, List.take_length]
        rw [hallj] at Hrest
        ihave #Hvsc : valsOk (GMap.fmap Fam nids) o vsc $$ []
        · iunfold valsOk
          iapply (BigSepM.bigSepM_intro (P := iprop(□ (∀ (n : GoString) (F : Fn GF),
              ⌜(GMap.fmap Fam nids) !! n = some F ∧ n ∈ names.take (GMap.size nfv : Int).toNat⌝ -∗
                objVals F o (vsAt vsc n))))
              (fun {n F} hn => ?_)) $$ [Hdone]
          · iintro #H
            iapply H $$ %n %F
            ipureintro
            refine ⟨hn, ?_⟩
            rw [hallj, Hnset]
            have := (Hndom n).1 (by rw [GMap.mem_iff, show (GMap.fmap Fam nids) !! n = some F from hn]; rfl)
            rw [GMap.mem_iff] at this
            exact this
          · iexact Hdone
        ihave %hvnil := valsOk_nil_pure _ o vsc $$ Hvsc
        (try wp_auto)
        unfold forMapPostcondition
        iright; ileft
        isplitr
        · ipureintro; rfl
        iexists o, k, ixj, <[k := vsc]> ivc
        simp only [named]
        rw [Htake, restrictK_snoc σ.items _ k o Ho]
        iframe
        isplitr
        · ipureintro; omega
        isplitr
        · ipureintro; exact Hokj
        isplitr
        · ipureintro
          intro n k' hn
          rw [ivAt_insert]
          by_cases hkk : k' = k
          · simp only [hkk, ↓reduceIte]
            rw [Hrest n ?_, Holdv n k hn]
            intro hm
            apply hn
            have := (Hnset n).1 hm
            exact (Hndom n).2 (by rw [GMap.mem_iff]; exact this)
          · simp only [hkk, ↓reduceIte]; exact Holdv n k' hn
        isplitr
        · ipureintro
          intro n k' hn hk'
          rw [ivAt_insert]
          rw [objAt_insert] at hk'
          by_cases hkk : k' = k
          · simp only [hkk, ↓reduceIte] at hk' ⊢
            exact hvnil hk' n hn
          · simp only [hkk, ↓reduceIte] at hk' ⊢
            exact Hnewv n k' hn hk'
        · iapply itemsIv_insert $$ [$Hivc $Hvsc]
    · iintro HP Hil
      iNamed HP
      have hall : restrictK σ.items (keys.take (GMap.size σ.items : Int).toNat) = σ.items := by
        rw [Int.toNat_natCast, ← Hklen, List.take_length]
        exact restrictK_all σ.items keys (fun k hk => (Hkset k).2 hk)
      rw [hall] at Hnewv
      have hH : itemsIv (GF := GF) (GMap.fmap Fam nids)
          (restrictK σ.items (keys.take (GMap.size σ.items : Int).toNat)) ivc ⊢
          itemsIv (GMap.fmap Fam nids) σ.items ivc := by rw [hall]
      ihave #Hivn := hH $$ Hivc
      (try wp_auto)
      imod storeSt_update γ σ (fun σ => σ.addIx nids) _ $$ [$Hst $HAU] with ⟨Hst, HK⟩
      have hσ : σ.addIx nids = { σ with fnIds := nids ∪ σ.fnIds } := by
        simp [St.addIx, hncl]
      rw [hσ]
      imod ghostVar_update (⟨ph.il, ph.ip, ixc, nfv ∪ ph.fv⟩ : Ph) $$ Hgp with Hgp
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
        iexists { σ with fnIds := nids ∪ σ.fnIds }, ⟨ph.il, ph.ip, ixc, nfv ∪ ph.fv⟩, ivc
        iframe
        isplitl
        · iunfold tsPhys; iframe
        isplitr
        · iunfold tsPers
          rw [hfns]
          isplitr
          · iapply (fnsOk_union OK nfv ph.fv _ _ hdisj) $$ [$Hnfns' $Hfns']
          isplitr
          · iexact Hits
          · iapply (itemsIv_union _ _ σ.items iv ivc Holdv) $$ [$Hivn $Hiv]
        · ipureintro
          rw [hfns]
          exact ⟨Hokc, ivWf_add Hok.2 Holdv Hnewv⟩
      (try wp_auto)
      iapply HK
      iframe
      ipureintro
      exact Or.inr ⟨hncl, rfl⟩

end proof2

end cache
end EtcdGrove
end Perennial
