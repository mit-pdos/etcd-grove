/-
Proof of `Spec/github_com/prometheus/client_golang/prometheus/Registry__Register.lean`: client_golang's
real `(*Registry).Register` (route (b), notes/prom-registry.md, "Step 2").
-/
module

public import Spec.github_com.prometheus.client_golang.prometheus.Registry__Register
public import Perennial.Proof.sync.Results

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode
open github_com.prometheus.client_golang.prometheus

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.prometheus.client_golang.prometheus.Assumptions]

theorem prometheus.Registry.Register.wp_proof :
    prometheus.Registry.Register.spec (GF := GF) (hG := hG) := by
  intro γ r c ps ds
  wp_start as ⟨#Hreg, #Hdesc, #Hps, Htoks, %Hok⟩
  iunfold prometheus.isRegistry at Hreg
  icases Hreg with ⟨%mC, %mD, %mN, #HfC, #HfD, #HfN, #Hguard⟩
  wp_auto
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_apply (wp_map_make1 (K := GoString) (V := w64) go.string go.uint64) as %mNN HmNN
  (try wp_auto)
  wp_apply (wp_map_make1 (K := w64) (V := Unit) go.uint64 (go.GoType.StructType [])) as %mND HmND
  (try wp_auto)
  wp_apply (chan.wp_make2 (V := Loc) (W64 10)) as %ch %γc ⟨#Hch, -, Hcown⟩
  · ipureintro; decide
  imod (start_spsc ch (fun (i : Int) (p : Loc) => iprop(⌜0 ≤ i ∧ ps[i.toNat]? = some p⌝))
    (fun l => iprop(⌜l = ps⌝)) γc) $$ Hch [Hcown] with ⟨%γs, #Hspsc, Hprod, Hcons⟩
  · iright; iexact Hcown
  (try wp_auto)
  ipersist descChan
  ipersist c
  wp_apply wp_fork $$ [Hprod]
  · wp_auto
    ihave HP : ([∗list] i ↦ p ∈ ps,
        iprop(⌜0 ≤ (([] : List Loc).length : Int) + (i : Int) ∧
          ps[(((([] : List Loc).length : Int) + (i : Int))).toNat]? = some p⌝) : IProp GF) $$ []
    · iapply (BigSepL.bigSepL_pure (PROP := IProp GF)).2
      ipureintro
      intro k x h
      simp only [List.length_nil, Int.natCast_zero, Int.zero_add, Int.toNat_natCast]
      exact ⟨by omega, h⟩
    wp_bind (App (Val #(methods c.ty _ c.v)) (Val #ch))
    iapply (wp_wand) $$ [Hprod HP]
    · iunfold prometheus.describes at Hdesc
      iapply Hdesc $$ %γs %ch %_ %_ %([] : List Loc) Hspsc HP Hprod
    iintro %v ⟨%hv, Hprod⟩
    subst hv
    wp_auto
    wp_apply (wp_spsc_close γs ch _ _ ([] ++ ps)) $$ [$Hspsc $Hprod]
    · ipureintro; simp
    itrivial
  wp_apply (lc := 2) sync.RWMutex.wp_Lock_guard $$ [$Hguard] as ⟨Hwl, HR⟩
  (try wp_auto)
  iunfold prometheus.regInv at HR
  icases HR with ⟨%C, %D, %N, HC, HD, HN, HK, %Hnames⟩
  icases prometheus.regKeysTok_absent_all γ (prometheus.regKeys C D) (prometheus.descKeys ds)
    $$ [HK Htoks] with ⟨%Habs, HK, Htoks⟩
  · iframe
  ihave %Hlen := BigSepL2.bigSepL2_length $$ Hps
  obtain ⟨Hne, Hlt, HnNd, HidNd, Hd⟩ := Hok
  -- the registry has none of the keys
  have hKn : ∀ k ∈ prometheus.descKeys ds, D !! k = none ∧ C !! k = none := by
    intro k hk
    have h := (GMap.lookup_union_None _ _ _).1 (Habs k hk)
    refine ⟨h.1, ?_⟩
    cases hc : C !! k with
    | none => rfl
    | some v =>
      have := h.2
      unfold GMap.domSet at this
      rw [GMap.lookup_fmap, hc] at this
      cases this
  ihave IH : (∃ (k : Nat) (dv : Loc),
      "Hcons" ∷ spscConsumer γs (ps.take k) ∗ "%Hk" ∷ ⌜k ≤ ps.length⌝ ∗
      "desc" ∷ desc_ptr ↦ dv ∗
      "HmND" ∷ mND ↦$ prometheus.insertList ((ds.take k).map (fun d => (d.id', ()))) ∅ ∗
      "HmNN" ∷ mNN ↦$ prometheus.insertList ((ds.take k).map (fun d => (d.fqName', d.dimHash'))) ∅ ∗
      "collectorID" ∷ collectorID_ptr ↦ prometheus.xorAll ((ds.take k).map (·.id')) : IProp GF)
    $$ [Hcons desc HmND HmNN collectorID]
  · iexists 0, _
    simp only [List.take_zero, List.map_nil]
    iframe
    ipureintro; exact Nat.zero_le _
  wp_for IH
  wp_apply (wp_spsc_receive_peek γs ch _ _ (ps.take k)) $$ [$Hspsc $Hcons] as %v %ok Hv
  cases ok
  · simp only [Bool.false_eq_true, ↓reduceIte]
    icases Hv with ⟨%Hall, Hcons, %hv⟩
    (try wp_auto)
    wp_for_post
    have hkl : k = ps.length := by
      have := congrArg List.length Hall; rw [List.length_take] at this; omega
    have hdt : ds.take k = ds := List.take_of_length_le (by omega)
    rw [hdt]
    have hND : ds.map (fun d => (d.id', ())) = (ds.map (·.id')).map (fun x => (x, ())) := by
      simp [List.map_map, Function.comp_def]
    rw [hND]
    have hsz : GMap.size (prometheus.insertList ((ds.map (·.id')).map (fun x => (x, ()))) ∅) =
        ds.length := by
      rw [GMap.size_eq_length _ (ds.map (·.id')) HidNd, List.length_map]
      intro x
      rw [prometheus.insertList_unit_lookup]
      split <;> simp_all
    wp_apply wp_map_len $$ HmND as HmND
    rw [hsz]
    have hpos : 0 < ds.length := List.length_pos_iff.mpr Hne
    have hlen0 : W64 (ds.length : Int) ≠ W64 0 := by
      intro h; have := congrArg uint.Z h; word
    rw [decide_eq_false hlen0]
    (try wp_auto)
    have hCn := (hKn _ (prometheus.descKeys_xor ds)).2
    wp_apply (wp_map_lookup2 (K := w64) (V := GoInterface) go.uint64 Collector.ty mC C _) $$ HC as HC
    rw [hCn]
    (try wp_auto)
    wp_apply (wp_mapInsert (K := w64) (V := GoInterface) go.uint64 mC C _ (GoInterface.ok c)) $$ HC as HC
    (try wp_auto)
    wp_func_lits
    wp_bind (App (App (Val (map.forRange _ _)) _) _)
    iapply wp_map_for_range (fun (keysD : List w64) (i : Int) => iprop(∃ (x : w64),
        "%Hi" ∷ ⌜0 ≤ i⌝ ∗ "hash" ∷ hash_ptr ↦ x ∗ "r" ∷ r_ptr ↦ r ∗
        "HD" ∷ mD ↦$ prometheus.insertList ((keysD.take i.toNat).map (fun x => (x, ()))) D)) $$ HmND
    iintro %keysD ⟨%HksetD, %HklenD, %HknodupD⟩
    isplitl [hash r HD]
    · iexists _
      simp only [named, Int.toNat_zero, List.take_zero, List.map_nil]
      iframe
      ipureintro; exact Int.le_refl _
    isplitr
    · imodintro
      iintro %i %key %u ⟨%Hkey, %Hu⟩ HP
      iNamed HP
      wp_auto
      wp_apply (wp_mapInsert (K := w64) (V := Unit) go.uint64 mD _ key ()) $$ HD as HD
      (try wp_auto)
      unfold forMapPostcondition
      iright; ileft
      isplitr
      · ipureintro; rfl
      iexists key
      simp only [named]
      have Htake : keysD.take (i + 1).toNat = keysD.take i.toNat ++ [key] := by
        rw [show (i + 1).toNat = i.toNat + 1 by omega]
        exact prometheus.take_succ_of_getElem? keysD _ key Hkey
      rw [Htake, List.map_append, List.map_cons, List.map_nil, prometheus.insertList_snoc]
      iframe
      ipureintro; omega
    iintro HP HmND
    iNamed HP
    rw [show (GMap.size _ : Int).toNat = keysD.length by rw [HklenD]; simp, List.take_length] at *
    (try wp_auto)
    wp_func_lits
    wp_bind (App (App (Val (map.forRange _ _)) _) _)
    iapply wp_map_for_range (fun (keysN : List GoString) (i : Int) => iprop(∃ (x : w64) (y : GoString),
        "%Hi" ∷ ⌜0 ≤ i⌝ ∗ "dimHash" ∷ dimHash_ptr ↦ x ∗ "name" ∷ name_ptr ↦ y ∗ "r" ∷ r_ptr ↦ r ∗
        "HN" ∷ mN ↦$ prometheus.insertList ((keysN.take i.toNat).map (fun n =>
          (n, ((prometheus.insertList (ds.map (fun d => (d.fqName', d.dimHash'))) ∅ !! n).getD 0)))) N))
      $$ HmNN
    iintro %keysN ⟨%HksetN, %HklenN, %HknodupN⟩
    isplitl [dimHash name r HN]
    · iexists _, _
      simp only [named, Int.toNat_zero, List.take_zero, List.map_nil]
      iframe
      ipureintro; exact Int.le_refl _
    isplitr
    · imodintro
      iintro %i %key %u ⟨%Hkey, %Hu⟩ HP
      iNamed HP
      wp_auto
      wp_apply (wp_mapInsert (K := GoString) (V := w64) go.string mN _ key u) $$ HN as HN
      (try wp_auto)
      unfold forMapPostcondition
      iright; ileft
      isplitr
      · ipureintro; rfl
      iexists u, key
      simp only [named]
      have Htake : keysN.take (i + 1).toNat = keysN.take i.toNat ++ [key] := by
        rw [show (i + 1).toNat = i.toNat + 1 by omega]
        exact prometheus.take_succ_of_getElem? keysN _ key Hkey
      rw [Htake, List.map_append, List.map_cons, List.map_nil, prometheus.insertList_snoc, Hu]
      iframe
      ipureintro; omega
    iintro HP HmNN
    iNamed HP
    rw [show (GMap.size _ : Int).toNat = keysN.length by rw [HklenN]; simp, List.take_length] at *
    (try wp_auto)
    -- the registry's predicate again, with the new keys, names and rights
    ihave HK' : prometheus.regKeysTok γ 1 (prometheus.regKeys
        (<[prometheus.xorAll (ds.map (·.id')) := GoInterface.ok c]> C)
        (prometheus.insertList (keysD.map (fun x => (x, ()))) D)) $$ [HK Htoks]
    · rw [← prometheus.regKeys_after C D ds keysD _ (fun x => by
        rw [HksetD x, prometheus.insertList_unit_lookup]; split <;> simp_all)]
      iapply prometheus.regKeysTok_insertKeys
      iframe
    ihave HR : prometheus.regInv γ mC mD mN 1 $$ [HC HD HN HK']
    · iunfold prometheus.regInv
      iexists _, _, _
      iframe
      ipureintro
      refine prometheus.namesOk_after D N ds keysD keysN _ (fun x => by
        rw [HksetD x, prometheus.insertList_unit_lookup]; split <;> simp_all)
        (fun n hn => (HksetN n).1 hn) (fun d hd => (Hd d hd).2.1) Hnames
    -- the deferred function: drain the (closed, drained) channel, then unlock
    ihave IH2 : (∃ l : List Loc, "Hc" ∷ spscConsumer γs l ∗ "%Hl" ∷ ⌜l = ps⌝ : IProp GF) $$ [Hcons]
    · iexists _; iframe; ipureintro; exact Hall
    wp_for IH2
    subst Hl
    wp_apply (wp_spsc_receive_peek γs ch _ _ l) $$ [$Hspsc $Hc] as %v2 %ok2 Hv2
    cases ok2
    · simp only [Bool.false_eq_true, ↓reduceIte]
      icases Hv2 with ⟨-, Hcons2, -⟩
      (try wp_auto)
      wp_for_post
      wp_apply sync.RWMutex.wp_Unlock_guard $$ [$Hwl $HR]
      (try wp_auto)
      iapply HΦ
      itrivial
    · simp only [↓reduceIte]
      icases Hv2 with ⟨%Hv2, -⟩
      exfalso
      obtain ⟨-, h⟩ := Hv2
      simp at h
  · simp only [↓reduceIte]
    icases Hv with ⟨%Hv, Hcons⟩
    obtain ⟨-, hpk⟩ := Hv
    rw [List.length_take, Nat.min_eq_left Hk, Int.toNat_natCast] at hpk
    have hk : k < ds.length := by
      rw [← Hlen]; exact (List.getElem?_eq_some_iff.mp hpk).1
    obtain ⟨d, hdk⟩ : ∃ d, ds[k]? = some d := ⟨ds[k], List.getElem?_eq_getElem hk⟩
    ihave #Hdv := BigSepL2.bigSepL2_lookup hpk hdk $$ Hps
    iStructNamed Hdv
    have hdmem : d ∈ ds := List.mem_of_getElem? hdk
    obtain ⟨herr, hid, hnb⟩ := Hd d hdmem
    have hDn : D !! d.id' = none :=
      (hKn _ (prometheus.descKeys_ids _ _ (List.mem_map_of_mem hdmem))).1
    rw [herr]
    (try wp_auto)
    wp_apply (wp_map_lookup2 (K := w64) (V := Unit) go.uint64 (go.StructType []) mD D d.id') $$ HD as HD
    rw [hDn]
    (try wp_auto)
    have hNDn : prometheus.insertList ((ds.take k).map (fun d => (d.id', ()))) ∅ !! d.id' = none := by
      rw [prometheus.insertList_lookup_notin]
      · rfl
      · simpa [List.map_map, Function.comp_def] using
          prometheus.nodup_take_notin (·.id') ds k d HidNd hdk
    have hNNn : prometheus.insertList ((ds.take k).map (fun d => (d.fqName', d.dimHash'))) ∅
        !! d.fqName' = none := by
      rw [prometheus.insertList_lookup_notin]
      · rfl
      · simpa [List.map_map, Function.comp_def] using
          prometheus.nodup_take_notin (·.fqName') ds k d HnNd hdk
    have hNn : N !! d.fqName' = none := by
      cases hn : N !! d.fqName' with
      | none => rfl
      | some h =>
        rcases Hnames _ _ hn with hb | hD
        · exact absurd hb hnb
        · rw [← hid, hDn] at hD; cases hD
    wp_apply (wp_map_lookup2 (K := w64) (V := Unit) go.uint64 (go.StructType []) mND _ d.id') $$ HmND as HmND
    rw [hNDn]
    (try wp_auto)
    wp_apply (wp_mapInsert (K := w64) (V := Unit) go.uint64 mND _ d.id' ()) $$ HmND as HmND
    (try wp_auto)
    wp_apply (wp_map_lookup2 (K := GoString) (V := w64) go.string go.uint64 mN N d.fqName') $$ HN as HN
    rw [hNn]
    (try wp_auto)
    wp_apply (wp_map_lookup2 (K := GoString) (V := w64) go.string go.uint64 mNN _ d.fqName') $$ HmNN as HmNN
    rw [hNNn]
    (try wp_auto)
    wp_apply (wp_mapInsert (K := GoString) (V := w64) go.string mNN _ d.fqName' d.dimHash') $$ HmNN as HmNN
    (try wp_auto)
    wp_for_post
    iframe
    iexists (k + 1), v
    rw [prometheus.take_succ_of_getElem? ps k v hpk, prometheus.take_succ_of_getElem? ds k d hdk]
    simp only [List.map_append, List.map_cons, List.map_nil, prometheus.insertList_snoc,
      prometheus.xorAll_snoc]
    iframe
    ipureintro; omega
end proof

end EtcdGrove
end Perennial
