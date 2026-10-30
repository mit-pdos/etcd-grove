module
public import Spec.go_etcd_io.bbolt.internal.freelist.hashMap__Init
public import Spec.go_etcd_io.bbolt.internal.freelist.hashMap__addSpan
public import Spec.go_etcd_io.bbolt.internal.freelist.hashMap__freePageIds
public import Spec.go_etcd_io.bbolt.internal.freelist.shared__reindex
public import Spec.sort.SliceIsSorted

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt.internal.freelist

theorem init_mem_take {l : List w64} {n : Nat} {x : w64} :
    x ∈ l.take n ↔ ∃ m, m < n ∧ l[m]? = some x := by
  rw [List.mem_iff_getElem?]
  constructor
  · rintro ⟨m, hm⟩
    rw [List.getElem?_take] at hm
    split at hm
    · exact ⟨m, ‹_›, hm⟩
    · cases hm
  · rintro ⟨m, hm, hx⟩
    exact ⟨m, by rw [List.getElem?_take, if_pos hm]; exact hx⟩

/-- One run of `hashMap.Init`'s scan: the ids `xs[st..k)`, consecutive from `stv`, become a
span, the free ids so far `xs.take st` becoming `xs.take k`. -/
theorem init_step {cnt : w64} {sp bwm : GMap w64 w64} {sets : GMap w64 (GMap w64 Unit)}
    {xs : List w64} {st k : Nat} {stv sz : w64} (hok : hashOK cnt sp bwm sets (xs.take st))
    (hinc : PgidsIncr xs) (hst : st < k) (hk : k ≤ xs.length) (hstv : xs[st]? = some stv)
    (hsz : uint.Z sz = (k : Int) - st)
    (hcons : ∀ j, st ≤ j → j < k → uint.Z (xs.getD j 0) = uint.Z stv + (j - st))
    (hlen : xs.length < 2 ^ 63) :
    hashOK (cnt + sz) (<[stv := sz]> sp) (<[stv - W64 1 + sz := sz]> bwm)
      (<[sz := <[stv := ()]> ((sets !! sz).getD ∅)]> sets) (xs.take k) := by
  have hszn : uint.nat sz = k - st := by word
  have hlast := hcons (k - 1) (by omega) (by omega)
  have hlt : uint.Z (xs.getD (k - 1) 0) < 2 ^ 64 := by word
  -- the ids before `st` are below `stv`
  have hbelow : ∀ y ∈ xs.take st, uint.Z y < uint.Z stv := by
    intro y hy
    obtain ⟨m, hm, hy⟩ := init_mem_take.1 hy
    obtain ⟨h1, e1⟩ := List.getElem?_eq_some_iff.1 hy
    obtain ⟨h2, e2⟩ := List.getElem?_eq_some_iff.1 hstv
    have := List.pairwise_iff_getElem.1 hinc m st h1 h2 hm
    rw [e1, e2] at this; exact this
  refine hashOK_add hok (by word) (by omega) (fun x hx hm => ?_) ?_ (xs.take k)
    (List.Pairwise.sublist (List.take_sublist _ _) hinc) (fun x => ?_)
  · have := hbelow x hm; unfold inRun at hx; omega
  · rw [List.length_take, hszn]; omega
  · rw [init_mem_take, init_mem_take]
    constructor
    · rintro ⟨m, hm, hx⟩
      by_cases hms : m < st
      · exact Or.inl ⟨m, hms, hx⟩
      · right
        have := hcons m (by omega) hm
        rw [getD_of_some hx] at this
        unfold inRun; rw [hszn]; omega
    · rintro (⟨m, hm, hx⟩ | hx)
      · exact ⟨m, by omega, hx⟩
      · unfold inRun at hx; rw [hszn] at hx
        refine ⟨st + (uint.Z x - uint.Z stv).toNat, by omega, ?_⟩
        have hm := hcons (st + (uint.Z x - uint.Z stv).toNat) (by omega) (by omega)
        have hb : st + (uint.Z x - uint.Z stv).toNat < xs.length := by omega
        rw [getD_of_lt 0 hb] at hm
        rw [List.getElem?_eq_getElem hb]
        congr 1
        apply word.unsigned_inj
        omega

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.internal.freelist.Assumptions]

theorem init_hashOK_empty : hashOK (W64 0) ∅ ∅ ∅ [] := by
  refine ⟨⟨fun _ _ h => by simp at h, fun _ _ _ _ _ h => by simp at h⟩,
    ⟨List.Pairwise.nil, fun x => by simp⟩,
    ⟨fun k v => by simp, fun z s => by simp, fun z set h => by simp at h⟩, by simp, by simp⟩

theorem hashMap.Init.wp_proof (hSIS : sort.SliceIsSorted.spec (GF := GF) (hG := hG))
    (hAdd : hashMap.addSpan.spec (GF := GF) (hG := hG))
    (hRI : shared.reindex.spec (GF := GF) (hG := hG))
    (hFPI : hashMap.freePageIds.spec (GF := GF) (hG := hG)) :
    hashMap.Init.spec (GF := GF) (hG := hG) := by
  intro h s σ ids xs Hwf Hne
  wp_start as ⟨#Hhdl, Hs, Hown, Hids, Hcap⟩
  unfold ownHashMap ownHashPart hmRaw
  icases Hown with ⟨-, ⟨%cnt0, %sp0, %bwm0, %sets0, Hraw, -⟩, -⟩
  icases Hraw with ⟨%fm0, %fw0, %bw0, %FM0, Hraw⟩
  iNamed Hraw
  ihave %Hxl := ownSlice_len _ _ _ $$ Hids
  wp_auto
  wp_apply (wp_map_make1 (K := w64) (V := Loc)) as %fm Hfm'
  try wp_auto
  wp_apply (wp_map_make1 (K := w64) (V := w64)) as %fw Hfw'
  try wp_auto
  wp_apply (wp_map_make1 (K := w64) (V := w64)) as %bw Hbw'
  try wp_auto
  ihave Hse : ([∗map] _sz ↦ l;st ∈ (∅ : GMap w64 Loc);(∅ : GMap w64 (GMap w64 Unit)),
      (l ↦$ st : IProp GF)) $$ []
  · iapply (BigSepM2.bigSepM2_empty _).2; itrivial
  wp_if_destruct
  · -- no ids: `Init` returns before `reindex`
    have hx : xs = [] := by
      have : xs.length = 0 := by rw [Hxl.1, Hif]; rfl
      exact List.length_eq_zero_iff.1 this
    subst hx
    have hf : ∀ x ∈ σ.free, x ∈ σ.pendingIds := by
      rcases Hne with h | h
      · exact absurd rfl h
      · exact h
    try wp_auto
    iapply HΦ
    unfold ownSharedW
    icases Hs with ⟨%sv, %c, Hs, %Hok⟩
    isplitl [Hs]
    · iexists sv, c
      isplitl
      · iExactEq Hs; rfl
      ipureintro
      refine ⟨fun x => ?_, Hwf⟩
      rw [Hok.1 x]
      unfold FLState.cached FLState.allIds FLState.pendingIds
      simp only [List.mem_append, List.nil_append]
      constructor
      · rintro (hx | hx)
        · exact hf x hx
        · exact hx
      · exact Or.inr
    isplitl []
    · iexact Hpkg
    isplitl
    · iexists W64 0, ∅, ∅, ∅
      simp only [named]
      isplitl
      · iexists fm, fw, bw, ∅
        iframe
      · ipureintro; exact init_hashOK_empty
    · ipureintro; simp
  have Hlen : sint.nat ids.len = xs.length := Hxl.1.symm
  have Hincr : PgidsIncr xs := Hwf.2.2.1
  wp_apply (hSIS _ _ _ iprop(pgids_ptr ↦ ids ∗ ids ↦* xs)
    (fun i j => decide (uint.Z (xs.getD i 0) < uint.Z (xs.getD j 0)))) $$ [pgids Hids]
  · iframe
    imodintro
    iintro %i %j %Φ' %Hij ⟨pgids, Hids⟩ HΦ'
    wp_auto
    have Hbi : sint.nat i < xs.length := by word
    have Hbj : sint.nat j < xs.length := by word
    list_elem xs (sint.nat i) as ei
    list_elem xs (sint.nat j) as ej
    rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨Hij.1, Hij.2.1⟩)]
    wp_apply wp_load_slice_index ids (sint.Z i) xs _ ei Hij.1 $$ [Hids] with Hids
    · iframe; ipureintro; exact Hei_lookup
    try wp_auto
    rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨Hij.2.2.1, Hij.2.2.2⟩)]
    wp_apply wp_load_slice_index ids (sint.Z j) xs _ ej Hij.2.2.1 $$ [Hids] with Hids
    · iframe; ipureintro; exact Hej_lookup
    try wp_auto
    rw [← getD_of_some Hei_lookup, ← getD_of_some Hej_lookup]
    iapply HΦ'; iframe
  iintro %b ⟨%Hb, pgids, Hids⟩
  have Hbt : b = true := Hb.2 (fun i h1 h2 => by
    have := List.pairwise_iff_getElem.1 Hincr (i - 1) i (by omega) (by omega) (by omega)
    rw [getD_of_lt 0 (by omega), getD_of_lt 0 (by omega)]
    simp only [decide_eq_false_iff_not]; omega)
  subst Hbt
  try wp_auto
  have Hn0 : 0 < xs.length := by
    rcases Nat.eq_zero_or_pos xs.length with h0 | h0
    · exfalso; apply Hif; rw [h0] at Hlen; word
    · exact h0
  have HxlenB : xs.length < 2 ^ 63 := by
    have := Hwf.2.2.2.1; unfold FLState.allIds at this; simp only [List.length_append] at this; omega
  have Hge2 : ∀ x ∈ xs, 2 ≤ uint.Z x := fun x hx =>
    Hwf.2.1 x (by unfold FLState.allIds; exact List.mem_append_left _ hx)
  list_elem xs 0 as x0
  rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by word, by word⟩)]
  wp_apply wp_load_slice_index ids (sint.Z (W64 0)) xs _ x0 (by word) $$ [Hids] with Hids
  · iframe; ipureintro; exact Hx0_lookup
  try wp_auto
  ihave Hraw : hmRaw (GF := GF) h (W64 0) ∅ ∅ ∅ $$ [Hcnt Hfmf Hfwf Hbwf Hfm' Hfw' Hbw' Hse]
  · unfold hmRaw; iexists fm, fw, bw, ∅; simp only [named]; iframe
  ihave IH : iprop(∃ (k sz stv cnt : w64) (sp bwm : GMap w64 w64)
      (sets : GMap w64 (GMap w64 Unit)) (st : Nat),
      "i" ∷ i_ptr ↦ k ∗ "size" ∷ size_ptr ↦ sz ∗ "start" ∷ start_ptr ↦ stv ∗
      "Hraw" ∷ hmRaw h cnt sp bwm sets ∗ "Hids" ∷ ids ↦* xs ∗ "pgids" ∷ pgids_ptr ↦ ids ∗
      "f" ∷ f_ptr ↦ h ∗
      "%Hk" ∷ ⌜1 ≤ sint.Z k ∧ sint.Z k ≤ (xs.length : Int) ∧ st < sint.nat k ∧
        xs[st]? = some stv ∧ uint.Z sz = (sint.nat k : Int) - st ∧
        (∀ j, st ≤ j → j < sint.nat k → uint.Z (xs.getD j 0) = uint.Z stv + (j - st)) ∧
        hashOK cnt sp bwm sets (xs.take st)⌝) $$ [i size start Hraw Hids pgids f]
  · iexists W64 1, W64 1, x0, W64 0, ∅, ∅, ∅, 0
    iframe
    ipureintro
    refine ⟨by word, by word, by word, Hx0_lookup, by word, fun j h1 h2 => ?_, ?_⟩
    · have : j = 0 := by word
      subst this; rw [getD_of_some Hx0_lookup]; simp
    · simpa using init_hashOK_empty
  wp_for IH
  wp_if_destruct
  · obtain ⟨Hk1, Hk2, Hk3, Hk4, Hk5, Hk6, Hk7⟩ := Hk
    have Hif' : sint.Z k < sint.Z ids.len := by simpa using Hif
    have Hb : sint.nat k < xs.length := by word
    list_elem xs (sint.nat k) as e
    list_elem xs (sint.nat (k - W64 1)) as ep
    have Hkm : sint.nat (k - W64 1) = sint.nat k - 1 := by word
    have Hlt : uint.Z ep < uint.Z e := by
      have := List.pairwise_iff_getElem.1 Hincr (sint.nat (k - W64 1)) (sint.nat k)
        (by omega) (by omega) (by omega)
      rw [(List.getElem?_eq_some_iff.1 He_lookup).2, (List.getElem?_eq_some_iff.1 Hep_lookup).2]
        at this
      exact this
    have Hep : uint.Z ep = uint.Z stv + ((sint.nat k - 1 : Nat) - st) := by
      rw [← Hk6 (sint.nat k - 1) (by omega) (by omega), ← Hkm, getD_of_some Hep_lookup]
    rw [ite_eq_left_of_eq_true _ _ (eq_true (by word))]
    wp_apply wp_load_slice_index ids (sint.Z k) xs _ e (by word) $$ [Hids] with Hids
    · iframe; ipureintro; exact He_lookup
    try wp_auto
    rw [ite_eq_left_of_eq_true _ _ (eq_true (by word))]
    wp_apply wp_load_slice_index ids (sint.Z (k - W64 1)) xs _ ep (by word) $$ [Hids] with Hids
    · iframe; ipureintro; exact Hep_lookup
    try wp_auto
    have hk1 : sint.nat (k + W64 1) = sint.nat k + 1 := by word
    wp_if_destruct
    · -- the run goes on
      try wp_auto
      wp_for_post
      iframe
      iexists k + W64 1, sz + W64 1, stv, cnt, sp, bwm, sets, st
      iframe
      ipureintro
      rw [hk1]
      refine ⟨by word, by word, by omega, Hk4, by word, fun j h1 h2 => ?_, Hk7⟩
      by_cases hj : j < sint.nat k
      · exact Hk6 j h1 hj
      · have : j = sint.nat k := by omega
        subst this
        rw [getD_of_some He_lookup]
        have hl := Hlt
        have : uint.Z (ep + W64 1) = uint.Z ep + 1 := by word
        omega
    · -- a gap: the run is a span
      try wp_auto
      wp_apply (hAdd h cnt sp bwm sets stv sz) $$ [Hraw] as Hraw
      · iframe
      try wp_auto
      rw [ite_eq_left_of_eq_true _ _ (eq_true (by word))]
      wp_apply wp_load_slice_index ids (sint.Z k) xs _ e (by word) $$ [Hids] with Hids
      · iframe; ipureintro; exact He_lookup
      try wp_auto
      wp_for_post
      iframe
      iexists k + W64 1, W64 1, e, _, _, _, _, sint.nat k
      iframe
      ipureintro
      rw [hk1]
      refine ⟨by word, by word, by omega, He_lookup, by word, fun j h1 h2 => ?_,
        init_step Hk7 Hincr Hk3 (by omega) Hk4 Hk5 Hk6 HxlenB⟩
      have : j = sint.nat k := by omega
      subst this
      rw [getD_of_some He_lookup]; omega
  obtain ⟨Hk1, Hk2, Hk3, Hk4, Hk5, Hk6, Hk7⟩ := Hk
  have Hif' : ¬ sint.Z k < sint.Z ids.len := by simpa using Hif
  have Hkn : sint.nat k = xs.length := by word
  have Hstv2 : 2 ≤ uint.Z stv := Hge2 stv (List.mem_of_getElem? Hk4)
  rw [decide_eq_false (show ¬ sz = W64 0 by intro h0; subst h0; word)]
  try wp_auto
  rw [decide_eq_false (show ¬ stv = W64 0 by intro h0; subst h0; word)]
  try wp_auto
  wp_apply (hAdd h cnt sp bwm sets stv sz) $$ [Hraw] as Hraw
  · iframe
  have Hok' := init_step Hk7 Hincr Hk3 (by omega) Hk4 Hk5 Hk6 HxlenB
  rw [Hkn, List.take_length] at Hok'
  try wp_auto
  wp_method_call
  wp_call
  unfold hashHdl
  wp_auto
  unfold ownSharedW
  icases Hs with ⟨%sv, %c, Hs, %Hok⟩
  have hF : (hashMapImpl (GF := GF) h).FreePageIdsSpec := by
    intro s' free
    rw [hashMapImpl.ity, hashMapImpl.iv]
    iintro %Φ' Hown HΦ'
    iapply (hFPI h s' free) $$ [Hown]
    · iExactEq Hown; rfl
    inext
    iintro %r ⟨Hr, Hown⟩
    iapply HΦ'
    iframe
    iintro -
    iExactEq Hown; rfl
  ihave Hown : ownHashMap (GF := GF) h s xs $$ [Hraw]
  · unfold ownHashMap ownHashPart
    isplitl []; · iexact Hpkg
    isplitl
    · iexists _, _, _, _; iframe; ipureintro; exact Hok'
    · ipureintro; exact Hge2
  wp_bind (App (Val #(methods (go.GoType.PointerType shared.ty) go!"reindex" #s)) (Val #()))
  iapply (hRI (hashMapImpl h) s sv ({ σ with free := xs } : FLState) c hF) $$ [Hs Hown]
  · isplitl []; · iexact Hpkg
    isplitl []; · iExactEq Hhdl; rfl
    isplitl [Hs]; · iExactEq Hs; rfl
    iExactEq Hown; rfl
  inext
  iintro %sv' %c' ⟨Hs, %Hc', Hown⟩
  wp_auto
  iapply HΦ
  isplitl [Hs]
  · iexists sv', c'
    iframe
    ipureintro; exact ⟨Hc', Hwf⟩
  · iExactEq Hown; rfl
  done

end proof

end bbolt
end EtcdGrove
end Perennial
