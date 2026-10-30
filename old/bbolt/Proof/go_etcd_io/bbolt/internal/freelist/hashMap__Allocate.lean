module
public import Spec.go_etcd_io.bbolt.internal.freelist.hashMap__Allocate
public import Spec.go_etcd_io.bbolt.internal.freelist.hashMap__delSpan
public import Spec.go_etcd_io.bbolt.internal.freelist.hashMap__addSpan

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt.internal.freelist

/-- The span at `pid` deleted (`delSpan`): its ids are no longer free. -/
theorem alloc_del {cnt : w64} {sp bwm : GMap w64 w64} {sets : GMap w64 (GMap w64 Unit)}
    {free : List w64} (h : hashOK cnt sp bwm sets free) {pid sz : w64} (hs : sp !! pid = some sz) :
    hashOK (cnt - sz) (GMap.delete pid sp) (GMap.delete (pid + (sz - W64 1)) bwm)
      (setsDel sets sz pid) (free.filter (fun x => decide ¬ inRun pid (uint.nat sz) x)) :=
  hashOK_del h hs _ (h.2.1.1.filter _) (fun x => by simp [List.mem_filter])

/-- The first `k ≤ sz` ids of the span at `pid` are free (and do not wrap around). -/
theorem alloc_can {cnt : w64} {sp bwm : GMap w64 w64} {sets : GMap w64 (GMap w64 Unit)}
    {free : List w64} (h : hashOK cnt sp bwm sets free) {pid sz : w64} (hs : sp !! pid = some sz)
    {k : Nat} (hk : k ≤ uint.nat sz) :
    uint.Z pid + k ≤ 2 ^ 64 ∧ ∀ x, inRun pid k x → x ∈ free := by
  have := (h.1.1 pid sz hs).2
  have e : (uint.nat sz : Int) = uint.Z sz := by word
  refine ⟨by omega, fun x hx => span_mem h.2.1 hs ?_⟩
  unfold inRun at hx ⊢; omega

/-- The span at `pid` of `sz > n` ids deleted and its last `sz - n` ids added back
(`Allocate`'s larger span): its first `n` ids are no longer free. -/
theorem alloc_split {cnt : w64} {sp bwm : GMap w64 w64} {sets : GMap w64 (GMap w64 Unit)}
    {free : List w64} (h : hashOK cnt sp bwm sets free) {pid sz n : w64}
    (hs : sp !! pid = some sz) (hn1 : 1 ≤ uint.Z n) (hlt : uint.Z n < uint.Z sz) :
    hashOK (cnt - sz + (sz - n)) (<[pid + n := sz - n]> (GMap.delete pid sp))
      (<[pid + n - W64 1 + (sz - n) := sz - n]> (GMap.delete (pid + (sz - W64 1)) bwm))
      (<[sz - n := <[pid + n := ()]> (((setsDel sets sz pid) !! (sz - n)).getD ∅)]>
        (setsDel sets sz pid))
      (free.filter (fun x => decide ¬ inRun pid (uint.nat n) x)) := by
  have hd := alloc_del h hs
  have hnw := (h.1.1 pid sz hs).2
  have hlen1 := filter_not_length h.2.1.1.nodup (st := pid) (n := uint.nat sz) (by word)
    (fun x hx => span_mem h.2.1 hs hx)
  have hle := span_le_len h.1 h.2.1 hs
  have hsz1 : 1 ≤ uint.Z (sz - n) := by word
  have hnw' : uint.Z (pid + n) + uint.Z (sz - n) ≤ 2 ^ 64 := by word
  refine hashOK_add hd hsz1 hnw' (fun x hx hm => ?_) ?_ _ (h.2.1.1.filter _) (fun x => ?_)
  · clear hd hlen1
    rw [List.mem_filter] at hm
    simp only [decide_eq_true_iff] at hm
    apply hm.2
    unfold inRun at hx ⊢; constructor <;> word
  · have e : (free.filter (fun x => decide ¬ inRun pid (uint.nat sz) x)).length =
        free.length - uint.nat sz := by
      rw [← hlen1]; simp only [decide_not]
    rw [e]; have := h.2.2.2.2; word
  · clear hd hlen1
    simp only [List.mem_filter, decide_eq_true_iff]
    constructor
    · rintro ⟨hx, hn⟩
      by_cases hr : inRun pid (uint.nat sz) x
      · right; unfold inRun at hr hn ⊢; constructor <;> word
      · left; exact ⟨hx, hr⟩
    · rintro (⟨hx, hr⟩ | hr)
      · refine ⟨hx, fun h' => hr ?_⟩
        unfold inRun at h' ⊢; constructor <;> word
      · have hin : inRun pid (uint.nat sz) x := by unfold inRun at hr ⊢; constructor <;> word
        refine ⟨span_mem h.2.1 hs hin, fun h' => ?_⟩
        unfold inRun at h' hr; word

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.internal.freelist.Assumptions]

/-- A `for range` over a map that looks for a binding satisfying `Q`: on the others the body
continues (keeping `P`); on the first it meets satisfying `Q` (in whatever order the range
visits the keys) it returns; if there is none, the loop ends. -/
theorem alloc_range_find {K V : Type} [ZeroVal K] [DecidableEq K] [ZeroVal V] [go.IntoValInj K]
    [TypedPointsto (GF := GF) K] {key_type elem_type : go.GoType}
    [IntoValTyped (GF := GF) K key_type]
    (P : IProp GF) (Q : K → V → Prop) (body : GoFunc) (mref : Loc) (m : GMap K V)
    (Φ : val → IProp GF) :
    (mref ↦$ m : IProp GF) -∗ P -∗
    □ (∀ (key : K) (v : V), ⌜m !! key = some v ∧ ¬ Q key v⌝ -∗ P -∗
        WP (App (App (Val #body) (Val #key)) (Val #v)) {{ bv, ⌜bv = continueVal⌝ ∗ P }}) -∗
    ((∀ (key : K) (v : V), ⌜m !! key = some v ∧ Q key v⌝ -∗ P -∗ mref ↦$ m -∗
        WP (App (App (Val #body) (Val #key)) (Val #v))
          {{ bv, ∃ v', ⌜bv = returnVal v'⌝ ∗ Φ bv }}) ∧
     (⌜∀ k v, m !! k = some v → ¬ Q k v⌝ -∗ P -∗ mref ↦$ m -∗ Φ executeVal)) -∗
    WP (App (App (Val (map.forRange key_type elem_type)) (Val #mref)) (Val #body)) {{ Φ }} := by
  iintro Hm HP #Hcont Hk
  iapply (wp_map_for_range_gen (fun keys i m' => iprop(
      ⌜m' = m ∧ ∀ j k v, j < i → keys[j]? = some k → m !! k = some v → ¬ Q k v⌝ ∗ P ∗
      ((∀ (key : K) (v : V), ⌜m !! key = some v ∧ Q key v⌝ -∗ P -∗ mref ↦$ m -∗
        WP (App (App (Val #body) (Val #key)) (Val #v))
          {{ bv, ∃ v', ⌜bv = returnVal v'⌝ ∗ Φ bv }}) ∧
       (⌜∀ k v, m !! k = some v → ¬ Q k v⌝ -∗ P -∗ mref ↦$ m -∗ Φ executeVal))))
    body key_type elem_type mref m (DFrac.own 1) Φ) $$ Hm
  iintro %keys %Hkeys
  obtain ⟨Hmem, Hsize, Hnd⟩ := Hkeys
  isplitl [HP Hk]
  · isplitr
    · ipureintro; exact ⟨rfl, fun j _ _ h => absurd h (Nat.not_lt_zero j)⟩
    iframe
  isplitr
  · imodintro
    iintro %i %key %v %m' %Hkv ⟨%Hpre, HP, Hk⟩ Hm
    obtain ⟨Hki, Hv⟩ := Hkv
    obtain ⟨rfl, Hpre⟩ := Hpre
    by_cases hq : Q key v
    · icases Hk with ⟨Hk, -⟩
      iapply wp_wand $$ (Hk $$ %key %v %(⟨Hv, hq⟩) HP Hm)
      iintro %bv ⟨%v', %Hbv, HΦ⟩
      unfold forMapPostcondition
      iright; iright; iright
      iexists v'
      isplitr
      · ipureintro; exact Hbv
      iexact HΦ
    · iapply wp_wand $$ (Hcont $$ %key %v %(⟨Hv, hq⟩) HP)
      iintro %bv ⟨%Hbv, HP⟩
      unfold forMapPostcondition
      ileft
      isplitr
      · ipureintro; exact Hbv
      iexists m'
      iframe
      ipureintro
      refine ⟨rfl, fun j k w hj hk hw => ?_⟩
      rcases Nat.lt_or_ge j i with h | h
      · exact Hpre j k w h hk hw
      · have : j = i := by omega
        subst this
        rw [Hki] at hk; cases hk
        rw [Hv] at hw; cases hw
        exact hq
  isplitr
  · imodintro
    iintro %i %key %m' %Hkn ⟨%Hpre, HP, Hk⟩
    obtain ⟨Hki, Hn⟩ := Hkn
    obtain ⟨rfl, -⟩ := Hpre
    have := (Hmem key).1 (List.mem_of_getElem? Hki)
    rw [Hn] at this; cases this
  · iintro %m' ⟨%Hpre, HP, Hk⟩ Hm
    obtain ⟨rfl, Hpre⟩ := Hpre
    icases Hk with ⟨-, Hk⟩
    have Hnone : ∀ k v, m' !! k = some v → ¬ Q k v := by
      intro k v hv
      obtain ⟨j, hk⟩ := List.mem_iff_getElem?.1 ((Hmem k).2 (by simp [hv]))
      exact Hpre j k v (List.getElem?_eq_some_iff.1 hk).1 hk hv
    iapply Hk $$ %Hnone HP Hm



theorem hashMap.Allocate.wp_proof (hDel : hashMap.delSpan.spec (GF := GF) (hG := hG))
    (hAdd : hashMap.addSpan.spec (GF := GF) (hG := hG)) :
    hashMap.Allocate.spec (GF := GF) (hG := hG) := by
  intro h s σ txid n Hn
  wp_start as Hfl
  iunfold ownFL at Hfl
  isimp only [hashMapImpl] at Hfl
  iunfold hashHdl, ownHashMap, ownHashPart, ownShared at Hfl
  icases Hfl with ⟨#Hhdl, ⟨%sv, %c, Hsh, %Hok⟩, ⟨-, ⟨%cnt, %sp, %bwm, %sets, Hraw, %Hhok⟩, %Hge⟩⟩
  obtain ⟨Hc, Hwf⟩ := Hok
  iunfold hmRaw at Hraw
  icases Hraw with ⟨%fm, %fw, %bw, %FM, Hraw⟩
  iNamed Hraw
  ihave %Hdom := BigSepM2.bigSepM2_lookup_iff $$ Hsets
  wp_auto
  wp_if_destruct
  · exfalso; exact absurd Hn (by decide)
  try wp_auto
  wp_apply wp_map_lookup2 $$ [Hfm] as Hfm
  · iexact Hfm
  try wp_auto
  wp_if_destruct
  · -- a span of exactly `n` ids
    obtain ⟨l, hl⟩ := Option.isSome_iff_exists.1 Hif
    obtain ⟨set, hset⟩ := Option.isSome_iff_exists.1 ((Hdom n).1
      (by simp only [show Std.get? FM n = some l from hl, Option.isSome_some]))
    have hset' : sets !! n = some set := hset
    rw [hl, Option.getD_some]
    icases BigSepM2.bigSepM2_lookup_acc (show Std.get? FM n = some l from hl) hset $$ Hsets
      with ⟨Hl, Hsets⟩
    try wp_auto
    wp_func_lits
    wp_bind (App (App (Val (map.forRange _ _)) _) _)
    iapply (alloc_range_find (K := w64) (V := Unit) iprop(emp) (fun _ _ => True) _ l set) $$ Hl
    · itrivial
    · imodintro; iintro %key %v %Hkv; exact absurd trivial Hkv.2
    isplit
    · iintro %key %v %Hkv - Hl
      obtain ⟨Hkv, -⟩ := Hkv
      have Hsp : sp !! key = some n := (Hhok.2.2.1.2.1 n key).1 ⟨set, hset', by simp [Hkv]⟩
      ihave Hsets := Hsets $$ Hl
      try wp_auto
      wp_apply (hDel h cnt sp bwm sets σ.free key n Hhok Hsp)
        $$ [Hcnt Hfmf Hfwf Hbwf Hfm Hsets Hfw Hbw] as Hraw
      · unfold hmRaw; iexists fm, fw, bw, FM; simp only [named]; iframe
      have Hok' := alloc_del Hhok Hsp
      iunfold ownSharedC at Hsh
      icases Hsh with ⟨%pp, Hsh⟩
      iNamed Hsh
      try wp_auto
      wp_apply wp_mapInsert $$ Hallocs as Hallocs
      try wp_auto
      have Hcan := alloc_can Hhok Hsp (k := uint.nat n) (Nat.le_refl _)
      ihave IH3 : iprop(∃ (j : w64) (m' : GMap w64 Unit),
          "i" ∷ i_ptr ↦ j ∗ "Hcache" ∷ sv.cache' ↦$ m' ∗
          "%Hj" ∷ ⌜uint.Z j ≤ uint.Z n ∧
            ∀ x, (m' !! x).isSome ↔ (c !! x).isSome ∧ ¬ inRun key (uint.nat j) x⌝) $$ [i Hcache]
      · iexists W64 0, c
        iframe
        ipureintro
        refine ⟨by word, fun x => ?_⟩
        simp only [inRun, show uint.nat (W64 0) = 0 from rfl]
        constructor
        · intro h; exact ⟨h, by omega⟩
        · exact fun h => h.1
      wp_for IH3
      wp_if_destruct
      · try wp_auto
        wp_apply wp_mapDelete $$ Hcache as Hcache
        wp_for_post
        iframe
        iexists j + W64 1, _
        iframe
        ipureintro
        have hj1 : uint.nat (j + W64 1) = uint.nat j + 1 := by word
        refine ⟨by word, fun x => ?_⟩
        rw [hj1, inRun_succ Hcan.1 (by word), GMap.lookup_delete_iff]
        by_cases hx : key + j = x
        · subst hx; simp
        · simp only [hx, if_false, Hj.2 x]
          constructor
          · rintro ⟨h1, h2⟩
            exact ⟨h1, by rintro (h | h); exact h2 h; exact hx h.symm⟩
          · rintro ⟨h1, h2⟩
            exact ⟨h1, fun h => h2 (Or.inl h)⟩
      have Hjn : uint.nat j = uint.nat n := by word
      rw [Hjn] at Hj
      try wp_auto
      iexists #key
      isplitr
      · ipureintro; rfl
      try wp_auto
      have Hnn : uint.nat n = sint.nat n := by word
      rw [Hnn] at Hj Hcan Hok'
      have HcanS : σ.canAllocate key (sint.nat n) := Hcan
      iapply HΦ
      iright
      isplitr
      · ipureintro; exact HcanS
      unfold ownFL; simp only [hashMapImpl]
      unfold hashHdl ownHashMap ownHashPart ownShared ownSharedC
      iframe Hhdl
      isplitl [Hs Hro Hro_cap Hallocs Hcache Hpending Hpds]
      · iexists sv, m'
        isplitl
        · iexists pp
          simp only [FLState.allocate, named]
          iframe
          ipureintro; exact Hiface
        · ipureintro
          exact ⟨allocate_cacheOK Hwf Hc HcanS Hj.2, allocate_WF Hwf txid key (sint.nat n)⟩
      isplitl []
      · iexact Hpkg
      isplitl
      · iexists _, _, _, _
        simp only [named, FLState.allocate]
        iframe
        ipureintro; exact Hok'
      · ipureintro
        intro x hx
        simp only [FLState.allocate, List.mem_filter] at hx
        exact Hge x hx.1
    · iintro %Hnone
      obtain ⟨k, hk⟩ := Hhok.2.2.1.2.2 n set hset'
      obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 hk
      exact (Hnone k v hv trivial).elim
  -- no span of exactly `n` ids: a longer one
  have hFMn : FM !! n = none := by
    cases h' : FM !! n with
    | none => rfl
    | some _ => rw [h'] at Hif; simp at Hif
  have hsn : sets !! n = none := by
    have := Hdom n
    simp only [show Std.get? FM n = FM !! n from rfl, hFMn, Option.isSome_none] at this
    cases h' : sets !! n with
    | none => rfl
    | some _ => simp [show Std.get? sets n = sets !! n from rfl, h'] at this
  try wp_auto
  wp_func_lits
  wp_bind (App (App (Val (map.forRange _ _)) _) _)
  iapply (alloc_range_find (K := w64) (V := Loc)
    iprop(∃ (bmv : Loc) (szv : w64), bm_ptr ↦ bmv ∗ size_ptr ↦ szv ∗ n_ptr ↦ n)
    (fun size _ => uint.Z n ≤ uint.Z size) _ fm FM) $$ Hfm [bm size n]
  · iexists _, _; iframe
  · imodintro
    iintro %key %v %Hkv ⟨%bmv, %szv, bm, size, n⟩
    obtain ⟨-, hq⟩ := Hkv
    try wp_auto
    rw [decide_eq_true (show uint.Z key < uint.Z n by omega)]
    try wp_auto
    isplitr
    · ipureintro; rfl
    iexists _, _; iframe
  isplit
  · iintro %key %v %Hkv ⟨%bmv, %szv, bm, size, n⟩ Hfm
    obtain ⟨Hkv, hq⟩ := Hkv
    obtain ⟨set, hset⟩ := Option.isSome_iff_exists.1 ((Hdom key).1
      (by simp only [show Std.get? FM key = some v from Hkv, Option.isSome_some]))
    have hset' : sets !! key = some set := hset
    have hne : key ≠ n := by rintro rfl; rw [hFMn] at Hkv; cases Hkv
    have hlt : uint.Z n < uint.Z key := by
      have : uint.Z key ≠ uint.Z n := fun e => hne (by word)
      omega
    icases BigSepM2.bigSepM2_lookup_acc (show Std.get? FM key = some v from Hkv) hset $$ Hsets
      with ⟨Hl, Hsets⟩
    try wp_auto
    rw [decide_eq_false (show ¬ uint.Z key < uint.Z n by omega)]
    try wp_auto
    wp_func_lits
    wp_bind (App (App (Val (map.forRange _ _)) _) _)
    iapply (alloc_range_find (K := w64) (V := Unit) iprop(emp) (fun _ _ => True) _ v set) $$ Hl
    · itrivial
    · imodintro; iintro %k %w %Hkw; exact absurd trivial Hkw.2
    isplit
    · iintro %pid %w %Hpw - Hl
      obtain ⟨Hpw, -⟩ := Hpw
      have Hsp : sp !! pid = some key := (Hhok.2.2.1.2.1 key pid).1 ⟨set, hset', by simp [Hpw]⟩
      ihave Hsets := Hsets $$ Hl
      try wp_auto
      wp_apply (hDel h cnt sp bwm sets σ.free pid key Hhok Hsp)
        $$ [Hcnt Hfmf Hfwf Hbwf Hfm Hsets Hfw Hbw] as Hraw
      · unfold hmRaw; iexists fm, fw, bw, FM; simp only [named]; iframe
      iunfold ownSharedC at Hsh
      icases Hsh with ⟨%pp, Hsh⟩
      iNamed Hsh
      try wp_auto
      wp_apply wp_mapInsert $$ Hallocs as Hallocs
      try wp_auto
      wp_apply (hAdd h (cnt - key) (GMap.delete pid sp) (GMap.delete (pid + (key - W64 1)) bwm)
        (setsDel sets key pid) (pid + n) (key - n)) $$ [Hraw] as Hraw
      · iexact Hraw
      have Hok' := alloc_split Hhok Hsp (by word) hlt
      try wp_auto
      have Hcan := alloc_can Hhok Hsp (k := uint.nat n) (by word)
      ihave IH3 : iprop(∃ (j : w64) (m' : GMap w64 Unit),
          "i" ∷ i_ptr ↦ j ∗ "Hcache" ∷ sv.cache' ↦$ m' ∗
          "%Hj" ∷ ⌜uint.Z j ≤ uint.Z n ∧
            ∀ x, (m' !! x).isSome ↔ (c !! x).isSome ∧ ¬ inRun pid (uint.nat j) x⌝) $$ [i Hcache]
      · iexists W64 0, c
        iframe
        ipureintro
        refine ⟨by word, fun x => ?_⟩
        simp only [inRun, show uint.nat (W64 0) = 0 from rfl]
        constructor
        · intro h; exact ⟨h, by omega⟩
        · exact fun h => h.1
      wp_for IH3
      wp_if_destruct
      · try wp_auto
        wp_apply wp_mapDelete $$ Hcache as Hcache
        wp_for_post
        iframe
        iexists j + W64 1, _
        iframe
        ipureintro
        have hj1 : uint.nat (j + W64 1) = uint.nat j + 1 := by word
        refine ⟨by word, fun x => ?_⟩
        rw [hj1, inRun_succ Hcan.1 (by word), GMap.lookup_delete_iff]
        by_cases hx : pid + j = x
        · subst hx; simp
        · simp only [hx, if_false, Hj.2 x]
          constructor
          · rintro ⟨h1, h2⟩
            exact ⟨h1, by rintro (h | h); exact h2 h; exact hx h.symm⟩
          · rintro ⟨h1, h2⟩
            exact ⟨h1, fun h => h2 (Or.inl h)⟩
      have Hjn : uint.nat j = uint.nat n := by word
      rw [Hjn] at Hj
      try wp_auto
      iexists #pid
      isplitr
      · ipureintro; rfl
      try wp_auto
      iexists #pid
      isplitr
      · ipureintro; rfl
      try wp_auto
      have Hnn : uint.nat n = sint.nat n := by word
      rw [Hnn] at Hj Hcan Hok'
      have HcanS : σ.canAllocate pid (sint.nat n) := Hcan
      iapply HΦ
      iright
      isplitr
      · ipureintro; exact HcanS
      unfold ownFL; simp only [hashMapImpl]
      unfold hashHdl ownHashMap ownHashPart ownShared ownSharedC
      iframe Hhdl
      isplitl [Hs Hro Hro_cap Hallocs Hcache Hpending Hpds]
      · iexists sv, m'
        isplitl
        · iexists pp
          simp only [FLState.allocate, named]
          iframe
          ipureintro; exact Hiface
        · ipureintro
          exact ⟨allocate_cacheOK Hwf Hc HcanS Hj.2, allocate_WF Hwf txid pid (sint.nat n)⟩
      isplitl []
      · iexact Hpkg
      isplitl
      · iexists _, _, _, _
        simp only [named, FLState.allocate]
        iframe
        ipureintro; exact Hok'
      · ipureintro
        intro x hx
        simp only [FLState.allocate, List.mem_filter] at hx
        exact Hge x hx.1
    · iintro %Hnone
      obtain ⟨k, hk⟩ := Hhok.2.2.1.2.2 key set hset'
      obtain ⟨w, hw⟩ := Option.isSome_iff_exists.1 hk
      exact (Hnone k w hw trivial).elim
  · iintro %Hnone ⟨%bmv, %szv, bm, size, n⟩ Hfm
    try wp_auto
    iapply HΦ
    ileft
    isplitr
    · ipureintro; rfl
    unfold ownFL; simp only [hashMapImpl]
    unfold hashHdl ownHashMap ownHashPart ownShared
    iframe Hhdl
    isplitl [Hsh]
    · iexists sv, c; iframe; ipureintro; exact ⟨Hc, Hwf⟩
    isplitl []
    · iexact Hpkg
    isplitl
    · iexists cnt, sp, bwm, sets
      isplitl
      · unfold hmRaw; iexists fm, fw, bw, FM; simp only [named]; iframe
      · ipureintro; exact Hhok
    · ipureintro; exact Hge

end proof

end bbolt
end EtcdGrove
end Perennial
