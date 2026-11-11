/-
`hashMap.Allocate` (U2 internal, the contract's `AllocateSpec` at `hashImpl h`; ported from the old proof).
-/
module

public import Proof.go_etcd_io.bbolt.internal.freelist.Impl.hashMap.hashMap__addSpan
public import Proof.go_etcd_io.bbolt.internal.freelist.Impl.hashMap.hashMap__delSpan
public import Proof.go_etcd_io.bbolt.internal.freelist.Impl.hashMap.hashMap__Init
public import Proof.go_etcd_io.bbolt.internal.freelist.Lemmas.ArrayLemmas

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs
namespace internal
namespace freelist

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt.internal.freelist

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.internal.freelist.Assumptions]

/-- The span at `pid` deleted (`delSpan`): its ids are no longer free. -/
theorem alloc_del {cnt : w64} {sp bwm : GMap w64 w64} {sets : GMap w64 (GMap w64 Unit)}
    {free : List w64} (h : hashOK cnt sp bwm sets free) {pid sz : w64} (hs : sp !! pid = some sz) :
    hashOK (cnt - sz) (GMap.delete pid sp) (GMap.delete (pid + (sz - W64 1)) bwm)
      (setsDel sets sz pid) (free.filter (fun x => decide ¬ inRun pid (sz.toNat) x)) :=
  hashOK_del h hs _ (h.2.1.1.filter _) (fun x => by simp [List.mem_filter])

/-- The first `k ≤ sz` ids of the span at `pid` are free (and do not wrap around). -/
theorem alloc_can {cnt : w64} {sp bwm : GMap w64 w64} {sets : GMap w64 (GMap w64 Unit)}
    {free : List w64} (h : hashOK cnt sp bwm sets free) {pid sz : w64} (hs : sp !! pid = some sz)
    {k : Nat} (hk : k ≤ sz.toNat) :
    pid.toNat + k ≤ 2 ^ 64 ∧ ∀ x, inRun pid k x → x ∈ free := by
  have := (h.1.1 pid sz hs).2
  have e : (sz.toNat : Int) = sz.toNat := by word
  refine ⟨by omega, fun x hx => span_mem h.2.1 hs ?_⟩
  unfold inRun at hx ⊢; omega

/-- The span at `pid` of `sz > n` ids deleted and its last `sz - n` ids added back
(`Allocate`'s larger span): its first `n` ids are no longer free. -/
theorem alloc_split {cnt : w64} {sp bwm : GMap w64 w64} {sets : GMap w64 (GMap w64 Unit)}
    {free : List w64} (h : hashOK cnt sp bwm sets free) {pid sz n : w64}
    (hs : sp !! pid = some sz) (hn1 : 1 ≤ n.toNat) (hlt : n.toNat < sz.toNat) :
    hashOK (cnt - sz + (sz - n)) (<[pid + n := sz - n]> (GMap.delete pid sp))
      (<[pid + n - W64 1 + (sz - n) := sz - n]> (GMap.delete (pid + (sz - W64 1)) bwm))
      (<[sz - n := <[pid + n := ()]> (((setsDel sets sz pid) !! (sz - n)).getD ∅)]>
        (setsDel sets sz pid))
      (free.filter (fun x => decide ¬ inRun pid (n.toNat) x)) := by
  have hd := alloc_del h hs
  have hnw := (h.1.1 pid sz hs).2
  have hlen1 := filter_not_length h.2.1.1.nodup (st := pid) (n := sz.toNat) (by word)
    (fun x hx => span_mem h.2.1 hs hx)
  have hle := span_le_len h.1 h.2.1 hs
  have hsz1 : 1 ≤ (sz - n).toNat := by word
  have hnw' : (pid + n).toNat + (sz - n).toNat ≤ 2 ^ 64 := by word
  refine hashOK_add hd hsz1 hnw' (fun x hx hm => ?_) ?_ _ (h.2.1.1.filter _) (fun x => ?_)
  · clear hd hlen1
    rw [List.mem_filter] at hm
    simp only [decide_eq_true_iff] at hm
    apply hm.2
    unfold inRun at hx ⊢; constructor <;> word
  · have e : (free.filter (fun x => decide ¬ inRun pid (sz.toNat) x)).length =
        free.length - sz.toNat := by
      rw [← hlen1]; simp only [decide_not]
    rw [e]; have := h.2.2.2.2; word
  · clear hd hlen1
    simp only [List.mem_filter, decide_eq_true_iff]
    constructor
    · rintro ⟨hx, hn⟩
      by_cases hr : inRun pid (sz.toNat) x
      · right; unfold inRun at hr hn ⊢; constructor <;> word
      · left; exact ⟨hx, hr⟩
    · rintro (⟨hx, hr⟩ | hr)
      · refine ⟨hx, fun h' => hr ?_⟩
        unfold inRun at h' ⊢; constructor <;> word
      · have hin : inRun pid (sz.toNat) x := by unfold inRun at hr ⊢; constructor <;> word
        refine ⟨span_mem h.2.1 hs hin, fun h' => ?_⟩
        unfold inRun at h' hr; word

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
    (hAdd : hashMap.addSpan.spec (GF := GF) (hG := hG)) (h : Loc) :
    (hashImpl (GF := GF) h).AllocateSpec := by
  unfold FLImpl.AllocateSpec
  rw [hashImpl_ity, hashImpl_iv]
  intro s σ txid n Hn
  wp_start as ⟨#Hhdl, Hsh, Hown⟩
  dsimp only [hashImpl]
  icases Hown with ⟨%cnt, %sp, %bwm, %sets, %fm, %fw, %bw, %FM, Hcnt, Hfmf, Hfwf, Hbwf, Hfm,
    Hsets, Hfw, Hbw, %Hhok⟩
  iunfold ownSh at Hsh
  icases Hsh with ⟨%c, Hsh, %Hok⟩
  obtain ⟨Hc, Hwf⟩ := Hok
  have Hge : ∀ x ∈ σ.free, 2 ≤ x.toNat := fun x hx => Hwf.2.1 x (List.mem_append_left _ hx)
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
      iunfold ownShC at Hsh
      icases Hsh with ⟨%al, %ca, %pe, %pp, Hsh⟩
      iNamed Hsh
      try wp_auto
      wp_apply wp_mapInsert $$ Hallocs as Hallocs
      try wp_auto
      have Hcan := alloc_can Hhok Hsp (k := uint.nat n) (Nat.le_refl _)
      ihave IH3 : iprop(∃ (j : w64) (m' : GMap w64 Unit),
          "i" ∷ i_ptr ↦ j ∗ "Hcache" ∷ ca ↦$ m' ∗
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
      iexists #()
      isplitr
      · ipureintro; rfl
      try wp_auto
      have Hnn : uint.nat n = sint.nat n := by word
      have Hnn' : n.toNat = sint.nat n := by word
      rw [Hnn] at Hj Hcan
      rw [Hnn'] at Hok'
      have HcanS : σ.canAlloc key (sint.nat n) := Hcan
      have Hr0 : key ≠ W64 0 := by
        have := Hge key (HcanS.2 key ⟨Nat.le_refl _, by word⟩); intro e; subst e; simp at this
      iapply HΦ
      iright
      isplitr
      · ipureintro; exact ⟨Hr0, HcanS⟩
      isplitl [Hif Hal Hallocs Hca Hcache Hpe Hpending Hpds]
      · iunfold ownSh
        iexists m'
        isplitl
        · iunfold ownShC
          iexists al, ca, pe, pp
          simp only [FLPg.alloc, named]
          iframe
        · ipureintro
          exact ⟨fun x => by rw [Hj.2 x, Hc x]; exact (alloc_allIds Hwf HcanS x).symm,
            alloc_WF Hwf txid key (sint.nat n)⟩
      · ihave Hown := hashImpl_own_close h (σ.alloc txid key (sint.nat n)).free _ _ _ _
          (by simpa [FLPg.alloc] using Hok') $$ Hraw
        iExactEq Hown; rfl
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
      iunfold ownShC at Hsh
      icases Hsh with ⟨%al, %ca, %pe, %pp, Hsh⟩
      iNamed Hsh
      try wp_auto
      wp_apply wp_mapInsert $$ Hallocs as Hallocs
      try wp_auto
      wp_apply (hAdd h (cnt - key) (GMap.delete pid sp) (GMap.delete (pid + (key - W64 1)) bwm)
        (setsDel sets key pid) (pid + n) (key - n)) $$ [Hraw] as Hraw
      · iexact Hraw
      have Hn1 : 1 ≤ n.toNat := by word
      have Hnk : n.toNat < key.toNat := by word
      have Hkle : uint.nat n ≤ key.toNat := by word
      have Hok' := alloc_split Hhok Hsp Hn1 Hnk
      try wp_auto
      have Hcan := alloc_can Hhok Hsp (k := uint.nat n) Hkle
      ihave IH3 : iprop(∃ (j : w64) (m' : GMap w64 Unit),
          "i" ∷ i_ptr ↦ j ∗ "Hcache" ∷ ca ↦$ m' ∗
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
      iexists #()
      isplitr
      · ipureintro; rfl
      try wp_auto
      iexists #()
      isplitr
      · ipureintro; rfl
      try wp_auto
      have Hnn : uint.nat n = sint.nat n := by word
      have Hnn' : n.toNat = sint.nat n := by word
      rw [Hnn] at Hj Hcan
      rw [Hnn'] at Hok'
      have HcanS : σ.canAlloc pid (sint.nat n) := Hcan
      have Hr0 : pid ≠ W64 0 := by
        have := Hge pid (HcanS.2 pid ⟨Nat.le_refl _, by word⟩); intro e; subst e; simp at this
      iapply HΦ
      iright
      isplitr
      · ipureintro; exact ⟨Hr0, HcanS⟩
      isplitl [Hif Hal Hallocs Hca Hcache Hpe Hpending Hpds]
      · iunfold ownSh
        iexists m'
        isplitl
        · iunfold ownShC
          iexists al, ca, pe, pp
          simp only [FLPg.alloc, named]
          iframe
        · ipureintro
          exact ⟨fun x => by rw [Hj.2 x, Hc x]; exact (alloc_allIds Hwf HcanS x).symm,
            alloc_WF Hwf txid pid (sint.nat n)⟩
      · ihave Hown := hashImpl_own_close h (σ.alloc txid pid (sint.nat n)).free _ _ _ _
          (by simpa [FLPg.alloc] using Hok') $$ Hraw
        iExactEq Hown; rfl
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
    isplitl [Hsh]
    · iunfold ownSh; iexists c; iframe; ipureintro; exact ⟨Hc, Hwf⟩
    iexists cnt, sp, bwm, sets, fm, fw, bw, FM
    iframe
    ipureintro; exact Hhok

end proof

end freelist
end internal
end bbolt
end EtcdGrove
end Perennial
