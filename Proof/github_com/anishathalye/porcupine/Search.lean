/-
Lean-first (no Rocq counterpart).

# `checkSingle`'s loop, in the heap (2026-10-14)

The loop invariant of `checkSingle` (`searchInv`) relates its variables to the abstract search
state of `Theory` (the frames `fs`, the state `s`, the cursor `p`, the cache):

- `entry` is the node of `(rem es (ids fs))[p]` (`nil` past the end, `curLoc`);
- the nodes are the list with `ids fs` lifted (`nodesOwn`);
- `state` holds a value of `s`;
- `linearized` is a bitset whose bits are `ids fs`;
- `cache` is a map of buckets, each a read-only slice of entries (`bucketOwn`) whose bitset and
  state are a configuration of the abstract cache (`cacheP`; which bucket is irrelevant);
- `calls` holds the frames, oldest first, each with its call's node and a value of its state
  (`callsOwn`).
-/
module

public import Proof.github_com.anishathalye.porcupine.Cache
public import Proof.github_com.anishathalye.porcupine.Linked

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProofMode

namespace github_com.anishathalye.porcupine

open Theory

section defs
variable [ext : FfiSyntax]
variable {σ : Type}

/-- The node of `l[p]`, `nil` past the end. -/
def curLoc (loc : Entry → Loc) (l : List Entry) (p : Nat) : Loc :=
  match l[p]? with
  | some e => loc e
  | none => null

/-- A cache entry's bitset (of `n` bits) and state are a configuration of the abstract cache. -/
def cacheP (n : Nat) (cache : List ((Nat → Prop) × σ)) (ws : List w64) (t : σ) : Prop :=
  ∃ c ∈ cache, (∀ i, c.1 i ↔ (i < n ∧ bsBit ws i = true)) ∧ c.2 = t

theorem cacheP_cons {n : Nat} {cache : List ((Nat → Prop) × σ)} {ws : List w64} {t : σ}
    (c : (Nat → Prop) × σ) (h : cacheP n cache ws t) : cacheP n (c :: cache) ws t := by
  obtain ⟨c', hc', h1, h2⟩ := h
  exact ⟨c', List.mem_cons_of_mem _ hc', h1, h2⟩

/-- Every frame lifted a call of the history. -/
theorem framesOk_mem {α : Type} {M : SeqModel σ α} {h : List (Op α)} {es : List Entry} :
    ∀ {fs : List (Frame σ)}, FramesOk M h es fs → ∀ f ∈ fs, (⟨false, f.id⟩ : Entry) ∈ es
  | [], _, _, hf => by cases hf
  | g :: fs, ⟨hfr, _, hpos⟩, f, hf => by
    rcases List.mem_cons.mp hf with rfl | hf
    · exact rem_get_mem hpos
    · exact framesOk_mem hfr f hf

theorem curLoc_null {loc : Entry → Loc} {es : List Entry} {B : List Nat}
    (hnn : ∀ e ∈ es, loc e ≠ null) {p : Nat} :
    curLoc loc (rem es B) p = null ↔ (rem es B)[p]? = none := by
  unfold curLoc
  cases he : (rem es B)[p]? with
  | none => simp
  | some e => simp only [reduceCtorEq, iff_false]; exact hnn e (rem_get_mem he)

theorem curLoc_some {loc : Entry → Loc} {l : List Entry} {p : Nat} {e : Entry}
    (h : l[p]? = some e) : curLoc loc l p = loc e := by
  simp [curLoc, h]

/-- The head's `next`: the first node of the list. -/
theorem nbrLoc_head (hd : Loc) (loc : Entry → Loc) {es : List Entry} (hnd : es.Nodup)
    (B : List Nat) : nbrLoc hd loc (layout es B none).2 = curLoc loc (rem es B) 0 := by
  have hc : (cur es B)[0]? = some none := by simp [cur]
  rw [layout_cur (List.mem_of_getElem? hc)]
  simp only [nb]
  rw [nextOf_getElem? (cur_nodup hnd B) hc, cur_getElem?]
  unfold curLoc
  cases (rem es B)[0]? <;> rfl

/-- The head's `next`, once `layout` is unfolded. -/
theorem nbrLoc_head' (hd : Loc) (loc : Entry → Loc) {es : List Entry} (hnd : es.Nodup)
    (B : List Nat) : nbrLoc hd loc (nextOf (cur es B) none) = curLoc loc (rem es B) 0 := by
  have hc : (cur es B)[0]? = some none := by simp [cur]
  rw [nextOf_getElem? (cur_nodup hnd B) hc, cur_getElem?]
  unfold curLoc
  cases (rem es B)[0]? <;> rfl

/-- An entry's `next`: the node after it. -/
theorem nbrLoc_next (hd : Loc) (loc : Entry → Loc) {es : List Entry} (hnd : es.Nodup)
    {B : List Nat} {p : Nat} {e : Entry} (he : (rem es B)[p]? = some e) :
    nbrLoc hd loc (layout es B (some e)).2 = curLoc loc (rem es B) (p + 1) := by
  have hc : (cur es B)[p + 1]? = some (some e) := by rw [cur_getElem?, he]; rfl
  rw [layout_cur (List.mem_of_getElem? hc)]
  simp only [nb]
  rw [nextOf_getElem? (cur_nodup hnd B) hc, cur_getElem?]
  unfold curLoc
  cases (rem es B)[p + 1]? <;> rfl

/-- `len(history) / 2` (a signed division). -/
theorem sdiv_two (l : w64) (k : Nat) (h1 : sint.Z l = 2 * (k : Int)) (hk : (k : Int) < 2 ^ 60) :
    BitVec.sdiv l (W64 2) = W64 k := by
  have h0 : 0 ≤ sint.Z l := by omega
  have hm : l.msb = false := by
    rw [BitVec.msb_eq_toInt]; simp only [sint.Z] at h0; simp; omega
  have h2 : (W64 2).msb = false := by decide
  rw [BitVec.sdiv_eq, hm, h2]
  simp only [BitVec.udiv_eq]
  have : uint.Z l = sint.Z l := by word
  word

end defs

section heap
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.anishathalye.porcupine.Assumptions]
variable {σ : Type}

/-- A bucket of the cache. -/
def bucketOwn (S : ModelSpec GF σ) (n : Nat) (cache : List ((Nat → Prop) × σ)) (bk : GoSlice) :
    IProp GF :=
  iprop(∃ ces : List cacheEntry, bk ↦*□ ces ∗ ownSliceCap cacheEntry bk (DFrac.own 1) ∗
    [∗list] ce ∈ ces, cacheEntryOk S (cacheP n cache) ce)

/-- The cache: a map of buckets. -/
def cacheOwn (S : ModelSpec GF σ) (n : Nat) (cm : Loc) (cache : List ((Nat → Prop) × σ)) :
    IProp GF :=
  iprop(∃ CM : GMap w64 GoSlice, cm ↦$ CM ∗ [∗map] _k ↦ bk ∈ CM, bucketOwn S n cache bk)

/-- The stack: the frames, oldest first, with their calls' nodes and values of their states. -/
def callsRep (S : ModelSpec GF σ) (loc : Entry → Loc) (ces : List callsEntry)
    (fs : List (Frame σ)) : IProp GF :=
  iprop([∗list] ce; f ∈ ces; fs.reverse,
    ⌜ce.entry' = loc ⟨false, f.id⟩⌝ ∗ S.rep ce.state' f.pre)

instance callsRep_persistent (S : ModelSpec GF σ) (loc : Entry → Loc) (ces : List callsEntry)
    (fs : List (Frame σ)) : Persistent (callsRep S loc ces fs) := by
  unfold callsRep
  exact BigSepL2.bigSepL2_persistent (fun _ _ _ _ _ => inferInstance)

theorem cacheEntryOk_cons (S : ModelSpec GF σ) (n : Nat) (cache : List ((Nat → Prop) × σ))
    (c : (Nat → Prop) × σ) (ce : cacheEntry) :
    cacheEntryOk S (cacheP n cache) ce ⊢ cacheEntryOk (GF := GF) S (cacheP n (c :: cache)) ce := by
  unfold cacheEntryOk
  iintro ⟨%ws, %t, #H1, #H2, %H3⟩
  iexists ws, t
  iframe H1 H2
  ipureintro; exact cacheP_cons c H3

theorem bucketOwn_cons (S : ModelSpec GF σ) (n : Nat) (cache : List ((Nat → Prop) × σ))
    (c : (Nat → Prop) × σ) (bk : GoSlice) :
    bucketOwn S n cache bk ⊢ bucketOwn (GF := GF) S n (c :: cache) bk := by
  unfold bucketOwn
  iintro ⟨%ces, #Hbk, Hcap, #Hces⟩
  iexists ces
  iframe Hbk Hcap
  iapply BigSepL.bigSepL_mono ?_ $$ Hces
  intro k ce _
  exact cacheEntryOk_cons S n cache c ce

/-- A bucket's entries, read (the bucket of a key absent from the map is `nil`). -/
theorem buckets_read (S : ModelSpec GF σ) (n : Nat) (cache : List ((Nat → Prop) × σ))
    (CM : GMap w64 GoSlice) (key : w64) :
    ([∗map] _k ↦ bk ∈ CM, bucketOwn S n cache bk) ⊢
      (∃ ces : List cacheEntry, (CM !! key).getD slice.nil ↦*□ ces ∗
        [∗list] ce ∈ ces, cacheEntryOk (GF := GF) S (cacheP n cache) ce) ∗
      [∗map] _k ↦ bk ∈ CM, bucketOwn S n cache bk := by
  cases hk : CM !! key with
  | none =>
    iintro H
    iframe H
    iexists []
    simp only [Option.getD_none]
    isplitl
    · iapply ownSlice_nil
    · iapply BigSepL.bigSepL_nil.2; iempintro
  | some bk =>
    iintro H
    icases (BigSepM.bigSepM_lookup_acc (Φ := fun _ bk => bucketOwn (GF := GF) S n cache bk) hk).1
      $$ H with ⟨Hb, Hback⟩
    unfold bucketOwn
    icases Hb with ⟨%ces, #Hbk, Hcap, #Hces⟩
    isplitr
    · iexists ces
      simp only [Option.getD_some]
      iframe Hbk Hces
    · iapply Hback
      iexists ces
      iframe Hbk Hcap Hces

/-- A bucket taken out of the map, to put a new one at its key. -/
theorem buckets_take (S : ModelSpec GF σ) (n : Nat) (cache : List ((Nat → Prop) × σ))
    (CM : GMap w64 GoSlice) (key : w64) :
    ([∗map] _k ↦ bk ∈ CM, bucketOwn S n cache bk) ⊢
      bucketOwn (GF := GF) S n cache ((CM !! key).getD slice.nil) ∗
      ∀ bk', bucketOwn S n cache bk' -∗ [∗map] _k ↦ b ∈ <[key := bk']> CM, bucketOwn S n cache b := by
  cases hk : CM !! key with
  | none =>
    iintro H
    simp only [Option.getD_none]
    isplitr
    · unfold bucketOwn
      iexists []
      isplitl
      · iapply ownSlice_nil
      isplitl
      · iapply ownSliceCap_nil
      · iapply BigSepL.bigSepL_nil.2; iempintro
    · iintro %bk' Hb
      iapply (BigSepM.bigSepM_insert (Φ := fun _ bk => bucketOwn (GF := GF) S n cache bk) hk).2
      iframe
  | some bk =>
    iintro H
    icases (BigSepM.bigSepM_delete (Φ := fun _ bk => bucketOwn (GF := GF) S n cache bk) hk).1
      $$ H with ⟨Hb, H⟩
    simp only [Option.getD_some]
    iframe Hb
    iintro %bk' Hb
    iapply (BigSepM.bigSepM_insert_delete (Φ := fun _ bk => bucketOwn (GF := GF) S n cache bk)).2
    iframe

theorem buckets_cons (S : ModelSpec GF σ) (n : Nat) (cache : List ((Nat → Prop) × σ))
    (c : (Nat → Prop) × σ) (CM : GMap w64 GoSlice) :
    ([∗map] _k ↦ bk ∈ CM, bucketOwn S n cache bk) ⊢
      [∗map] _k ↦ bk ∈ CM, bucketOwn (GF := GF) S n (c :: cache) bk := by
  iapply BigSepM.bigSepM_mono
  intro k v _
  exact bucketOwn_cons S n cache c v

theorem nulls_ok (n : Nat) :
    ⊢ ([∗list] p ∈ List.replicate n null, ⌜p = null⌝ ∨
      ∃ (sl : GoSlice) (xs : List w64), p ↦□ sl ∗ sl ↦*{DFrac.discard} xs : IProp GF) := by
  induction n with
  | zero => exact BigSepL.bigSepL_nil.2
  | succ n ih =>
    rw [List.replicate_succ]
    iapply BigSepL.bigSepL_cons.2
    isplitl []
    · ileft; ipureintro; rfl
    · iapply ih

theorem longestOwn_replicate (lg : GoSlice) (n : Nat) :
    lg ↦* List.replicate n null ⊢ longestOwn (GF := GF) lg n := by
  unfold longestOwn
  iintro H
  iexists _
  iframe H
  isplitl []
  · ipureintro; exact List.length_replicate
  · iapply nulls_ok

/-- The loop invariant of `checkSingle` (see the file header), at the abstract state
`(fs, s, p, cache)`. -/
def searchInv (S : ModelSpec GF σ) (h : List (Op OpV)) (aes : List Entry) (hd : Loc)
    (loc : Entry → Loc) (entry_ptr state_ptr lin_ptr cm calls_ptr : Loc)
    (fs : List (Frame σ)) (s : σ) (p : Nat) (cache : List ((Nat → Prop) × σ)) : IProp GF :=
  iprop(∃ (sv : GoInterface) (lsl : GoSlice) (ws : List w64) (csl : GoSlice)
      (ces : List callsEntry),
    "entry" ∷ entry_ptr ↦ curLoc loc (rem aes (ids fs)) p ∗
    "Hnodes" ∷ nodesOwn hd loc (valOf h) aes (ids fs) ∗
    "state" ∷ state_ptr ↦ sv ∗ "#Hsv" ∷ S.rep sv s ∗
    "linearized" ∷ lin_ptr ↦ lsl ∗ "Hlin" ∷ lsl ↦* ws ∗
    "Hcache" ∷ cacheOwn S h.length cm cache ∗
    "calls" ∷ calls_ptr ↦ csl ∗ "Hcalls" ∷ csl ↦* ces ∗
    "Hcap" ∷ ownSliceCap callsEntry csl (DFrac.own 1) ∗ "#Hces" ∷ callsRep S loc ces fs ∗
    "%Hws" ∷ ⌜ws.length = bsChunks h.length ∧ ∀ i, bsBit ws i = decide (i ∈ ids fs)⌝ ∗
    "%Hinv" ∷ ⌜Inv S.M h aes fs s p cache ∧
      (rem aes (ids fs) ≠ [] → p < (rem aes (ids fs)).length)⌝)

end heap

end github_com.anishathalye.porcupine

end Perennial
