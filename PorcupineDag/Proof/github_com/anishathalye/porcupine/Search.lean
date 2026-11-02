/-
Lean-first (no Rocq counterpart).

# The DAG search's memory (2026-11-02, from v1.3.1's `Search.lean`)

What `chains.lift`, `chains.unlift` and `checkSingle`'s loop own besides the chains
(`ChainsOwn.lean`), at the abstract search state of `DagTheory` (the frames `fs`, the candidate
list `fr`, the cache): `searchOwn`, the chains at the heads of `ids fs` with `ChainsInv`, the
stack (`stackRep`: each entry's operation, client and frontier position are its frame's, its
state a shared value of the frame's state), the bitset of `ids fs` and the cache (v1.3.1's
`cacheOwn`, with `cacheP`). The state values (the current one, the frames', the cache entries')
are shared in the pool `np` (`Shared.lean`), whose token the caller keeps.
-/
module

public import PorcupineDag.Proof.github_com.anishathalye.porcupine.ChainsOwn
public import PorcupineDag.Proof.github_com.anishathalye.porcupine.Cache

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProofMode

namespace github_com.anishathalye.porcupine

open Theory

section defs
variable [GooseExts]
variable {σ : Type}

/-- A cache entry's bitset (of `n` bits) and state are a configuration of the abstract cache. -/
def cacheP (n : Nat) (cache : List ((Nat → Prop) × σ)) (ws : List w64) (t : σ) : Prop :=
  ∃ c ∈ cache, (∀ i, c.1 i ↔ (i < n ∧ bsBit ws i = true)) ∧ c.2 = t

theorem cacheP_cons {n : Nat} {cache : List ((Nat → Prop) × σ)} {ws : List w64} {t : σ}
    (c : (Nat → Prop) × σ) (h : cacheP n cache ws t) : cacheP n (c :: cache) ws t := by
  obtain ⟨c', hc', h1, h2⟩ := h
  exact ⟨c', List.mem_cons_of_mem _ hc', h1, h2⟩

end defs

section heap
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [NaInvG GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.anishathalye.porcupine.Assumptions]
variable {σ : Type}

/-- A bucket of the cache. -/
def bucketOwn (S : ModelSpec GF σ) (np : NaInvPoolName) (n : Nat) (cache : List ((Nat → Prop) × σ)) (bk : GoSlice) :
    IProp GF :=
  iprop(∃ ces : List cacheEntry, bk ↦*□ ces ∗ ownSliceCap cacheEntry bk (DFrac.own 1) ∗
    [∗list] ce ∈ ces, cacheEntryOk S np (cacheP n cache) ce)

/-- The cache: a map of buckets. -/
def cacheOwn (S : ModelSpec GF σ) (np : NaInvPoolName) (n : Nat) (cm : Loc) (cache : List ((Nat → Prop) × σ)) :
    IProp GF :=
  iprop(∃ CM : GMap w64 GoSlice, cm ↦$ CM ∗ [∗map] _k ↦ bk ∈ CM, bucketOwn S np n cache bk)

theorem cacheEntryOk_cons (S : ModelSpec GF σ) (np : NaInvPoolName) (n : Nat) (cache : List ((Nat → Prop) × σ))
    (c : (Nat → Prop) × σ) (ce : cacheEntry) :
    cacheEntryOk S np (cacheP n cache) ce ⊢ cacheEntryOk (GF := GF) S np (cacheP n (c :: cache)) ce := by
  unfold cacheEntryOk
  iintro ⟨%ws, %t, %k, #H1, #H2, %H3⟩
  iexists ws, t, k
  iframe H1 H2
  ipureintro; exact cacheP_cons c H3

theorem bucketOwn_cons (S : ModelSpec GF σ) (np : NaInvPoolName) (n : Nat) (cache : List ((Nat → Prop) × σ))
    (c : (Nat → Prop) × σ) (bk : GoSlice) :
    bucketOwn S np n cache bk ⊢ bucketOwn (GF := GF) S np n (c :: cache) bk := by
  unfold bucketOwn
  iintro ⟨%ces, #Hbk, Hcap, #Hces⟩
  iexists ces
  iframe Hbk Hcap
  iapply BigSepL.bigSepL_mono ?_ $$ Hces
  intro k ce _
  exact cacheEntryOk_cons S np n cache c ce

/-- A bucket's entries, read (the bucket of a key absent from the map is `nil`). -/
theorem buckets_read (S : ModelSpec GF σ) (np : NaInvPoolName) (n : Nat) (cache : List ((Nat → Prop) × σ))
    (CM : GMap w64 GoSlice) (key : w64) :
    ([∗map] _k ↦ bk ∈ CM, bucketOwn S np n cache bk) ⊢
      (∃ ces : List cacheEntry, (CM !! key).getD slice.nil ↦*□ ces ∗
        [∗list] ce ∈ ces, cacheEntryOk (GF := GF) S np (cacheP n cache) ce) ∗
      [∗map] _k ↦ bk ∈ CM, bucketOwn S np n cache bk := by
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
    icases (BigSepM.bigSepM_lookup_acc (Φ := fun _ bk => bucketOwn (GF := GF) S np n cache bk) hk).1
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
theorem buckets_take (S : ModelSpec GF σ) (np : NaInvPoolName) (n : Nat) (cache : List ((Nat → Prop) × σ))
    (CM : GMap w64 GoSlice) (key : w64) :
    ([∗map] _k ↦ bk ∈ CM, bucketOwn S np n cache bk) ⊢
      bucketOwn (GF := GF) S np n cache ((CM !! key).getD slice.nil) ∗
      ∀ bk', bucketOwn S np n cache bk' -∗ [∗map] _k ↦ b ∈ <[key := bk']> CM, bucketOwn S np n cache b := by
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
      iapply (BigSepM.bigSepM_insert (Φ := fun _ bk => bucketOwn (GF := GF) S np n cache bk) hk).2
      iframe
  | some bk =>
    iintro H
    icases (BigSepM.bigSepM_delete (Φ := fun _ bk => bucketOwn (GF := GF) S np n cache bk) hk).1
      $$ H with ⟨Hb, H⟩
    simp only [Option.getD_some]
    iframe Hb
    iintro %bk' Hb
    iapply (BigSepM.bigSepM_insert_delete (Φ := fun _ bk => bucketOwn (GF := GF) S np n cache bk)).2
    iframe

theorem buckets_cons (S : ModelSpec GF σ) (np : NaInvPoolName) (n : Nat) (cache : List ((Nat → Prop) × σ))
    (c : (Nat → Prop) × σ) (CM : GMap w64 GoSlice) :
    ([∗map] _k ↦ bk ∈ CM, bucketOwn S np n cache bk) ⊢
      [∗map] _k ↦ bk ∈ CM, bucketOwn (GF := GF) S np n (c :: cache) bk := by
  iapply BigSepM.bigSepM_mono
  intro k v _
  exact bucketOwn_cons S np n cache c v

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

/-- An element of `longest` (`longestOwn`). -/
abbrev longestElem (p : Loc) : IProp GF :=
  iprop(⌜p = null⌝ ∨ ∃ (sl : GoSlice) (xs : List w64), p ↦□ sl ∗ sl ↦*{DFrac.discard} xs)

theorem longestElems_set (ps : List Loc) (k : Nat) (q : Loc) (hk : k < ps.length) :
    ([∗list] p ∈ ps, longestElem (GF := GF) p) ∗ longestElem q ⊢
      [∗list] p ∈ ps.set k q, longestElem p := by
  iintro ⟨H, Hq⟩
  icases BigSepL.bigSepL_insert_acc (Φ := fun _ p => longestElem (GF := GF) p)
    (List.getElem?_eq_getElem hk) $$ H with ⟨-, Hback⟩
  iapply Hback $$ Hq

theorem longestElems_get (ps : List Loc) (k : Nat) (p : Loc) (hk : ps[k]? = some p) :
    ([∗list] p ∈ ps, longestElem (GF := GF) p) ⊢ longestElem p :=
  BigSepL.bigSepL_lookup (Φ := fun _ p => longestElem (GF := GF) p) hk

/-- `computePartial`'s copy, made read-only (once `longest` points to it). -/
theorem persist_or (l : Loc) (sl : GoSlice) (xs : List w64) :
    ((l ↦ sl ∗ sl ↦* xs) ∨ (l ↦□ sl ∗ sl ↦*□ xs)) ⊢ |==> (l ↦□ sl ∗ sl ↦*□ xs : IProp GF) := by
  iintro (⟨H1, H2⟩ | ⟨#H1, #H2⟩)
  · ipersist H1
    ipersist H2
    imodintro
    iframe H1 H2
  · imodintro
    iframe H1 H2

/-- The stack: the frames, oldest first; the `i`-th oldest entry records its frame's operation,
client and frontier position, and holds a value of its state, of index `i`. -/
def stackRep (S : ModelSpec GF σ) (np : NaInvPoolName) (cs : List (List Nat))
    (ses : List stackEntry) (fs : List (Frame σ)) : IProp GF :=
  iprop([∗list] i ↦ se; f ∈ ses; fs.reverse,
    ⌜sint.Z se.opId' = f.id ∧ sint.Z se.clientId' = clientOf cs f.id ∧
      sint.Z se.frontierIdx' = f.pos⌝ ∗ shared S np i se.state' f.pre)

instance stackRep_persistent (S : ModelSpec GF σ) (np : NaInvPoolName) (cs : List (List Nat))
    (ses : List stackEntry) (fs : List (Frame σ)) : Persistent (stackRep S np cs ses fs) := by
  unfold stackRep
  exact BigSepL2.bigSepL2_persistent (fun _ _ _ _ _ => inferInstance)

/-- What `chains.lift`, `chains.unlift` and `checkSingle`'s loop own at the abstract state
`(fs, fr, cache)` (see the file header): the chains at `ch`, the stack at `stack_ptr`, the
bitset at `lin_ptr`, the cache at `cm`. -/
def searchOwn (S : ModelSpec GF σ) (np : NaInvPoolName) (h : List (Op OpV))
    (cs : List (List Nat)) (ch stack_ptr lin_ptr cm : Loc) (fs : List (Frame σ))
    (fr : List Nat) (cache : List ((Nat → Prop) × σ)) : IProp GF :=
  iprop(∃ (st : ChSt) (ssl : GoSlice) (ses : List stackEntry) (lsl : GoSlice) (ws : List w64),
    "Hch" ∷ chainsOwn ch h cs st ∗
    "%Hci" ∷ ⌜ChainsInv h cs (ids fs) st ∧ frOf cs st = fr⌝ ∗
    "stack" ∷ stack_ptr ↦ ssl ∗ "Hstack" ∷ ssl ↦* ses ∗
    "Hscap" ∷ ownSliceCap stackEntry ssl (DFrac.own 1) ∗ "#Hses" ∷ stackRep S np cs ses fs ∗
    "lin" ∷ lin_ptr ↦ lsl ∗ "Hlin" ∷ lsl ↦* ws ∗
    "%Hws" ∷ ⌜ws.length = bsChunks h.length ∧ ∀ i, bsBit ws i = decide (i ∈ ids fs)⌝ ∗
    "Hcache" ∷ cacheOwn S np h.length cm cache)

end heap

end github_com.anishathalye.porcupine

end Perennial
