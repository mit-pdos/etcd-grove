/-
Lean-first (no Rocq counterpart).

# kvdurable's codecs, pure (2026-10-31)

What the functions of `examples/kvdurable/storage.go` and `kv.go` that touch only bytes and raftpb
records write, as functions of the records' models (`EntryM`, `SnapshotM`, `HardStateM`,
`Proof/go_etcd_io/raft/v3/PbModel.lean`), and pure decoders that read them back, with their round
trips (`dec (enc x ++ r) = some (x, r)` under the well-formedness the Go readers check) and the
injectivity of the encodings. The WP specs of the Go functions (`Spec/.../kvdurable/`) are stated
in the encoders; the decoders are for the proofs of `encode`/`openStorage` (the file a replica
reads back is the one it wrote: `encStor_inj`).

* `putB x` (`putBytes`): `x`'s length (8 bytes, little-endian), then `x`.
* `encIDs ids` (`putIDs`): their number, then each (`u64sLe`).
* `encEntry e` (`putEntry`): its term, index and type (8 bytes each), then its data (`putB`).
* `encConf c` (`putSnapshot`'s configuration): the voters, learners, outgoing voters and next
  learners (`encIDs` each), then auto-leave (one byte, `1` for `true`).
* `encSnap s` (`putSnapshot`): its index and term, its configuration, then its data.
* `encStor f` (`Storage.encode`): the hard state (term, vote, commit), the snapshot, the index and
  term of the log's start, the number of entries, then each (`encEntry`).

The map codec (`putMap`/`encodeState`) is kvreconf's: `encKVs`, `encMap`, `encState`, `KVsWf`,
`KVsOf` (copied under this namespace, as the Go is the same text).
-/
module

public import Proof.go_etcd_io.raft.v3.PbModel
public import Perennial.Proof.encoding.binary

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove.kvdurable

/-! ## The byte strings and the map codec (kvreconf's) -/

/-- `putBytes`: the bytes `x`, prefixed by their length. -/
def putB (x : List w8) : List w8 := u64Le (W64 x.length) ++ x

/-- The bindings, each key then its value, `putB`'d. -/
def encKVs : List (List w8 × List w8) → List w8
  | [] => []
  | p :: r => putB p.1 ++ putB p.2 ++ encKVs r

theorem encKVs_snoc (l : List (List w8 × List w8)) (p : List w8 × List w8) :
    encKVs (l ++ [p]) = encKVs l ++ (putB p.1 ++ putB p.2) := by
  induction l with
  | nil => simp [encKVs]
  | cons q l ih => simp only [List.cons_append, encKVs, ih, List.append_assoc]

theorem encKVs_cons (p : List w8 × List w8) (l : List (List w8 × List w8)) :
    encKVs (p :: l) = putB p.1 ++ (putB p.2 ++ encKVs l) := by
  simp [encKVs, List.append_assoc]

theorem lookup_take_succ (kvs : List (List w8 × List w8)) (n : Nat) (p : List w8 × List w8)
    (h : kvs[n]? = some p) (hnd : (kvs.map Prod.fst).Nodup) (k : List w8) :
    (kvs.take (n + 1)).lookup k = if k = p.1 then some p.2 else (kvs.take n).lookup k := by
  rw [List.take_add_one, h]
  simp only [Option.toList_some]
  have hn : p.1 ∉ (kvs.take n).map Prod.fst := by
    intro hm
    have hl : n < kvs.length := (List.getElem?_eq_some_iff.1 h).1
    have : (kvs.map Prod.fst) = (kvs.take n).map Prod.fst ++ (kvs.drop n).map Prod.fst := by
      rw [← List.map_append, List.take_append_drop]
    rw [this] at hnd
    have hd : p.1 ∈ (kvs.drop n).map Prod.fst := by
      rw [List.drop_eq_getElem_cons hl]
      rw [List.getElem?_eq_getElem hl] at h
      simp [Option.some.inj h]
    exact (List.nodup_append.1 hnd).2.2 _ hm _ hd rfl
  obtain ⟨p1, p2⟩ := p
  simp only at hn ⊢
  generalize kvs.take n = l at hn ⊢
  induction l with
  | nil =>
    by_cases hk : k = p1
    · subst hk; simp
    · have : (k == p1) = false := by simpa using hk
      simp [List.lookup, this, hk]
  | cons q l ih =>
    obtain ⟨q1, q2⟩ := q
    simp only [List.map_cons, List.mem_cons, not_or] at hn
    simp only [List.cons_append, List.lookup]
    by_cases hq : k = q1
    · subst hq
      have : (k == k) = true := by simp
      have h2 : k ≠ p1 := fun h => hn.1 h.symm
      simp [h2]
    · have : (k == q1) = false := by simpa using hq
      rw [this]
      exact ih hn.2

/-- What `putMap` writes of the bindings `kvs`: their count, then each binding. -/
def encMap (kvs : List (List w8 × List w8)) : List w8 :=
  u64Le (W64 kvs.length) ++ encKVs kvs

/-- What `encodeState` writes of the bindings `kvs` (the store's) and `ops` (the operations
applied, each with its answer). -/
def encState (kvs ops : List (List w8 × List w8)) : List w8 := encMap kvs ++ encMap ops

/-- What a list of bindings needs for `getMap` to read it back: no repeated key, and every
length (the count, each key's and value's) a Go slice's. -/
def KVsWf (kvs : List (List w8 × List w8)) : Prop :=
  (kvs.map Prod.fst).Nodup ∧ (kvs.length : Int) < 2 ^ 63 ∧
    ∀ p ∈ kvs, (p.1.length : Int) < 2 ^ 63 ∧ (p.2.length : Int) < 2 ^ 63

/-- The bindings `kvs` are the map `K`'s, and well formed for `getMap` (`KVsWf`): what `putMap`
writes of `K` (in Go, in increasing order of the keys). -/
def KVsOf (K : GMap (List w8) (List w8)) (kvs : List (List w8 × List w8)) : Prop :=
  KVsWf kvs ∧ ∀ k, kvs.lookup k = K !! k

/-! ## The storage file's codec -/

/-- Words, each as 8 bytes, little-endian (`putUint64` in a loop). -/
def u64sLe : List w64 → List w8
  | [] => []
  | x :: r => u64Le x ++ u64sLe r

/-- `putIDs`: the ids' number, then each. -/
def encIDs (ids : List w64) : List w8 := u64Le (W64 ids.length) ++ u64sLe ids

/-- `putEntry`: the entry's term, index and type (8 bytes each; the type, an `int32`, sign-extended
as Go's `uint64(e.GetType())`), then its data. -/
def encEntry [GooseExts] (e : EntryM) : List w8 :=
  u64Le e.Term' ++ (u64Le e.Index' ++ (u64Le (W64 (sint.Z e.Type')) ++ putB e.Data'))

/-- The entries, each as `putEntry` writes it (`encode`'s loop). -/
def encEntries [GooseExts] : List EntryM → List w8
  | [] => []
  | e :: r => encEntry e ++ encEntries r

/-- The byte of auto-leave: `1` for `true`, `0` for `false`. -/
def autoB (b : Bool) : w8 := if b then W8 1 else W8 0

/-- `putSnapshot`'s configuration: the four id lists, then auto-leave. -/
def encConf (c : ConfStateM) : List w8 :=
  encIDs c.Voters' ++ (encIDs c.Learners' ++ (encIDs c.VotersOutgoing' ++
    (encIDs c.LearnersNext' ++ [autoB c.AutoLeave'])))

/-- `putSnapshot`: the snapshot's index and term, its configuration, then its data. -/
def encSnap (s : SnapshotM) : List w8 :=
  u64Le s.Metadata'.Index' ++ (u64Le s.Metadata'.Term' ++
    (encConf s.Metadata'.ConfState' ++ putB s.Data'))

/-- **A storage file's contents** (what `Storage.encode` writes, `openStorage` reads): the hard
state, the snapshot, the index and term of the log's start, and the entries after it. -/
structure StorFile [GooseExts] where
  mk ::
  hs : HardStateM
  snap : SnapshotM
  prev : w64
  prevTerm : w64
  ents : List EntryM

/-- `Storage.encode`'s bytes of the contents `f`. -/
def encStor [GooseExts] (f : StorFile) : List w8 :=
  u64Le f.hs.Term' ++ (u64Le f.hs.Vote' ++ (u64Le f.hs.Commit' ++ (encSnap f.snap ++
    (u64Le f.prev ++ (u64Le f.prevTerm ++ (u64Le (W64 f.ents.length) ++ encEntries f.ents))))))

/-- An entry `getEntry` reads back: a known type (`typ > 2` is rejected), data of a Go slice's
length. -/
def EntWf [GooseExts] (e : EntryM) : Prop :=
  uint.Z e.Type' ≤ 2 ∧ (e.Data'.length : Int) < 2 ^ 63

/-- A configuration whose lists are of Go slices' lengths. -/
def ConfWf (c : ConfStateM) : Prop :=
  (c.Voters'.length : Int) < 2 ^ 63 ∧ (c.Learners'.length : Int) < 2 ^ 63 ∧
    (c.VotersOutgoing'.length : Int) < 2 ^ 63 ∧ (c.LearnersNext'.length : Int) < 2 ^ 63

/-- A snapshot `getSnapshot` reads back. -/
def SnapWf (s : SnapshotM) : Prop :=
  ConfWf s.Metadata'.ConfState' ∧ (s.Data'.length : Int) < 2 ^ 63

/-- Contents whose bytes decode back. -/
def StorWf [GooseExts] (f : StorFile) : Prop :=
  SnapWf f.snap ∧ (∀ e ∈ f.ents, EntWf e) ∧ (f.ents.length : Int) < 2 ^ 63

/-! ## Decoders -/

/-- The word at the start of `b` (`getUint64`), and the rest. -/
def decU64 (b : List w8) : Option (w64 × List w8) :=
  if 8 ≤ b.length then some (leToU64 (b.take 8), b.drop 8) else none

/-- The byte string at the start of `b` (`getBytes`), and the rest. -/
def decB (b : List w8) : Option (List w8 × List w8) :=
  match decU64 b with
  | none => none
  | some (n, r) => if uint.nat n ≤ r.length then some (r.take (uint.nat n), r.drop (uint.nat n))
    else none

/-- `n` words at the start of `b`, and the rest. -/
def decU64s : Nat → List w8 → Option (List w64 × List w8)
  | 0, b => some ([], b)
  | n + 1, b =>
    match decU64 b with
    | none => none
    | some (x, r) =>
      match decU64s n r with
      | none => none
      | some (xs, r') => some (x :: xs, r')

/-- The ids at the start of `b` (`getIDs`), and the rest. -/
def decIDs (b : List w8) : Option (List w64 × List w8) :=
  match decU64 b with
  | none => none
  | some (n, r) => decU64s (uint.nat n) r

/-- The entry at the start of `b` (`getEntry`), and the rest. -/
def decEntry [GooseExts] (b : List w8) : Option (EntryM × List w8) :=
  match decU64 b with
  | none => none
  | some (t, r1) =>
    match decU64 r1 with
    | none => none
    | some (i, r2) =>
      match decU64 r2 with
      | none => none
      | some (ty, r3) =>
        if uint.Z ty ≤ 2 then
          match decB r3 with
          | none => none
          | some (d, r4) => some (EntryM.mk t i (W32 (uint.Z ty)) d, r4)
        else none

/-- `n` entries at the start of `b`, and the rest. -/
def decEntries [GooseExts] : Nat → List w8 → Option (List EntryM × List w8)
  | 0, b => some ([], b)
  | n + 1, b =>
    match decEntry b with
    | none => none
    | some (e, r) =>
      match decEntries n r with
      | none => none
      | some (es, r') => some (e :: es, r')

/-- The auto-leave byte at the start of `b`: `true` iff it is `1`. -/
def decAuto (b : List w8) : Option (Bool × List w8) :=
  match b with
  | [] => none
  | x :: r => some (decide (x = W8 1), r)

/-- The configuration at the start of `b`, and the rest. -/
def decConf (b : List w8) : Option (ConfStateM × List w8) :=
  match decIDs b with
  | none => none
  | some (v, r1) =>
    match decIDs r1 with
    | none => none
    | some (l, r2) =>
      match decIDs r2 with
      | none => none
      | some (o, r3) =>
        match decIDs r3 with
        | none => none
        | some (n, r4) =>
          match decAuto r4 with
          | none => none
          | some (a, r5) => some (ConfStateM.mk v l o n a, r5)

/-- The snapshot at the start of `b` (`getSnapshot`), and the rest. -/
def decSnap (b : List w8) : Option (SnapshotM × List w8) :=
  match decU64 b with
  | none => none
  | some (i, r1) =>
    match decU64 r1 with
    | none => none
    | some (t, r2) =>
      match decConf r2 with
      | none => none
      | some (c, r3) =>
        match decB r3 with
        | none => none
        | some (d, r4) => some (SnapshotM.mk d (SnapshotMetadataM.mk c i t), r4)

/-- The storage contents `b` holds, all of it. -/
def decStor [GooseExts] (b : List w8) : Option StorFile :=
  match decU64 b with
  | none => none
  | some (term, r1) =>
    match decU64 r1 with
    | none => none
    | some (vote, r2) =>
      match decU64 r2 with
      | none => none
      | some (commit, r3) =>
        match decSnap r3 with
        | none => none
        | some (s, r4) =>
          match decU64 r4 with
          | none => none
          | some (prev, r5) =>
            match decU64 r5 with
            | none => none
            | some (pt, r6) =>
              match decU64 r6 with
              | none => none
              | some (n, r7) =>
                match decEntries (uint.nat n) r7 with
                | none => none
                | some (es, r8) =>
                  if r8 = [] then some (StorFile.mk (HardStateM.mk term vote commit) s prev pt es)
                  else none

/-! ## Round trips -/

theorem decU64_enc (x : w64) (r : List w8) : decU64 (u64Le x ++ r) = some (x, r) := by
  have hl := u64Le_length x
  unfold decU64
  rw [if_pos (by simp [hl])]
  rw [List.take_left' hl, List.drop_left' hl, u64Le_to_word]

theorem decB_putB (x r : List w8) (hx : (x.length : Int) < 2 ^ 63) :
    decB (putB x ++ r) = some (x, r) := by
  unfold decB putB
  rw [List.append_assoc, decU64_enc]
  have hn : uint.nat (W64 x.length) = x.length := by word
  simp only [hn]
  rw [if_pos (by simp), List.take_left' rfl, List.drop_left' rfl]

theorem decU64s_enc (xs : List w64) (r : List w8) :
    decU64s xs.length (u64sLe xs ++ r) = some (xs, r) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.length_cons, decU64s, u64sLe, List.append_assoc, decU64_enc, ih]

theorem decIDs_enc (ids : List w64) (r : List w8) (h : (ids.length : Int) < 2 ^ 63) :
    decIDs (encIDs ids ++ r) = some (ids, r) := by
  unfold decIDs encIDs
  rw [List.append_assoc, decU64_enc]
  have hn : uint.nat (W64 ids.length) = ids.length := by word
  simp only [hn, decU64s_enc]

theorem decEntry_enc [GooseExts] (e : EntryM) (r : List w8) (h : EntWf e) :
    decEntry (encEntry e ++ r) = some (e, r) := by
  obtain ⟨hty, hd⟩ := h
  unfold decEntry encEntry
  simp only [List.append_assoc, decU64_enc]
  have hty' : uint.Z (W64 (sint.Z e.Type')) ≤ 2 := by word
  rw [if_pos hty', decB_putB _ _ hd]
  have : W32 (uint.Z (W64 (sint.Z e.Type'))) = e.Type' := by word
  rw [this]

theorem decEntries_enc [GooseExts] (es : List EntryM) (r : List w8) (h : ∀ e ∈ es, EntWf e) :
    decEntries es.length (encEntries es ++ r) = some (es, r) := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    simp only [List.length_cons, decEntries, encEntries, List.append_assoc,
      decEntry_enc e _ (h e (List.mem_cons_self ..)),
      ih (fun e' he' => h e' (List.mem_cons_of_mem _ he'))]

theorem decAuto_enc (a : Bool) (r : List w8) : decAuto (autoB a :: r) = some (a, r) := by
  cases a <;> simp [decAuto, autoB]

theorem decConf_enc (c : ConfStateM) (r : List w8) (h : ConfWf c) :
    decConf (encConf c ++ r) = some (c, r) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  unfold decConf encConf
  simp only [List.append_assoc, decIDs_enc _ _ h1, decIDs_enc _ _ h2, decIDs_enc _ _ h3,
    decIDs_enc _ _ h4, List.singleton_append, decAuto_enc]

theorem decSnap_enc (s : SnapshotM) (r : List w8) (h : SnapWf s) :
    decSnap (encSnap s ++ r) = some (s, r) := by
  unfold decSnap encSnap
  simp only [List.append_assoc, decU64_enc, decConf_enc _ _ h.1, decB_putB _ _ h.2]

/-- **The storage file's round trip**: `openStorage`'s reading of the bytes `encode` wrote. -/
theorem decStor_enc [GooseExts] (f : StorFile) (h : StorWf f) :
    decStor (encStor f) = some f := by
  obtain ⟨hs, he, hn⟩ := h
  unfold decStor encStor
  have hnn : uint.nat (W64 f.ents.length) = f.ents.length := by word
  simp only [decU64_enc, decSnap_enc _ _ hs, hnn]
  have := decEntries_enc f.ents [] he
  rw [List.append_nil] at this
  rw [this]; rfl

/-! ## Injectivity -/

/-- Two well-formed contents with the same bytes are equal. -/
theorem encStor_inj [GooseExts] (f f' : StorFile) (h : StorWf f) (h' : StorWf f')
    (he : encStor f = encStor f') : f = f' := by
  have := decStor_enc f h
  rw [he, decStor_enc f' h'] at this
  exact (Option.some.inj this).symm

/-! ## Lengths -/

theorem u64sLe_snoc (xs : List w64) (x : w64) : u64sLe (xs ++ [x]) = u64sLe xs ++ u64Le x := by
  induction xs with
  | nil => simp [u64sLe]
  | cons y xs ih => simp only [List.cons_append, u64sLe, ih, List.append_assoc]

@[simp] theorem putB_length (x : List w8) : (putB x).length = 8 + x.length := by
  simp [putB, u64Le_length]

theorem u64sLe_length (xs : List w64) : (u64sLe xs).length = 8 * xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [u64sLe, List.length_append, u64Le_length, ih, List.length_cons]; omega

@[simp] theorem encIDs_length (ids : List w64) : (encIDs ids).length = 8 + 8 * ids.length := by
  simp [encIDs, u64Le_length, u64sLe_length]

end EtcdGrove.kvdurable
end Perennial
