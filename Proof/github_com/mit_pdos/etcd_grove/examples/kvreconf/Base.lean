/-
Lean-first (no Rocq counterpart).

# The reconfiguring key-value store: package initialization and the pure model (2026-10-29,
track C of `notes/raft-unified-plan.md`)

`examples/kvreconf` has no package-level variable (its constants are untyped or typed constants),
so its package fact is `True`; the packages it imports have theirs.

The pure model is `examples/kv`'s (`Proof/github_com/mit_pdos/etcd_grove/examples/kv/Base.lean`),
copied under the namespace `EtcdGrove.kvreconf` (the two examples' proofs are linked in one Lean run
by `etc/tcb-report.py`, so their names must differ) and changed where the Go differs: an
operation's encoding (`encodeOp`: its id, little-endian, the kind, the key's length, the key, the
value; kv's has the proposing replica and its sequence number in place of the id), what `decode`
reads back (`decodeOp`), and the store's state machine (`kvNext`: a `Put` sets its key, anything
else leaves the store; kvreconf has no `Append`).
-/
module

public import Spec.go_etcd_io.raft.v3.Api
public import Proof.go_etcd_io.raft.v3.Base
public import GeneratedProof.github_com.mit_pdos.etcd_grove.examples.kvreconf
public import Perennial.Proof.encoding.binary
public import Proof.github_com.mit_pdos.etcd_grove.examples.lintest.Base
public import Perennial.Proof.github_com.goose_lang.primitive.Base
public import Proof.github_com.mit_pdos.gokv.trusted_proph.Base
public import Perennial.Proof.context.Base
public import Perennial.Proof.time.Base
public import Perennial.Proof.fmt.Base
public import Perennial.Proof.sync.atomic.Base
public import Proof.github_com.anishathalye.porcupine.Defs

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace github_com.mit_pdos.etcd_grove.examples.kvreconf

section init
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvreconf.Assumptions]

instance isPkgInit_inst :
    IsPkgInit (IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.kvreconf :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.kvreconf :=
  build_get_is_pkg_init_wf

end init

end github_com.mit_pdos.etcd_grove.examples.kvreconf

namespace EtcdGrove.kvreconf

/-- The store's `quietLogger` type. -/
abbrev qLoggerTy [GooseExts] [GoGlobalContext] : go.GoType :=
  github_com.mit_pdos.etcd_grove.examples.kvreconf.quietLogger.ty

/-- `quietLogger{}`. -/
abbrev qLoggerV [GooseExts] : github_com.mit_pdos.etcd_grove.examples.kvreconf.quietLogger :=
  github_com.mit_pdos.etcd_grove.examples.kvreconf.quietLogger.mk

/-- `quietLogger{}` as a `raft.Logger`. -/
def qLogger [GooseExts] [GoGlobalContext] : GoInterfaceOk := interface.mk qLoggerTy #qLoggerV

/-! ## The pure model -/

/-- `opPut`. -/
def opPutB : w8 := W8 1

/-- `opGet`. -/
def opGetB : w8 := W8 2

/-- `opRead`: the kind of a read's context. -/
def opReadB : w8 := W8 3

/-- What `encode(id, kind, key, val)` returns: the 17-byte header (the id, the kind, the key's
length), the key, the value. -/
def encodeOp (id : w64) (kind : w8) (key val : List w8) : List w8 :=
  u64Le id ++ [kind] ++ u64Le (W64 key.length) ++ key ++ val

/-- What `decode` reads back: `none` for fewer than 17 bytes, or a key length past the end. -/
def decodeOp (d : List w8) : Option (w64 × w8 × List w8 × List w8) :=
  if 17 ≤ d.length then
    if uint.Z (leToU64 ((d.drop 9).take 8)) ≤ (d.length : Int) - 17 then
      some (leToU64 (d.take 8), d.getD 8 (W8 0),
        (d.drop 17).take (uint.nat (leToU64 ((d.drop 9).take 8))),
        (d.drop 17).drop (uint.nat (leToU64 ((d.drop 9).take 8))))
    else none
  else none

/-- What `readCtx(replica, seq, key)` returns: the replica, then the read's encoding. -/
def readCtxB (replica seq : w64) (key : List w8) : List w8 :=
  u64Le replica ++ encodeOp seq opReadB key []

/-- What `decodeReadCtx` reads back. -/
def decodeReadCtxB (b : List w8) : Option (w64 × w64 × List w8) :=
  if 8 ≤ b.length then
    match decodeOp (b.drop 8) with
    | some (seq, kind, key, _) => if kind = opReadB then some (leToU64 (b.take 8), seq, key) else none
    | none => none
  else none

/-- The store's state: every key's value (`[]`, the empty string, for a key never set). -/
abbrev KVMap := List w8 → List w8

/-- The empty store. -/
def kvEmpty : KVMap := fun _ => []

/-- `m` with `k` set to `v`. -/
def kvUpd (m : KVMap) (k v : List w8) : KVMap := fun k' => if k' = k then v else m k'

/-- The store after an operation of kind `kind` on `key` with value `val`: a `Put` sets the
key, anything else (a `Get`) leaves it. -/
def kvNext (kind : w8) (key val : List w8) (m : KVMap) : KVMap :=
  if kind = opPutB then kvUpd m key val else m

/-- One datum of the client log applied to the store. -/
def kvApply (m : KVMap) (d : List w8) : KVMap :=
  match decodeOp d with
  | some (_, k, key, v) => kvNext k key v m
  | none => m

/-- A datum's key (the empty key for a datum that is no operation): what its operation
answers, the key's value after it. -/
def dkey (d : List w8) : List w8 :=
  match decodeOp d with
  | some (_, _, key, _) => key
  | none => []

/-- The store after the client log `L`. -/
def kvFold (L : List (List w8)) : KVMap := L.foldl kvApply kvEmpty

/-- `v` is what the operation `d` answers in the history `H`: its key's value right after `d`,
which occurs in `H` after the history `H0` (and not in `H0`: the first occurrence). -/
def AnsOk (H : List (List w8)) (d v : List w8) : Prop :=
  ∃ H0, H0 ++ [d] <+: H ∧ d ∉ H0 ∧ v = kvFold (H0 ++ [d]) (dkey d)

/-- A table of answers (a lookup function `f`) for the history `H`: it has exactly the decodable
data of `H`, each with its answer (`AnsOk`). -/
def AnsTab (f : List w8 → Option (List w8)) (H : List (List w8)) : Prop :=
  (∀ d, (f d).isSome ↔ d ∈ H ∧ (decodeOp d).isSome) ∧ ∀ d v, f d = some v → AnsOk H d v

/-- `applyOp`'s table: the decodable data of the client log `L`, each mapped to its answer. -/
def AppliedOk (A : GMap (List w8) (List w8)) (L : List (List w8)) : Prop :=
  AnsTab (fun d => A !! d) L

theorem ansOk_mono (H H' : List (List w8)) (d v : List w8) (h : H <+: H') (ha : AnsOk H d v) :
    AnsOk H' d v := by
  obtain ⟨H0, h1, h2, h3⟩ := ha
  exact ⟨H0, h1.trans h, h2, h3⟩

theorem ansOk_last (H : List (List w8)) (d : List w8) (h : d ∉ H) :
    AnsOk (H ++ [d]) d (kvFold (H ++ [d]) (dkey d)) :=
  ⟨H, List.prefix_refl _, h, rfl⟩

theorem encodeOp_length (id : w64) (kind : w8) (key val : List w8) :
    (encodeOp id kind key val).length = 17 + key.length + val.length := by
  simp [encodeOp, u64Le_length]; omega

theorem decodeOp_encodeOp (id : w64) (kind : w8) (key val : List w8)
    (hk : (key.length : Int) < 2 ^ 64) :
    decodeOp (encodeOp id kind key val) = some (id, kind, key, val) := by
  have hkz : uint.Z (W64 key.length) = key.length := by word
  have hkn : uint.nat (W64 key.length) = key.length := by word
  have hA : (u64Le id ++ [kind]).length = 9 := by simp [u64Le_length]
  have h1 : (encodeOp id kind key val).take 8 = u64Le id := by
    simp [encodeOp, u64Le_length]
  have h3 : (encodeOp id kind key val).getD 8 (W8 0) = kind := by
    simp [encodeOp, List.getD_eq_getElem?_getD, u64Le_length]
  have h4 : ((encodeOp id kind key val).drop 9).take 8 = u64Le (W64 key.length) := by
    have : encodeOp id kind key val =
        (u64Le id ++ [kind]) ++ (u64Le (W64 key.length) ++ (key ++ val)) := by
      simp [encodeOp]
    rw [this, List.drop_left' hA]
    exact List.take_left' (u64Le_length _)
  have h5 : (encodeOp id kind key val).drop 17 = key ++ val := by
    have : encodeOp id kind key val =
        (u64Le id ++ [kind] ++ u64Le (W64 key.length)) ++ (key ++ val) := by
      simp [encodeOp]
    rw [this, List.drop_left' (by simp [u64Le_length])]
  have hl := encodeOp_length id kind key val
  unfold decodeOp
  rw [h4, u64Le_to_word, h5, hkn, hl, if_pos (by omega), if_pos (by rw [hkz]; push_cast; omega),
    h1, h3, u64Le_to_word, List.take_left' rfl, List.drop_left' rfl]

theorem kvFold_snoc (L : List (List w8)) (d : List w8) :
    kvFold (L ++ [d]) = kvApply (kvFold L) d := by
  simp [kvFold, List.foldl_append]

theorem kvApply_encodeOp (m : KVMap) (id : w64) (kind : w8) (key val : List w8)
    (hk : (key.length : Int) < 2 ^ 64) :
    kvApply m (encodeOp id kind key val) = kvNext kind key val m := by
  simp [kvApply, decodeOp_encodeOp _ _ _ _ hk]

theorem dkey_encodeOp (id : w64) (kind : w8) (key val : List w8)
    (hk : (key.length : Int) < 2 ^ 64) :
    dkey (encodeOp id kind key val) = key := by
  simp [dkey, decodeOp_encodeOp _ _ _ _ hk]

theorem kvApply_none (m : KVMap) (d : List w8) (h : decodeOp d = none) : kvApply m d = m := by
  simp [kvApply, h]

theorem kvUpd_same (m : KVMap) (k v : List w8) : kvUpd m k v k = v := by
  simp [kvUpd]

theorem kvUpd_other (m : KVMap) (k k' v : List w8) (h : k' ≠ k) : kvUpd m k v k' = m k' := by
  simp [kvUpd, h]

/-! ## A snapshot's data (D22 S-r, 2026-10-21)

What a replica's snapshot holds (`encodeState`, `kv.go`): the store's replicated state -- every
key's value and the operations applied, each with its answer (2026-10-22) -- as bytes
(`encState`): each map as `putMap` writes it (`encMap`), its count (8 bytes, little-endian), then
each key and its value length-prefixed (`putB`). `putMap` writes the keys in increasing order,
so that the bytes are a function of the state; the proof needs only that they are *some* order
of them (`StateEnc`: any list of the bindings, without repeated keys), which `getMap` reads back
whatever the order.

**The cluster's data certificate** (`kvSnapOk`, what each record of the store's registry of the
snapshots made promises of its data: `kvSnapRecOk`, `kvSnapInv`, `Defs.lean`): the data of a
snapshot at index `i` encodes the replicated state of the committed log prefix of length `i` --
`StateEnc` of its client history, the first occurrences of its entries' client data (`odOf`,
`logHist`). A replica records it where it takes a snapshot (`CreateSnapshot`, of its applied
prefix: `runOwn`'s; `kv_snap_make`), and the one that installs it reads it back at the prefix it
is handed (`kv_snap_read`; committed prefixes of one length are equal). -/

section snapdata
variable [GooseExts]

/-- An entry's client datum: a normal entry's non-empty data, else none (a filler, a conf change). -/
def odOf (e : LogEntry) : Option (List w8) :=
  if e.type = W32 0 ∧ e.data ≠ [] then some e.data else none

/-- A filler has no client datum. -/
theorem odOf_filler (e : LogEntry) (h : e.isFiller) : odOf e = none := by
  unfold odOf; rw [ite_eq_right_iff]; intro h'; exact absurd h.1 h'.2

end snapdata

/-! ## The client history (2026-10-27: until then raft's `firstOcc`)

The data of committed client entries in commit order, first occurrences only, given each entry's
datum (`none` for an entry that carries none, `odOf`). -/

/-- One entry's datum added to the history: a new one is appended; a repeated one, or none,
leaves it. -/
def histStep (L : List (List w8)) : Option (List w8) → List (List w8)
  | none => L
  | some d => if d ∈ L then L else L ++ [d]

/-- The history of the entries' data `ods`. -/
def histOf (ods : List (Option (List w8))) : List (List w8) := ods.foldl histStep []

theorem histOf_snoc (ods : List (Option (List w8))) (o : Option (List w8)) :
    histOf (ods ++ [o]) = histStep (histOf ods) o := by
  simp [histOf, List.foldl_append]

theorem histStep_prefix (L : List (List w8)) (o : Option (List w8)) : L <+: histStep L o := by
  cases o with
  | none => exact List.prefix_refl _
  | some d =>
    by_cases h : d ∈ L
    · simp only [histStep, h, ite_true]; exact List.prefix_refl _
    · simp only [histStep, h, ite_false]; exact List.prefix_append _ _

theorem foldl_histStep_prefix (L : List (List w8)) (b : List (Option (List w8))) :
    L <+: b.foldl histStep L := by
  induction b generalizing L with
  | nil => exact List.prefix_refl _
  | cons o b ih => exact (histStep_prefix L o).trans (ih _)

theorem histOf_append_prefix (a b : List (Option (List w8))) :
    histOf a <+: histOf (a ++ b) := by
  unfold histOf; rw [List.foldl_append]; exact foldl_histStep_prefix _ _

theorem mem_foldl_histStep (L : List (List w8)) (b : List (Option (List w8))) (d : List w8) :
    d ∈ b.foldl histStep L ↔ d ∈ L ∨ some d ∈ b := by
  induction b generalizing L with
  | nil => simp
  | cons o b ih =>
    simp only [List.foldl_cons, List.mem_cons]
    rw [ih]
    cases o with
    | none => simp [histStep]
    | some d' =>
      by_cases h : d' ∈ L
      · simp only [histStep, h, ite_true]
        constructor
        · rintro (h1 | h1)
          · exact .inl h1
          · exact .inr (.inr h1)
        · rintro (h1 | h1 | h1)
          · exact .inl h1
          · cases h1; exact .inl h
          · exact .inr h1
      · simp only [histStep, h, ite_false, List.mem_append, List.mem_singleton]
        constructor
        · rintro ((h1 | h1) | h1)
          · exact .inl h1
          · subst h1; exact .inr (.inl rfl)
          · exact .inr (.inr h1)
        · rintro (h1 | h1 | h1)
          · exact .inl (.inl h1)
          · cases h1; exact .inl (.inr rfl)
          · exact .inr h1

theorem mem_histOf (ods : List (Option (List w8))) (d : List w8) :
    d ∈ histOf ods ↔ some d ∈ ods := by
  unfold histOf; rw [mem_foldl_histStep]; simp

theorem nodup_foldl_histStep (L : List (List w8)) (b : List (Option (List w8))) :
    L.Nodup → (b.foldl histStep L).Nodup := by
  induction b generalizing L with
  | nil => exact id
  | cons o b ih =>
    intro hL
    apply ih
    cases o with
    | none => exact hL
    | some d =>
      by_cases h : d ∈ L
      · simp only [histStep, h, ite_true]; exact hL
      · simp only [histStep, h, ite_false]
        exact List.nodup_append.mpr ⟨hL, List.nodup_cons.mpr ⟨by simp, List.nodup_nil⟩,
          fun a ha b hb => by
            simp only [List.mem_singleton] at hb; subst hb; intro e; subst e; exact h ha⟩

theorem histOf_nodup (ods : List (Option (List w8))) : (histOf ods).Nodup :=
  nodup_foldl_histStep [] ods List.nodup_nil

/-- In a list without duplicates, what comes before `d` is determined. -/
theorem hist_prefix_before_unique (L L0 L1 : List (List w8)) (d : List w8) (Hnd : L.Nodup)
    (H0 : L0 ++ [d] <+: L) (H1 : L1 ++ [d] <+: L) : L0 = L1 := by
  have k0 : L[L0.length]? = some d := by
    obtain ⟨r, rfl⟩ := H0; simp
  have k1 : L[L1.length]? = some d := by
    obtain ⟨r, rfl⟩ := H1; simp
  obtain ⟨h0lt, h0e⟩ := List.getElem?_eq_some_iff.mp k0
  obtain ⟨h1lt, h1e⟩ := List.getElem?_eq_some_iff.mp k1
  have hlen := (List.Nodup.getElem_inj Hnd).mp (h0e.trans h1e.symm)
  have e0 := List.prefix_iff_eq_take.mp ((List.prefix_append L0 [d]).trans H0)
  have e1 := List.prefix_iff_eq_take.mp ((List.prefix_append L1 [d]).trans H1)
  rw [e0, e1, hlen]

/-- The history of a log: its entries' data's (`odOf`). -/
def logHist [GooseExts] (l : List LogEntry) : List (List w8) := histOf (l.map odOf)

theorem foldl_histStep_opsOf [GooseExts] (l : List LogEntry) (L : List (List w8)) :
    ((opsOf l).map odOf).foldl histStep L = (l.map odOf).foldl histStep L := by
  induction l generalizing L with
  | nil => rfl
  | cons e l ih =>
    unfold opsOf at ih ⊢
    rw [List.filter_cons]
    split
    · simp only [List.map_cons, List.foldl_cons]; exact ih _
    · rename_i hk
      have hn : odOf e = none := by
        unfold odOf; rw [ite_eq_right_iff]; rintro ⟨h1, h2⟩
        simp [LogEntry.isFiller, LogEntry.isEmptyV2, h2] at hk
      simp only [List.map_cons, List.foldl_cons, hn, histStep]; exact ih L

/-- The history of a log is that of its requested entries (a filler carries no datum). -/
theorem logHist_opsOf [GooseExts] (l : List LogEntry) :
    logHist (opsOf l) = logHist l := by
  unfold logHist histOf; exact foldl_histStep_opsOf l []

theorem logHist_prefix [GooseExts] (a b : List LogEntry) (h : a <+: b) :
    logHist a <+: logHist b := by
  obtain ⟨c, rfl⟩ := h
  unfold logHist; rw [List.map_append]; exact histOf_append_prefix _ _
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
    · subst hk; simp [List.lookup]
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
applied, each with its answer; 2026-10-22: until then the operations alone). -/
def encState (kvs ops : List (List w8 × List w8)) : List w8 := encMap kvs ++ encMap ops

/-- What a list of bindings needs for `getMap` to read it back: no repeated key, and every
length (the count, each key's and value's) a Go slice's. -/
def KVsWf (kvs : List (List w8 × List w8)) : Prop :=
  (kvs.map Prod.fst).Nodup ∧ (kvs.length : Int) < 2 ^ 63 ∧
    ∀ p ∈ kvs, (p.1.length : Int) < 2 ^ 63 ∧ (p.2.length : Int) < 2 ^ 63

/-- The bindings `kvs` are the map `K`'s, and well formed for `getMap` (`KVsWf`): what `putMap`
writes of `K` (in Go, in increasing order of the keys; see `less.spec`). -/
def KVsOf (K : GMap (List w8) (List w8)) (kvs : List (List w8 × List w8)) : Prop :=
  KVsWf kvs ∧ ∀ k, kvs.lookup k = K !! k

/-- **The bytes `d` encode the replicated state of the client history `H`** (see the section
header): bindings giving every key its value after `H` (a key they lack has `[]`, as
`runOwn`'s map), and bindings of exactly the decodable data of `H`, each to its answer (what
`apply` records, `AppliedOk`). -/
def StateEnc (H : List (List w8)) (d : List w8) : Prop :=
  ∃ (kvs ops : List (List w8 × List w8)),
    d = encState kvs ops ∧ KVsWf kvs ∧ KVsWf ops ∧
    (∀ k, ((kvs.lookup k).getD []) = kvFold H k) ∧
    AnsTab (fun o => ops.lookup o) H

/-- **The key-value cluster's data certificate** (what each record of the store's registry of the
snapshots made promises of its data, `kvSnapRecOk`; see the section header): the data of a snapshot at the end of the committed prefix `L` encodes the replicated
state of `L`. -/
def kvSnapOk [GooseExts] (L : List LogEntry) (d : List w8) : Prop :=
  StateEnc (logHist L) d


end EtcdGrove.kvreconf

end Perennial
