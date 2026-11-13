/-
**`ReadAll`'s fold over the decoded records** (pure; W3 of `notes/wal-fsext-plan.md`, §4.2). The Go
reference is `(*WAL).ReadAll` at the pin (fork commit `0b50f04262d9`, S/ = `server/storage/wal/`,
S/wal.go:505-676): the loop over `decoder.Decode` (:523-596), the stop check (:598-611), the
`ErrSnapshotNotFound` of the fork's `1aaca041c` (:640-643, :665-669). The effects after the loop
(the zeroing F-Z, its `Fdatasync`, the directory syncs F-N4, `newFileEncoder`) only add error
returns; they are not here.

`readAllFold` is the loop as a function of the records the decoder accepted (`walDecodeFiles`,
`WalEncFiles.lean`; the CRC-record check, :556-564, is the decoder layer's `crcRec` stop) and the
decoder's stop. The theorems: over the records of a WAL's files from a cut file on
(`walDecodeFiles_suffix`'s), the fold returns exactly `walReadFrom` (`readAllFold_from`,
`readAllFold_from_complete`); over the records from the first file, it returns the fold at the fixed
base `s` (`walReadAt`), which is `walRead` when `walRead` succeeds and `walCommitLe` holds
(`readAllFold_zero_eq`), but not always: `readAllFold_zero_dev` is a history where `ReadAll`
succeeds and `walRead` fails.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.WalEncSuffix
public import Proof.go_etcd_io.etcd.server.v3.storage.WalHistLemmas

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace WalEnc

open go_etcd_io.raft.v3

section fold
variable [GooseExts]

/-- **The unmarshalling of the records' payloads** (parameters, as `WalMarshal`). `decEntry`:
`MustUnmarshalEntry` (S/wal.go:525; `none` where it panics); `decState`: `MustUnmarshalState`
(:546); `decSnap`: `pbutil.MustUnmarshalMessage(&snap, rec.Data)` into a `walpb.Snapshot`, its
`(GetIndex(), GetTerm())` (:567-568). -/
structure WalUnmarshal where
  decEntry : List w8 → Option EntryM
  decState : List w8 → Option HardStateM
  decSnap : List w8 → Option (w64 × w64)

/-- **The round trips** the fold needs, against the marshalling `M`. -/
structure WalUnmarshal.Ok (U : WalUnmarshal) (M : WalMarshal) : Prop where
  entry : ∀ e, U.decEntry (M.encEntry e) = some e
  state : ∀ h, U.decState (M.encState h) = some h
  snap : ∀ m, U.decSnap (M.encSnap m) = some (m.Index', m.Term')
  snap0 : U.decSnap M.snap0 = some (W64 0, W64 0)

/-- **What `ReadAll` returns an error for**, by the line that returns it. -/
inductive ReadAllErr where
  /-- `MustUnmarshalEntry`/`MustUnmarshalState`/`MustUnmarshalMessage` panic (:525, :546, :568). -/
  | panic
  /-- `ErrSliceOutOfRange` (:533-539): an entry more than one past the entries read. -/
  | sliceOutOfRange
  /-- `ErrMetadataConflict` (:549-552). -/
  | metadataConflict
  /-- `ErrSnapshotMismatch` (:573-576): a record of the start's index with another term. -/
  | snapshotMismatch
  /-- `unexpected block type` (:592-594). -/
  | unexpectedType
  /-- The decoder's error, not accepted by the mode (:598-611). -/
  | stop (s : WalStop)
  /-- `ErrSnapshotNotFound` (:640-643, :665-669): no record of the start snapshot. -/
  | snapshotNotFound

/-- The loop's variables: `metadata` (`none` while nil), `state`, `ents`, `match`. (`w.enti` and
`w.snapi` are only written.) -/
structure RAState where
  md : Option (List w8)
  hs : HardStateM
  ents : List EntryM
  matched : Bool

/-- The variables before the loop (:506, :517). -/
def raInit : RAState := ⟨none, hsZero, [], false⟩

/-- **One iteration of the loop** on a record `(type, data)` with the start snapshot `s = (index,
term)` (`w.start`). An entry (:524-542): `readEnt` is exactly the code (an index at or below the
start's empties `ents`, :527-529; above it, the offset `index - start - 1` must be at most
`len(ents)`, :533, and `ents[:offset]` gets it appended, :541). A state (:545-546) replaces `state`.
Metadata (:548-553) must equal the earlier one. A CRC record (:555-564): checked by the decoder layer
(`decStep`'s `crcRec`). A snapshot (:566-587): one of the start's index must have its term, sets
`match`, and empties `ents` if its index is above `state.Commit`. -/
def raStep (U : WalUnmarshal) (s : w64 × w64) (st : RAState) (r : w64 × List w8) :
    Except ReadAllErr RAState :=
  if r.1 = entryType then
    match U.decEntry r.2 with
    | none => .error .panic
    | some e =>
      match readEnt (uint.nat s.1) st.ents e with
      | none => .error .sliceOutOfRange
      | some ents => .ok { st with ents := ents }
  else if r.1 = stateType then
    match U.decState r.2 with
    | none => .error .panic
    | some h => .ok { st with hs := h }
  else if r.1 = metadataType then
    match st.md with
    | some d => if d = r.2 then .ok st else .error .metadataConflict
    | none => .ok { st with md := some r.2 }
  else if r.1 = crcType then .ok st
  else if r.1 = snapshotType then
    match U.decSnap r.2 with
    | none => .error .panic
    | some p =>
      if p.1 = s.1 then
        if p.2 = s.2 then
          .ok { st with matched := true,
                        ents := if uint.nat st.hs.Commit' < uint.nat p.1 then [] else st.ents }
        else .error .snapshotMismatch
      else .ok st
  else .error .unexpectedType

/-- **`ReadAll`'s result as a function of the decoded records `recs` and the decoder's stop**, in
write mode (`write`, `w.tail() != nil`) or read mode: the loop, the stop check (write mode: only
`io.EOF`, :606-611; read mode: `io.EOF` or `io.ErrUnexpectedEOF`, :600-605), then
`ErrSnapshotNotFound` without a match. Success returns `(metadata, state, ents)`. -/
def readAllFold (U : WalUnmarshal) (s : w64 × w64) (write : Bool) (recs : List WalRec)
    (stop : WalStop) : Except ReadAllErr (List w8 × HardStateM × List EntryM) := do
  let st ← (recs.map (fun r => (r.typ, r.data))).foldlM (raStep U s) raInit
  if write then
    if stop ≠ .eof then throw (.stop stop)
  else
    if stop ≠ .eof ∧ stop.unexpectedEOF = false then throw (.stop stop)
  if st.matched = false then throw .snapshotNotFound
  return (st.md.getD [], st.hs, st.ents)

/-- **The read at the fixed base `s` from position `k`** (what `ReadAll` computes, with the files
from position `k` and the start `s`): the fold of `walReadFrom`, from `s` rather than from the
newest record. At `k ≥ 1` with `s` the newest valid pair it is `walReadFrom` (`walReadAt_from`). -/
def walReadAt (I : WalHist) (k : Nat) (s : w64 × w64) : Option StorContents :=
  walFoldChkFrom ⟨walLastHS (I.take k), none, entryID.mk s.2 s.1, []⟩
    ((I.drop k).filter (walKeep (uint.nat (walLastHS I).Commit')))

/-! ## The loop over an operation's records -/

/-- Whether an operation is a snapshot record of index `i`. -/
def snapAt (i : w64) : WalOp → Bool
  | .snap m => decide (m.Index' = i)
  | .save _ _ => false

/-- **The loop over one operation's records** (`opDs`), as one step (`raStep_opDs`). -/
def goOp (s : w64 × w64) (st : RAState) : WalOp → Except ReadAllErr RAState
  | .save h es =>
    match es.foldlM (fun ents e => readEnt (uint.nat s.1) ents e) st.ents with
    | none => .error .sliceOutOfRange
    | some ents => .ok { st with ents := ents, hs := phsNext st.hs h }
  | .snap m =>
    if m.Index' = s.1 then
      if m.Term' = s.2 then
        .ok { st with matched := true,
                      ents := if uint.nat st.hs.Commit' < uint.nat m.Index' then [] else st.ents }
      else .error .snapshotMismatch
    else .ok st

theorem except_bind_ok {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {b : β} :
    (x >>= f) = .ok b ↔ ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x <;> simp [bind, Except.bind]

theorem hsEmptyP_eq {h : HardStateM} (he : hsEmptyP h) : h = hsZero := by
  obtain ⟨t, v, c⟩ := h
  obtain ⟨h1, h2, h3⟩ := he
  simp only at h1 h2 h3; subst h1 h2 h3; rfl

theorem raStep_entries (U : WalUnmarshal) (M : WalMarshal) (hU : U.Ok M) (s : w64 × w64) :
    ∀ (es : List EntryM) (st : RAState),
    (es.map (fun e => (entryType, M.encEntry e))).foldlM (raStep U s) st =
      match es.foldlM (fun ents e => readEnt (uint.nat s.1) ents e) st.ents with
      | none => .error .sliceOutOfRange
      | some ents => .ok { st with ents := ents } := by
  intro es
  induction es with
  | nil => intro st; rfl
  | cons e es ih =>
    intro st
    simp only [List.map_cons, List.foldlM_cons]
    have : raStep U s st (entryType, M.encEntry e) =
        match readEnt (uint.nat s.1) st.ents e with
        | none => .error .sliceOutOfRange
        | some ents => .ok { st with ents := ents } := by
      simp [raStep, hU.entry]
    rw [this]
    cases readEnt (uint.nat s.1) st.ents e with
    | none => rfl
    | some ents =>
      show (es.map _).foldlM (raStep U s) { st with ents := ents } = _
      rw [ih]
      simp only [Option.bind_eq_bind, Option.bind_some]

theorem raStep_opDs (U : WalUnmarshal) (M : WalMarshal) (hU : U.Ok M) (s : w64 × w64)
    (st : RAState) (o : WalOp) : (opDs M o).foldlM (raStep U s) st = goOp s st o := by
  cases o with
  | save h es =>
    simp only [opDs, List.foldlM_append, raStep_entries U M hU, goOp]
    cases es.foldlM (fun ents e => readEnt (uint.nat s.1) ents e) st.ents with
    | none => rfl
    | some ents =>
      show (if hsEmptyP h then [] else [(stateType, M.encState h)]).foldlM (raStep U s) _ = _
      by_cases he : hsEmptyP h
      · have hp : phsNext st.hs h = st.hs := phsNext_empty _ _ he
        simp [he, hp]; rfl
      · have hp : phsNext st.hs h = h := by unfold phsNext; exact ite_eq_right_iff.mpr (fun h1 => absurd h1 he)
        simp [he, hp, raStep, hU.state, stateType, entryType]
  | snap m =>
    simp [opDs, goOp, raStep, hU.snap, snapshotType, entryType, stateType, metadataType, crcType]

theorem raStep_flatMap (U : WalUnmarshal) (M : WalMarshal) (hU : U.Ok M) (s : w64 × w64) :
    ∀ (L : WalHist) (st : RAState),
    (L.flatMap (opDs M)).foldlM (raStep U s) st = L.foldlM (goOp s) st := by
  intro L
  induction L with
  | nil => intro st; rfl
  | cons o L ih =>
    intro st
    simp only [List.flatMap_cons, List.foldlM_append, List.foldlM_cons, raStep_opDs U M hU, ih]

/-! ## The main theorems -/

/-- **From a cut file: `ReadAll` succeeds only with `walReadFrom`'s read.** The WAL's segments are
`Spre ++ Ss`, the records read those after `Spre`'s (`walDecodeFiles_suffix`, with
`Ss = Smid ++ [histCut M S n]`), the start the newest valid pair of the history from the read's
position (`Open`'s, `walValidSnaps`). -/
theorem readAllFold_from {C : WalCodec} {M : WalMarshal} {U : WalUnmarshal} (hU : U.Ok M)
    (md : List w8) (Spre Ss : List WalHist) (hpre : Spre ≠ []) (s : w64 × w64) (write : Bool)
    (stop : WalStop) (r : List w8 × HardStateM × List EntryM)
    (hs : some s = walNewestPair (walValidSnaps (Spre ++ Ss).flatten Spre.flatten.length))
    (hok : readAllFold U s write
      ((recsOfSegs C M md (Spre ++ Ss)).drop (recsOfSegs C M md Spre).length) stop = .ok r) :
    ∃ σ, walReadFrom (Spre ++ Ss).flatten Spre.flatten.length = some σ ∧ r = (md, σ.hs, σ.ents) := by
  sorry

/-- **… and it succeeds whenever `walReadFrom` does**, the stop accepted, unless a record of the
start's index has another term (`ErrSnapshotMismatch`, which `walReadFrom` does not check). -/
theorem readAllFold_from_complete {C : WalCodec} {M : WalMarshal} {U : WalUnmarshal} (hU : U.Ok M)
    (md : List w8) (Spre Ss : List WalHist) (hpre : Spre ≠ []) (s : w64 × w64) (write : Bool)
    (stop : WalStop) (σ : StorContents)
    (hs : some s = walNewestPair (walValidSnaps (Spre ++ Ss).flatten Spre.flatten.length))
    (hterm : ∀ m, WalOpG.snap m ∈ Ss.flatten → m.Index' = s.1 → m.Term' = s.2)
    (hstop : stop = .eof ∨ (write = false ∧ stop.unexpectedEOF = true))
    (h : walReadFrom (Spre ++ Ss).flatten Spre.flatten.length = some σ) :
    readAllFold U s write
      ((recsOfSegs C M md (Spre ++ Ss)).drop (recsOfSegs C M md Spre).length) stop =
      .ok (md, σ.hs, σ.ents) := by
  sorry

/-- **From the first file: `ReadAll` succeeds only with the read at the fixed base `s`.** -/
theorem readAllFold_zero {C : WalCodec} {M : WalMarshal} {U : WalUnmarshal} (hU : U.Ok M)
    (md : List w8) (Ss : List WalHist) (s : w64 × w64) (write : Bool)
    (stop : WalStop) (r : List w8 × HardStateM × List EntryM)
    (hs : some s = walNewestPair (walValidSnaps Ss.flatten 0))
    (hok : readAllFold U s write (recsOfSegs C M md Ss) stop = .ok r) :
    ∃ σ, walReadAt Ss.flatten 0 s = some σ ∧ r = (md, σ.hs, σ.ents) := by
  sorry

/-- **… which is `walRead`'s when that succeeds** (`walCommitLe`: W4b's C2 premise). -/
theorem readAllFold_zero_eq {C : WalCodec} {M : WalMarshal} {U : WalUnmarshal} (hU : U.Ok M)
    (md : List w8) (Ss : List WalHist) (s : w64 × w64) (write : Bool)
    (stop : WalStop) (r : List w8 × HardStateM × List EntryM) (σ : StorContents)
    (hs : some s = walNewestPair (walValidSnaps Ss.flatten 0))
    (hcl : walCommitLe Ss.flatten) (h : walRead Ss.flatten = some σ)
    (hok : readAllFold U s write (recsOfSegs C M md Ss) stop = .ok r) :
    r = (md, σ.hs, σ.ents) := by
  sorry

/-- **The deviation: `ReadAll` from the first file succeeds where `walRead` fails.** `Save` of the
hard state `{Term 1, Commit 5}` with the entry 6, then `SaveSnapshot({Index 5, Term 1})`: the start
is `(5, 1)` (`walValidSnaps`'s newest: `5 ≤` the commit), and `ReadAll` keeps the entry 6 (offset 0
from the start), where `walRead`'s fold, at base 0 when it meets the entry, fails
(`ErrSliceOutOfRange`'s case). `walCommitLe` holds (vacuously: the fold fails). -/
theorem readAllFold_zero_dev {C : WalCodec} {M : WalMarshal} {U : WalUnmarshal} (hU : U.Ok M)
    (md : List w8) (cs : ConfStateM) (ty : raftpb.EntryType) :
    let h : HardStateM := ⟨W64 1, W64 0, W64 5⟩
    let e : EntryM := ⟨W64 1, W64 6, ty, []⟩
    let I : WalHist := [.save h [e], .snap ⟨cs, W64 5, W64 1⟩]
    some (W64 5, W64 1) = walNewestPair (walValidSnaps I 0) ∧ walCommitLe I ∧
    walRead I = none ∧
    readAllFold U (W64 5, W64 1) true (recsOfSegs C M md [I]) .eof = .ok (md, h, [e]) := by
  sorry

end fold

end WalEnc
end EtcdGrove
end Perennial
