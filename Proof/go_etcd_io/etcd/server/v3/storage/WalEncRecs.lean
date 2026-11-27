/-
**The records a WAL's history writes, and what a crash image of them decodes to** (pure; W1 of
`notes/wal-fsext-plan.md`, §2.2-§2.3). The Go reference is the WAL at the pin (fork commit
`0b50f04262d9`): `Create` (wal.go:169-183: `saveCrc(0)`, the metadata record,
`SaveSnapshot({Index: 0, Term: 0})`), `Save` (:1093-1135: `saveEntry` per entry, then `saveState`
unless the hard state is empty, :1072-1091), `SaveSnapshot` (:1137-1162), `encode`
(encoder.go:66-98: the record's CRC is the chain's after its data, a CRC record's data nil).

One segment (the first file, no cut): `recsOf` is the records of the first file of a WAL whose
history `H` was written without a cut, `streamOf` their frames. The cut's headers (CRC, metadata,
state, wal.go:914-924) are for the multi-file stream.

The map from an accepted record prefix back to a history (`histCut`) is not a parse: it cuts `H` at
the prefix's length (the plan's §2.2), which is `walImg`'s shape.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.WalEncDecode
public import Proof.go_etcd_io.etcd.server.v3.storage.WalHist
public import Proof.go_etcd_io.etcd.server.v3.storage.WalNorm

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace WalEnc

open go_etcd_io.raft.v3

section recs
variable [GooseExts]

/-- **The marshalled payloads** (parameters: protobuf's models live elsewhere). `encEntry e`:
`pbutil.MustMarshalMessage(e)` of the entry (`saveEntry`, wal.go:1074); `encState h`: of the hard
state (`saveState`, :1088); `encSnap m al`: of the `walpb.Snapshot` `SaveSnapshot` is given for the
history's `.snap m al` (:1145); `snap0`: of `walpb.Snapshot{Index: 0, Term: 0}` (`Create`, :181). -/
structure WalMarshal where
  encEntry : EntryM → List w8
  encState : HardStateM → List w8
  encSnap : SnapshotMetadataM → Bool → List w8
  snap0 : List w8

/-- **An operation's records**, as (type, data): `Save(h, es)` an entry record per entry, then the
state record of `h` unless there are no entries and `h` is empty (the torn-`Save` fix, fork
`2bd3048d7`: a `Save` with entries ends with `encodeState`, of `h` or, when `h` is empty, of `w.state`,
which the normalized history `normH`, `WalNorm.lean`, puts in the op; without entries `saveState`
skips an empty `h`; `Save`'s shortcut writes nothing when both are empty, which this gives too);
`SaveSnapshot(m)` one snapshot record. -/
def opDs (M : WalMarshal) : WalOp → List (w64 × List w8)
  | .save h es => es.map (fun e => (entryType, M.encEntry e)) ++
      (if es = [] ∧ hsEmptyP h then [] else [(stateType, M.encState h)])
  | .snap m al => [(snapshotType, M.encSnap m al)]

/-- **The first file's header records** (`Create`, wal.go:174-183): the CRC record (data nil), the
metadata `md`, the initial snapshot record. -/
def hdrDs (M : WalMarshal) (md : List w8) : List (w64 × List w8) :=
  [(crcType, []), (metadataType, md), (snapshotType, M.snap0)]

/-- **The encoder's CRCs** (encoder.go:74-75): each record carries the chain's CRC after its data,
from the encoder's initial CRC `c`. -/
def chainRecs (C : WalCodec) : w32 → List (w64 × List w8) → List WalRec
  | _, [] => []
  | c, (t, d) :: ds => ⟨t, C.crc32c c d, d⟩ :: chainRecs C (C.crc32c c d) ds

/-- **The records of a WAL with metadata `md` and history `H`**, in one file (`Create`'s encoder
starts at CRC 0, wal.go:169). -/
def recsOf (C : WalCodec) (M : WalMarshal) (md : List w8) (H : WalHist) : List WalRec :=
  chainRecs C 0#32 (hdrDs M md ++ H.flatMap (opDs M))

/-- **The bytes the records are written as** (the page writer's output, in order). The file then
holds the preallocated zeros (`streamOf … ++ List.replicate z 0`). -/
def streamOf (C : WalCodec) (M : WalMarshal) (md : List w8) (H : WalHist) : List w8 :=
  recFrames C (recsOf C M md H)

/-- **The whole operations a record count keeps of `H`** (§2.2): the operations whose records all
fit in `n` op records, in order, up to the first that does not. -/
def histCut (M : WalMarshal) : WalHist → Nat → WalHist
  | [], _ => []
  | o :: H, n =>
    if (opDs M o).length ≤ n then o :: histCut M H (n - (opDs M o).length) else []

/-- **The records a record count keeps past `histCut`**: the first records of the first operation
that does not fit (entry records only, `histCutRest_entry`: a `Save` with entries ends with its state
record, the torn-`Save` fix; the fold of `ReadAll` drops them). -/
def histCutRest (M : WalMarshal) : WalHist → Nat → List (w64 × List w8)
  | [], _ => []
  | o :: H, n =>
    if (opDs M o).length ≤ n then histCutRest M H (n - (opDs M o).length) else (opDs M o).take n

/-! ## The lemmas -/

/-- The encoder's records are a chain the reader accepts. -/
theorem chainOk_chainRecs {C : WalCodec} (hC : C.Ok) (c : w32) (ds : List (w64 × List w8))
    (hds : ∀ p ∈ ds, p.1 = crcType → p.2 = []) : ChainOk C c (chainRecs C c ds) := by
  induction ds generalizing c with
  | nil => trivial
  | cons p ds ih =>
    obtain ⟨t, d⟩ := p
    have hnext : crcNext C c ⟨t, C.crc32c c d, d⟩ = C.crc32c c d := by
      unfold crcNext; split <;> rfl
    simp only [chainRecs, ChainOk, hnext]
    refine ⟨?_, ih _ (fun q hq => hds q (List.mem_cons_of_mem _ hq))⟩
    unfold CrcOk
    split
    · rfl
    · rename_i ht
      have hd := hds (t, d) List.mem_cons_self (by simpa using ht)
      simp only at hd
      subst hd
      exact Or.inr (hC.crc_nil c)

theorem chainOk_recsOf {C : WalCodec} (hC : C.Ok) (M : WalMarshal) (md : List w8) (H : WalHist) :
    ChainOk C 0#32 (recsOf C M md H) := by
  apply chainOk_chainRecs hC
  intro p hp ht
  simp only [hdrDs, List.mem_append, List.mem_cons, List.mem_flatMap, List.not_mem_nil,
    or_false] at hp
  rcases hp with (rfl | rfl | rfl) | ⟨o, -, ho⟩
  · rfl
  · exact absurd ht (by simp only; decide)
  · exact absurd ht (by simp only; decide)
  · exfalso
    cases o with
    | save h es =>
      simp only [opDs, List.mem_append, List.mem_map] at ho
      rcases ho with ⟨e, -, rfl⟩ | ho
      · exact absurd ht (by simp only; decide)
      · split at ho
        · simp at ho
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
          subst ho; exact absurd ht (by simp only; decide)
    | snap m al =>
      simp only [opDs, List.mem_cons, List.not_mem_nil, or_false] at ho
      subst ho; exact absurd ht (by simp only; decide)

theorem length_chainRecs (C : WalCodec) (c : w32) (ds : List (w64 × List w8)) :
    (chainRecs C c ds).length = ds.length := by
  induction ds generalizing c with
  | nil => rfl
  | cons p ds ih => obtain ⟨t, d⟩ := p; simp [chainRecs, ih]

theorem chainRecs_take (C : WalCodec) (c : w32) (ds : List (w64 × List w8)) (n : Nat) :
    chainRecs C c (ds.take n) = (chainRecs C c ds).take n := by
  induction ds generalizing c n with
  | nil => simp [chainRecs]
  | cons p ds ih =>
    obtain ⟨t, d⟩ := p
    cases n with
    | zero => simp [chainRecs]
    | succ n => simp [chainRecs, ih]

theorem chainRecs_prefix (C : WalCodec) (c : w32) {ds ds' : List (w64 × List w8)}
    (h : ds' <+: ds) : chainRecs C c ds' <+: chainRecs C c ds := by
  rw [List.prefix_iff_eq_take] at h ⊢
  rw [length_chainRecs, ← chainRecs_take, ← h]

/-- **(a) What the encoder wrote decodes to its records**, then the preallocated zeros read as the
end (`io.EOF`). -/
theorem walDecode_streamOf {C : WalCodec} (hC : C.Ok) (M : WalMarshal) (md : List w8) (H : WalHist)
    (hfit : RecsFit C (recsOf C M md H)) {z : Nat} (hz : z = 0 ∨ 8 ≤ z) :
    (walDecode C (streamOf C M md H ++ List.replicate z (0#8))).recs = recsOf C M md H ∧
    (walDecode C (streamOf C M md H ++ List.replicate z (0#8))).stop = .eof := by
  have h := walDecodeFrom_frames hC (last := true) (bs := streamOf C M md H ++ List.replicate z (0#8))
    (recsOf C M md H) (off := 0) (c := 0#32) (rest := List.replicate z (0#8)) hfit
    (chainOk_recsOf hC M md H) (by rw [List.drop_zero]; rfl)
  have hz' := walDecodeFrom_zeros C (last := true) (bs := streamOf C M md H ++ List.replicate z (0#8))
    (off := (recFrames C (recsOf C M md H)).length) (c := chainEnd C 0#32 (recsOf C M md H)) hz
    (by unfold streamOf; exact List.drop_left' rfl)
  unfold walDecode
  rw [h, Nat.zero_add, hz']
  simp

theorem hsEmptyP_zero : hsEmptyP (HardStateM.mk 0 0 0) := ⟨rfl, rfl, rfl⟩

/-- The op records of a cut history, then the records left, are the first `n` op records. -/
theorem flatMap_histCut (M : WalMarshal) (H : WalHist) (n : Nat) :
    (histCut M H n).flatMap (opDs M) ++ histCutRest M H n = (H.flatMap (opDs M)).take n := by
  induction H generalizing n with
  | nil => simp [histCut, histCutRest]
  | cons o H ih =>
    simp only [histCut, histCutRest, List.flatMap_cons]
    split
    · rename_i hk
      rw [List.flatMap_cons, List.append_assoc, ih, List.take_append, List.take_of_length_le hk]
    · rename_i hk
      rw [List.take_append_of_le_length (by omega)]
      simp

/-- **The records left past the whole operations are entry records.** -/
theorem histCutRest_entry (M : WalMarshal) (H : WalHist) (n : Nat) :
    ∀ p ∈ histCutRest M H n, p.1 = entryType := by
  induction H generalizing n with
  | nil => simp [histCutRest]
  | cons o H ih =>
    simp only [histCutRest]
    split
    · exact ih _
    · rename_i hk
      intro p hp
      cases o with
      | save h es =>
        simp only [opDs, List.length_append, List.length_map] at hk hp
        have hn : n ≤ es.length := by
          by_cases he : es = [] ∧ hsEmptyP h
          · rw [if_pos he] at hk; simp at hk; omega
          · rw [if_neg he] at hk; simp at hk; omega
        rw [List.take_append_of_le_length (by simpa using hn)] at hp
        obtain ⟨e, -, rfl⟩ := List.mem_map.1 (List.mem_of_mem_take hp)
        rfl
      | snap m al =>
        simp only [opDs, List.length_cons, List.length_nil] at hk
        have : n = 0 := by omega
        subst this; simp at hp

/-- **The entry records of `es`** (`(entryType, M.encEntry e)` each): a torn `Save`'s records before
its state record (P6). -/
def pendDs (M : WalMarshal) (es : List EntryM) : List (w64 × List w8) :=
  es.map (fun e => (entryType, M.encEntry e))

/-- **The records left past the whole operations are a torn `Save`'s entry records.** -/
theorem histCutRest_pend (M : WalMarshal) (H : WalHist) (n : Nat) :
    ∃ es, histCutRest M H n = pendDs M es := by
  induction H generalizing n with
  | nil => exact ⟨[], by simp [histCutRest, pendDs]⟩
  | cons o H ih =>
    simp only [histCutRest]
    split
    · exact ih _
    · rename_i hk
      cases o with
      | save h es =>
        simp only [opDs, List.length_append, List.length_map] at hk ⊢
        have hn : n ≤ es.length := by
          by_cases he : es = [] ∧ hsEmptyP h
          · rw [if_pos he] at hk; simp at hk; omega
          · rw [if_neg he] at hk; simp at hk; omega
        rw [List.take_append_of_le_length (by simpa using hn), ← List.map_take]
        exact ⟨es.take n, rfl⟩
      | snap m al =>
        simp only [opDs, List.length_cons, List.length_nil] at hk
        have : n = 0 := by omega
        subst this; exact ⟨[], by simp [pendDs]⟩

/-- A cut history is a prefix of the history. -/
theorem histCut_take (M : WalMarshal) (H : WalHist) (n : Nat) :
    histCut M H n = H.take (histCut M H n).length := by
  induction H generalizing n with
  | nil => simp [histCut]
  | cons o H ih =>
    simp only [histCut]
    split
    · simp only [List.length_cons, List.take_succ_cons]; rw [← ih]
    · simp

/-- **(c) A cut history is an image** (`walImgS`) when it keeps the first `m` operations' records. -/
theorem walImgS_histCut (M : WalMarshal) (H : WalHist) (m n : Nat) (hm : m ≤ H.length)
    (hn : ((H.take m).flatMap (opDs M)).length ≤ n) : walImgS H m (histCut M H n) := by
  induction H generalizing m n with
  | nil =>
    simp only [List.length_nil, Nat.le_zero] at hm; subst hm
    exact ⟨0, Nat.le_refl _, Nat.le_refl _, rfl⟩
  | cons o H ih =>
    unfold histCut
    split
    · rename_i hk
      have hcons : ∀ m', m' ≤ H.length →
          ((H.take m').flatMap (opDs M)).length ≤ n - (opDs M o).length →
          walImgS (o :: H) (m' + 1) (o :: histCut M H (n - (opDs M o).length)) := by
        intro m' hm' hn'
        obtain ⟨j, hj1, hj2, hI⟩ := ih m' (n - (opDs M o).length) hm' hn'
        exact ⟨j + 1, by omega, by simp; omega, by rw [hI]; rfl⟩
      cases m with
      | zero =>
        obtain ⟨j, -, hj2, hI⟩ := hcons 0 (Nat.zero_le _) (by simp)
        exact ⟨j, Nat.zero_le _, hj2, hI⟩
      | succ m' =>
        apply hcons m' (by simpa using hm)
        simp only [List.take_succ_cons, List.flatMap_cons, List.length_append] at hn
        omega
    · rename_i hk
      have hm0 : m = 0 := by
        cases m with
        | zero => rfl
        | succ m' =>
          simp only [List.take_succ_cons, List.flatMap_cons, List.length_append] at hn
          omega
      subst hm0
      exact ⟨0, Nat.le_refl _, Nat.zero_le _, rfl⟩

end recs

end WalEnc
end EtcdGrove
end Perennial
