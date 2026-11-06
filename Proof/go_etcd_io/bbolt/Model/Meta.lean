/-
bbolt's meta pages and the committed state (U0a of `notes/bbolt-proof-plan.md`).

A meta page is a page header and, after it, a `common.Meta` (64 bytes: `magic`, `version`,
`pageSize`, `flags`, the root bucket's `InBucket`, `freelist`, `pgid`, `txid`, `checksum`).
`Validate` checks the magic, the version and the checksum, an FNV-64a over the first 56 bytes;
`db.meta()` picks the valid meta with the higher txid (`metaPick`).

`CommitSt` is the committed state (design §3.2): the two meta slots' bytes, the current tree's
pages, its root, high-water mark, txid and synced freelist page. `CommitSt.metaOk` is
`fileHolds`' meta clauses, which also tie the record's fields to the current meta.

(U0a deviation, `notes/bbolt-proof-plan.md`: `Pages` and `CommitSt` are here, not in
`Model/Tree.lean`, since `CommitSt.metaOk` is; and the checksum is `fnv64a`, not a parameter of
`metaValid`. It was uninterpreted until 2026-11-04; it is now FNV-1a 64, `hash/fnv`'s model.)
-/
module

public import Proof.go_etcd_io.bbolt.Model.Page
public import Spec.hash.fnv.Model

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open go_etcd_io.bbolt.internal.common

/-- **FNV-64a** (`hash/fnv`'s `New64a`, `Write`, `Sum64`): `hash/fnv`'s model
(`Spec/hash/fnv/Model.lean`), which its specs (`Spec/hash/fnv/`, proved from its translated
bodies) are stated over; `Meta.Sum64`'s proof computes it through them. -/
def fnv64a : List w8 → w64 := hash.fnv.fnv64a

section metas
variable [GooseExts]

instance Meta.byteEncoding : ByteEncoding Meta 64 :=
  ByteEncoding.ofEquiv (W := w32 × w32 × w32 × w32 × InBucket × Pgid × Pgid × w64 × w64)
    (fun v => (v.magic', v.version', v.pageSize', v.flags', v.root', v.freelist', v.pgid',
      v.txid', v.checksum'))
    (fun p => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2.1, p.2.2.2.2.2.1, p.2.2.2.2.2.2.1,
      p.2.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2.2⟩) (fun _ => rfl) (fun _ => rfl)

/-- The meta of a meta page's bytes (after the page header, `Page.Meta()`). -/
def metaOf (pg : List w8) : Meta := decode (bytesAt pg 16 64)

/-- `Meta.Sum64`'s result: FNV-64a over the meta's bytes before `checksum`. -/
def metaSum (m : Meta) : w64 := fnv64a ((encode m).take 56)

/-- What `Meta.Validate` checks: the magic, the version and the checksum. -/
def metaValid (m : Meta) : Prop :=
  m.magic'.toNat = boltMagic ∧ m.version'.toNat = boltVersion ∧ m.checksum' = metaSum m

instance (m : Meta) : Decidable (metaValid m) := by unfold metaValid; infer_instance

/-- The meta with its checksum (`Meta.Write`'s `m.checksum = m.Sum64()`; moved from U10's
`Commit/MetaBuf` by batch 37). -/
def metaSummed (mv : Meta) : Meta := { mv with checksum' := metaSum mv }

/-- The checksum covers the bytes before the checksum field only (batch 37, U10). -/
theorem metaSum_checksum (m : Meta) (c : w64) : metaSum { m with checksum' := c } = metaSum m := by
  unfold metaSum
  have h : (encode { m with checksum' := c }).take 56 = (encode m).take 56 := by
    show List.take 56 (encode (m.magic', m.version', m.pageSize', m.flags', m.root', m.freelist',
        m.pgid', m.txid', c)) = List.take 56 (encode (m.magic', m.version', m.pageSize', m.flags',
        m.root', m.freelist', m.pgid', m.txid', m.checksum'))
    simp only [ByteEncoding.prod_encode, ← List.append_assoc]
    rw [List.take_left' (by simp), List.take_left' (by simp)]
  rw [h]

/-- A meta with its checksum field set to the sum of its other fields is valid when its magic and
version are (stated over the field's value `c`: the kernel must not unfold `metaSum`). -/
theorem metaValid_with (m : Meta) (c : w64) (hc : c = metaSum m) (h1 : m.magic'.toNat = boltMagic)
    (h2 : m.version'.toNat = boltVersion) : metaValid { m with checksum' := c } :=
  ⟨h1, h2, hc.trans (metaSum_checksum m c).symm⟩

/-- **A summed meta is valid** when its magic and version are (batch 37, U10: `writeMeta`'s meta). -/
theorem metaValid_metaSummed (mv : Meta) (h1 : mv.magic'.toNat = boltMagic)
    (h2 : mv.version'.toNat = boltVersion) : metaValid (metaSummed mv) :=
  metaValid_with mv _ rfl h1 h2

/-- `db.meta()`'s choice between `meta0` and `meta1`: the one with the higher txid if valid,
else the other if valid (`none`: `db.meta()` panics). -/
def metaPick (m0 m1 : Meta) : Option Meta :=
  let (a, b) := if m0.txid'.toNat < m1.txid'.toNat then (m1, m0) else (m0, m1)
  if metaValid a then some a else if metaValid b then some b else none

/-! ## The committed state -/

/-- A file's pages: page id ↦ its extent's bytes (`1 + overflow` slots of 4096 bytes). -/
abbrev Pages := GMap Nat (List w8)

/-- **The committed state** (design §3.2): what `metaR` publishes and every view is taken
from. -/
structure CommitSt where
  /-- The two meta slots' bytes (4096 each). -/
  m0 : List w8
  m1 : List w8
  /-- The current tree's pages (the root bucket's tree and its nested buckets' trees). -/
  pages : Pages
  /-- The root bucket's root page. -/
  root : Nat
  /-- The high-water mark (`meta.pgid`). -/
  hwm : Nat
  txid : Nat
  /-- The synced freelist page (`none`: `PgidNoFreelist`). -/
  flpg : Option Nat
  deriving Inhabited

instance CommitSt.countable : Pos.Countable CommitSt :=
  countableOfLeftInverse (fun C => (C.m0, C.m1, C.pages, C.root, C.hwm, C.txid, C.flpg))
    (fun p => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2.1, p.2.2.2.2.2.1, p.2.2.2.2.2.2⟩)
    (fun _ => rfl)

/-- Meta slot `i` (0 or 1). -/
def CommitSt.slot (C : CommitSt) (i : Nat) : List w8 := if i % 2 = 0 then C.m0 else C.m1

/-- The meta `db.meta()` picks. -/
def CommitSt.cur (C : CommitSt) : Option Meta := metaPick (metaOf C.m0) (metaOf C.m1)

/-- The synced freelist page a meta names. -/
def metaFlpg (m : Meta) : Option Nat :=
  if m.freelist'.toNat = pgidNoFreelist then none else some m.freelist'.toNat

/-- The record's fields are the meta `m`'s. -/
def CommitSt.isMeta (C : CommitSt) (m : Meta) : Prop :=
  m.txid'.toNat = C.txid ∧ m.root'.root'.toNat = C.root ∧ m.pgid'.toNat = C.hwm ∧
    metaFlpg m = C.flpg

/-- **`fileHolds`' meta clauses** (and the fields of the record are the current meta's):
- both slots 4096 bytes;
- every valid meta records page size 4096;
- no valid meta at offsets 1024 and 2048 of slot 0 (`getPageSize`'s probes, D18);
- the current meta is valid, lies at slot `txid % 2`, and its txid is strictly higher than any
  other valid meta's (so that a torn write of the other slot leaves it current). -/
def CommitSt.metaOk (C : CommitSt) : Prop :=
  C.m0.length = 4096 ∧ C.m1.length = 4096 ∧
  (∀ i, metaValid (metaOf (C.slot i)) → (metaOf (C.slot i)).pageSize'.toNat = 4096) ∧
  ¬ metaValid (metaOf (C.m0.drop 1024)) ∧ ¬ metaValid (metaOf (C.m0.drop 2048)) ∧
  metaValid (metaOf (C.slot C.txid)) ∧ C.isMeta (metaOf (C.slot C.txid)) ∧
  (metaValid (metaOf (C.slot (C.txid + 1))) →
    (metaOf (C.slot (C.txid + 1))).txid'.toNat < C.txid)

/-- The committed state after a commit (design §3.11, `writeMeta`): the meta page `buf`, whose
meta is `m`, written at slot `m.txid % 2`, with the new tree's pages. -/
def CommitSt.publish (C : CommitSt) (buf : List w8) (m : Meta) (pages : Pages) : CommitSt :=
  { m0 := if m.txid'.toNat % 2 = 0 then buf else C.m0
    m1 := if m.txid'.toNat % 2 = 0 then C.m1 else buf
    pages := pages
    root := m.root'.root'.toNat
    hwm := m.pgid'.toNat
    txid := m.txid'.toNat
    flpg := metaFlpg m }
proj_simps CommitSt.publish

/-! ## Lemma statements (U1, U10) -/

/-- The current meta is the one at slot `txid % 2`. Used by U4 (`DB.meta`) and U5 (`Tx.init`). -/
theorem metaPick_current (C : CommitSt) (h : C.metaOk) :
    C.cur = some (metaOf (C.slot C.txid)) := by
  obtain ⟨-, -, -, -, -, hv, ⟨ht, -⟩, hother⟩ := h
  unfold CommitSt.cur metaPick
  unfold CommitSt.slot at hv ht hother ⊢
  rcases Nat.mod_two_eq_zero_or_one C.txid with he | ho
  · have h1 : (C.txid + 1) % 2 ≠ 0 := by omega
    simp only [he, ↓reduceIte, h1] at hv ht hother ⊢
    by_cases hlt : (metaOf C.m0).txid'.toNat < (metaOf C.m1).txid'.toNat
    · have hn : ¬ metaValid (metaOf C.m1) := fun hv1 => by have := hother hv1; omega
      simp only [hlt, ↓reduceIte, hn, hv]
    · simp only [hlt, ↓reduceIte, hv]
  · have h0 : C.txid % 2 ≠ 0 := by omega
    have h1 : (C.txid + 1) % 2 = 0 := by omega
    simp only [h0, ↓reduceIte, h1] at hv ht hother ⊢
    by_cases hlt : (metaOf C.m0).txid'.toNat < (metaOf C.m1).txid'.toNat
    · simp only [hlt, ↓reduceIte, hv]
    · have hn : ¬ metaValid (metaOf C.m0) := fun hv0 => by have := hother hv0; omega
      simp only [hlt, ↓reduceIte, hn, hv]

/-- **A commit's meta write keeps `metaOk`** (design §3.12, "meta parity"): the meta of txid
`C.txid + 1`, valid, of page size 4096, written into a page whose probed offsets hold no valid
meta, at the slot the current meta is not on. Used by U10 (`writeMeta`'s commit point). -/
theorem metaOk_parity_write (C : CommitSt) (buf : List w8) (m : Meta) (pages : Pages)
    (hC : C.metaOk) (hlen : buf.length = 4096) (hm : metaOf buf = m) (hv : metaValid m)
    (ht : m.txid'.toNat = C.txid + 1) (hps : m.pageSize'.toNat = 4096)
    (hz : ¬ metaValid (metaOf (buf.drop 1024)) ∧ ¬ metaValid (metaOf (buf.drop 2048))) :
    (C.publish buf m pages).metaOk := by
  have hslot : ∀ i, (C.publish buf m pages).slot i =
      if i % 2 = m.txid'.toNat % 2 then buf else C.slot i := by
    intro i
    unfold CommitSt.slot CommitSt.publish
    rcases Nat.mod_two_eq_zero_or_one i with hi | hi <;>
    rcases Nat.mod_two_eq_zero_or_one m.txid'.toNat with ht | ht <;> simp [hi, ht]
  obtain ⟨h0, h1, hpsz, hz1, hz2, hcv, hcm, hoth⟩ := hC
  have htx : (C.publish buf m pages).txid = C.txid + 1 := by simp [CommitSt.publish, ht]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [CommitSt.publish]; split <;> simp [hlen, h0]
  · simp only [CommitSt.publish]; split <;> simp [hlen, h1]
  · intro i hi
    rw [hslot] at hi ⊢
    split
    · simp_all
    · rename_i hne; rw [ite_eq_right hne] at hi; exact hpsz i hi
  · simp only [CommitSt.publish]; split
    · exact hz.1
    · exact hz1
  · simp only [CommitSt.publish]; split
    · exact hz.2
    · exact hz2
  · rw [htx, hslot, ite_eq_left (by rw [ht])]; rw [hm]; exact hv
  · rw [htx, hslot, ite_eq_left (by rw [ht]), hm]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [CommitSt.publish, ht]
  · rw [htx, hslot, ite_eq_right (by rw [ht]; omega)]
    have e : C.slot (C.txid + 1 + 1) = C.slot C.txid := by
      unfold CommitSt.slot
      have : (C.txid + 1 + 1) % 2 = C.txid % 2 := by omega
      rw [this]
    rw [e, hcm.1]; intro _; omega

end metas

end bbolt
end EtcdGrove
end Perennial
