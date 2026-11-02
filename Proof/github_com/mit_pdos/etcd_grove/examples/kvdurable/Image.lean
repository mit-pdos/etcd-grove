/-
Lean-first (no Rocq counterpart).

# The replica's image of its file (2026-11-01)

`Storage.img` (`examples/kvdurable/storage.go`, type `image`) is the replica's own record of what
its file should hold, changed under `dmu` with each of the replica's storage changes, and what
`Storage.encode` writes: the file is never written from the `MemoryStorage` (raft's storage
contract owns its log above the commit index between `Ready`s, and its `Snapshot` does not say which
snapshot it returns: `stageI-5-clients.md`, API gaps G2/G3). The image's contents are a `StorFile`
(`Codec.lean`), the file's own contents.

* **The changes, pure**: `imgApplySnapshot`, `imgSetHardState`, `imgAppend`, `imgCreateSnapshot`,
  `imgCompact` are `MemoryStorage`'s `ApplySnapshot`, `SetHardState`, `Append`, `CreateSnapshot`,
  `Compact` on the contents (the log's start `prev`/`prevTerm` is `MemoryStorage`'s dummy entry,
  `ents` its entries after it), with their refusals (`imgSnapStale`: `ErrSnapOutOfDate` of
  `ApplySnapshot`; `CreateSnapshot`'s is `i ≤` the snapshot's index, `Compact`'s `i ≤ prev`) and the
  conditions under which they do not panic, which the WP specs (`Spec/.../kvdurable/image__*.lean`)
  take as premises.
* **`ownImage p I`**: the image at `p` holds `I`, its fields owned, what they point to read-only
  (the hard state `hsOpt`, the snapshot `ownSnapM … discard`, the entries `entsRO`): nothing is
  written in place, so a change replaces a field.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.kvdurable.Base
public import Proof.github_com.mit_pdos.etcd_grove.examples.kvdurable.Codec
public import Proof.go_etcd_io.raft.v3.InvMemstorage

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvdurable

open Iris Iris.BI go_etcd_io.raft.v3

/-! ## The changes, pure -/

section pure
variable [GooseExts]

/-- The empty image (`newStorage`'s): the zero hard state, the empty snapshot, the log's start at
index and term `0`, no entries. -/
def imgEmpty : StorFile :=
  ⟨HardStateM.mk (W64 0) (W64 0) (W64 0), memSnapEmpty, W64 0, W64 0, []⟩

/-- `ApplySnapshot(sv)` is refused (`ErrSnapOutOfDate`): the image's snapshot is at a non-zero index
at least `sv`'s. -/
def imgSnapStale (I : StorFile) (sv : SnapshotM) : Prop :=
  I.snap.Metadata'.Index' ≠ W64 0 ∧ uint.Z sv.Metadata'.Index' ≤ uint.Z I.snap.Metadata'.Index'

instance (I : StorFile) (sv : SnapshotM) : Decidable (imgSnapStale I sv) := by
  unfold imgSnapStale; infer_instance

/-- `ApplySnapshot(sv)`, not refused: the snapshot `sv`, the log starting at it, empty. -/
def imgApplySnapshot (I : StorFile) (sv : SnapshotM) : StorFile :=
  ⟨I.hs, sv, sv.Metadata'.Index', sv.Metadata'.Term', []⟩

/-- `SetHardState(hs)`. -/
def imgSetHardState (I : StorFile) (hs : HardStateM) : StorFile :=
  ⟨hs, I.snap, I.prev, I.prevTerm, I.ents⟩

/-- `Append(es)` of entries consecutive from index `k`: no change if there are none, or if all are at
or below the log's start (`prev`); otherwise the entries above the start (the others dropped)
replace the log's from the first of them on. (Does not panic when `k ≤ prev + 1 + |ents|`.) -/
def imgAppend (I : StorFile) (k : Nat) (es : List EntryM) : StorFile :=
  if es = [] ∨ k + es.length ≤ uint.nat I.prev + 1 then I
  else ⟨I.hs, I.snap, I.prev, I.prevTerm,
    I.ents.take (k - (uint.nat I.prev + 1)) ++ es.drop (uint.nat I.prev + 1 - k)⟩

/-- The term of the log at index `i` (from `prev` to the last index): `prevTerm` at the start, the
entry's after it. -/
def imgTermAt (I : StorFile) (i : w64) : w64 :=
  if uint.nat i ≤ uint.nat I.prev then I.prevTerm
  else ((I.ents[uint.nat i - uint.nat I.prev - 1]?).map EntryM.Term').getD (W64 0)

/-- `CreateSnapshot(i, cs, data)` is refused (`ErrSnapOutOfDate`): `i` is at most the snapshot's
index. -/
def imgCreateStale (I : StorFile) (i : w64) : Prop :=
  uint.Z i ≤ uint.Z I.snap.Metadata'.Index'

instance (I : StorFile) (i : w64) : Decidable (imgCreateStale I i) := by
  unfold imgCreateStale; infer_instance

/-- `CreateSnapshot(i, cs, data)`, not refused: the snapshot at `i` and the log's term there, of the
configuration `co` (the old snapshot's if `cs` is `nil`, `co = none`) and the data `bs`. (Does not
panic when `prev ≤ i ≤ prev + |ents|`.) -/
def imgCreateSnapshot (I : StorFile) (i : w64) (co : Option ConfStateM) (bs : List w8) : StorFile :=
  ⟨I.hs, memSnapMade i (imgTermAt I i) (co.getD I.snap.Metadata'.ConfState') bs, I.prev,
    I.prevTerm, I.ents⟩

/-- `Compact(i)` is refused (`ErrCompacted`): `i` is at most the log's start. -/
def imgCompactStale (I : StorFile) (i : w64) : Prop :=
  uint.Z i ≤ uint.Z I.prev

instance (I : StorFile) (i : w64) : Decidable (imgCompactStale I i) := by
  unfold imgCompactStale; infer_instance

/-- `Compact(i)`, not refused: the log starts at `i` (at the log's term there), with the entries after
it. (Does not panic when `i ≤ prev + |ents|`.) -/
def imgCompact (I : StorFile) (i : w64) : StorFile :=
  ⟨I.hs, I.snap, i, imgTermAt I i, I.ents.drop (uint.nat i - uint.nat I.prev)⟩

end pure

/-! ## The image's points-to -/

/-- The image struct, and the storage's (whose `img` field points to its image). -/
abbrev KImage [GooseExts] := github_com.mit_pdos.etcd_grove.examples.kvdurable.image
abbrev KStorage [GooseExts] := github_com.mit_pdos.etcd_grove.examples.kvdurable.Storage

abbrev kImageTy [GooseExts] [GoGlobalContext] : go.GoType :=
  github_com.mit_pdos.etcd_grove.examples.kvdurable.image.ty
abbrev kStorageTy [GooseExts] [GoGlobalContext] : go.GoType :=
  github_com.mit_pdos.etcd_grove.examples.kvdurable.Storage.ty

section ghost
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvdurable.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions]

/-- **The image at `p` holds `I`** (exclusive): its fields owned; the hard state (`nil` before the
first: the zero one), the snapshot and the entries they point to read-only; the log's last index
within a `uint64` (every change keeps it, `append` by its premise). -/
def ownImage (p : Loc) (I : StorFile) : IProp GF :=
  iprop(∃ (hsp sp : Loc) (es : GoSlice),
    "Hhs" ∷ p.[KImage, go!"hs"] ↦ hsp ∗ "#HhsO" ∷ hsOpt hsp I.hs ∗
    "Hsnap" ∷ p.[KImage, go!"snap"] ↦ sp ∗ "#HsnapO" ∷ ownSnapM sp DFrac.discard I.snap ∗
    "Hprev" ∷ p.[KImage, go!"prev"] ↦ I.prev ∗
    "HprevTerm" ∷ p.[KImage, go!"prevTerm"] ↦ I.prevTerm ∗
    "Hents" ∷ p.[KImage, go!"ents"] ↦ es ∗ "#HentsO" ∷ entsRO es I.ents ∗
    "%Hwf" ∷ ⌜uint.nat I.prev + I.ents.length < 2 ^ 64⌝)

end ghost

end kvdurable
end EtcdGrove
end Perennial
