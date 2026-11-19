/-
**The backend's snapshot and the database files** (D22 S-f, 2026-10-19; `notes/decisions.md`,
"D22 S-f carried out"): the vocabulary of the snapshot path's trust boundary at etcd's backend,
beside bbolt's (`InvBbolt.lean`). Lean-first (no Rocq counterpart). Nothing here touches the
bbolt proofs (`Proof`/`Spec` under `go_etcd_io/bbolt`): bbolt-level facts are stated as specs or
axioms of etcd's backend (`backend.Snapshot`, `snapshot.WriteTo`) and of the file system
(`os.Rename`).

* `snapOpen sp D` (exclusive): the `*snapshot` `sp` (`backend.go`'s `snapshot`: bbolt's
  read transaction, with the goroutine that warns while it is open) that `backend.Snapshot()`
  returned is open, and its read transaction reads bbolt's committed data `D` (`WriteTo`, `Size`
  and `Close` read it). (D22 S-h, 2026-10-20) Fractional: `snapOpenQ sp D γ q`, a share `q` of the
  snapshot named `γ`; `WriteTo` and `Size` read at any share (the sender's goroutine streams while
  the sender reads the size), `Close` takes the whole (no read after it: bbolt's closed transaction
  has a nil `meta`, which `Size` dereferences). `snapOpen sp D` is the whole for some `γ`.
  (S4b, 2026-11-18: until then over an opaque persistent `snapRO`) A definition: the snapshot's
  fields (`snapAt`: its transaction `tx` of the database `γd`, its channels `stopc` and `donec` as
  broadcast channels, and the invariant `snapN` holding `stopc`'s close right until `Close`, which
  swaps it for the whole of `γ`), the share `q` of the ghost variable `γ` at `(tx, γd)` and the
  share `q` of bbolt's read transaction (`txLive tx γd q (TxView.ro D)`). At `HasLC.hasLC` (the
  broadcast channels'), as its clients are.
* `boltImage bs D` (bbolt's `boltImage`, session S4; until then an opaque `Prop`): the bytes `bs` are a bbolt database file whose data is `D`
  (what `Tx.WriteTo` writes: its two meta pages and its data pages; many byte strings encode one
  `D`, by their page layout and free list). A file holding such bytes holds `D` (`fileHolds`):
  that is the receiver's half of the round trip, the transport's (D22 S-i).
* (S5, 2026-11-18) The program's right to the backend file's directory entry, until then the opaque
  exclusive `pathOwn p`, is the claim on the name in the tree's shared mode, `bPath γ p`
  (`InvBbolt.lean`): `backend.New` gives it, naming the opened file; `os.Rename` onto `p` takes it.
  `fileHolds p D` (`InvBbolt.lean`) is the claim with the file holding `D`, `fileAt p D` the same
  with a file there (the server's received snapshots), `fileFree p` the claim with nothing there.
  Until S5 the server's snapshot path had its own abstract `srvFileHolds`, backed by no
  file-extension resource.
* `writerOk w Wr`: the `io.Writer` `w`'s contract, by its client's predicate `Wr c bs` of the bytes
  written so far, `c` whether a `Write` call has returned (D22 S-h, 2026-10-20: a pipe's writer
  learns at its first `Write`'s return that its reader has started, `Spec/io/Pipe.lean`):
  `Write(p)` appends some prefix of `p`'s bytes, returns their number, and all of them unless it
  returns an error (`io.Writer`'s documentation).
* `readerStreams r Φ` (D22 S-i): the right to read the `io.Reader` `r`, whose complete streams
  satisfy `Φ`: the reader's half of a byte stream, as `writerOk` is the writer's.
* `viewAt γ vd`: the batch lock's quarter of the readers' view (`batchGhostAt`'s), at a logical view
  the physical view `vd` is thin of (question 2, option (a), 2026-10-29), the witness the snapshot's
  axiom hands its caller's observation (`backend.Snapshot.spec`): it agrees with the clients' shares
  (`bView`, of which the server's batch-lock resource holds one), the physical view thin of theirs.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.backend.InvBackend
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.DelKeys
public import Proof.io.SectionReader
public import Perennial.Golang.Theory.Chan.Idioms.Broadcast

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace backend

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.backend

/-- **The bytes `bs` are a bbolt database file holding `D`** (see the file header; session S4: bbolt's
`boltImage`, what bbolt's proved `Tx.WriteTo` writes, until then opaque). -/
def boltImage [GooseExts] (bs : List w8) (D : Data) : Prop := bbolt.boltImage bs D

section preds
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **The file system lets `src` be renamed onto `dst`** (opaque, a named premise about the
program's environment, D19a's first kind; D22 receiver epochs, S8d, 2026-10-24): `os.Rename(src,
dst)` of a file the program holds onto an entry it owns fails for no reason of the environment
(I/O, permissions, a full disk). (S5, 2026-11-18) No spec gives its negation since `os.Rename` is
proved from the file model, which has no such error under `theFs`'s `FsNoErrAll`: the premise
`storage.snapOpensOk`'s conjunct is unused (until then `os.Rename`'s axiom gave `¬ renameOk src dst`
on an error). -/
opaque renameOk (src dst : GoString) : Prop

/-- **The `io.Writer` `w`'s contract** (persistent): `io.writerOk` (`Proof/io/SectionReader.lean`;
session S4 moved its body there, for bbolt's `Tx.WriteTo` and `io.CopyN`). -/
abbrev writerOk (w : GoInterfaceOk) (Wr : Bool → List w8 → IProp GF) : IProp GF :=
  io.writerOk w Wr

/-- **The right to read the stream of the `io.ReadCloser` `r`, whose complete streams satisfy
`Φ`** (opaque, exclusive; D22 S-i, 2026-10-19): `r` is read by one reader, and any byte string it
yields in full -- every byte its `Read`s return until one returns `io.EOF`, with no other error
before -- satisfies `Φ`; a reader may also stop early or see an error (then nothing is
promised). Its meaning is what the axioms that make and take it say: the merged snapshot's pipe
(`io.Pipe`, whose reader returns `io.EOF` only after its writer's `Close`, i.e. `CloseWithError(nil)`,
which `newSnapshotReaderCloser` calls only when `WriteTo` succeeded: S-h) makes it, with
`Φ bs := boltImage bs D`; the transport's `SendSnapshot` takes it (`netSnapBundle`). -/
opaque readerStreams (r : GoInterface) (Φ : List w8 → Prop) : IProp GF

variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]

/-- **The batch lock's quarter of the readers' view, its physical view at `vd`** (see the file
header): the quarter at some logical view `L` that `vd` is thin of (question 2, option (a), the
user's, 2026-10-29: the batch lock's quarter is over the logical view, `batchViewQ`; until then the
quarter at `vd` itself, an instance: `viewQ_exact`). -/
def viewAt (γ : BNames) (vd : VData) : IProp GF :=
  iprop(∃ L : VData, viewQ γ (1 : Qp).half.half vd L)

/-- **The batch lock's quarter of the readers' view at a commit, with the safe-range buckets'
deleted entries** (the user's decision, 2026-11-04, probe M2: a snapshot's observation knows the
safe-range bucket exactly): the quarter at a logical view `L`, the physical view `vd` thin of it,
and `vd` exactly `L` but the deleted entries `X` on the safe-range buckets (`dlVd`). -/
def viewAtD (γ : BNames) (P : BParams) (vd X : VData) : IProp GF :=
  iprop(∃ L : VData, viewQ γ (1 : Qp).half.half vd L ∗ ⌜dlVd P vd L X⌝)

/-- The quarter with the deleted entries is the quarter. -/
theorem viewAtD_viewAt (γ : BNames) (P : BParams) (vd X : VData) :
    viewAtD (GF := GF) γ P vd X ⊢ viewAt γ vd := by
  unfold viewAtD viewAt
  iintro ⟨%L, Hq, -⟩
  iexists L; iexact Hq

/-- **`viewAt` agrees with the clients' shares** (review round 12, R12-3): the snapshot's physical
view is thin of the clients' view. -/
theorem viewAt_bView (γ : BNames) (vd vd' : VData) (q : Qp) :
    viewAt (GF := GF) γ vd ∗ bView γ q vd' ⊢ viewAt γ vd ∗ bView γ q vd' ∗ thinV γ vd vd' := by
  unfold viewAt bView bViewC viewQ
  iintro ⟨⟨%L, Hq, #Ht⟩, ⟨%c, Hv, Hc, Hl⟩⟩
  icombine Hq Hv gives %Heq
  obtain ⟨-, rfl⟩ := Heq
  iframe Hc Hl Hv
  isplitl [Hq]
  · iexists _; iframe Hq; iframe #
  iframe #

/-- **With nothing deletable, `viewAt` is the quarter at `vd` itself** (R12-3; D22's users never
compact). -/
theorem viewAt_noDel (γ : BNames) (vd : VData) :
    dlNoDel (GF := GF) γ ∗ viewAt γ vd ⊢ ghostVar γ.view (1 : Qp).half.half vd := by
  unfold viewAt viewQ
  iintro ⟨#Hf, %L, Hv, #Ht⟩
  ihave %Heq := thinV_exact γ vd L $$ [$Hf $Ht]
  subst Heq
  iexact Hv

end preds

/-! ## The snapshot (S4b, 2026-11-18) -/

section snap
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]

/-- The snapshot's invariant's namespace. -/
abbrev snapN : Namespace := bN.@"snap"

/-- **The snapshot `sp` named `γ`, of the read transaction `tx` of the database `γd`** (persistent;
see the file header): its fields, its channels `stopc` (`Close` closes it, the goroutine waits for
it) and `donec` (the goroutine closes it, `Close` waits for it), broadcasting nothing, and the
invariant keeping `stopc`'s close right until `Close`, which leaves the whole of `γ` in its place
(so a second `Close` would find none: it has no whole of `γ`). -/
def snapAt (sp : Loc) (γ : GName) (tx : Loc) (γd : DBNames) : IProp GF :=
  iprop(∃ (sc dc : GoChan) (γsc γdc : ChanNames),
    structFieldRef snapshot go!"Tx" sp ↦□ tx ∗ structFieldRef snapshot go!"stopc" sp ↦□ sc ∗
    structFieldRef snapshot go!"donec" sp ↦□ dc ∗
    ownBroadcastChan sc γsc iprop(True) .Unknown ∗ ownBroadcastChan dc γdc iprop(True) .Unknown ∗
    inv snapN iprop(ownBroadcastChan sc γsc iprop(True) .Pending ∨ ghostVar γ 1 (tx, γd)))

instance snapAt_persistent (sp : Loc) (γ : GName) (tx : Loc) (γd : DBNames) :
    Persistent (snapAt (GF := GF) sp γ tx γd) := by
  unfold snapAt; infer_instance

/-- **A share `q` of the snapshot `sp` open over `D`** (see the file header). -/
def snapOpenQ (sp : Loc) (D : Data) (γ : GName) (q : Qp) : IProp GF :=
  iprop(∃ (tx : Loc) (γd : DBNames), snapAt sp γ tx γd ∗ ghostVar γ q (tx, γd) ∗
    txLive tx γd q (bbolt.TxView.ro D))

/-- **The snapshot `sp` is open over bbolt's committed data `D`** (exclusive; see the file
header): the whole of it. -/
def snapOpen (sp : Loc) (D : Data) : IProp GF := iprop(∃ γ : GName, snapOpenQ sp D γ 1)

/-- A share of a read transaction as two halves, both ways. -/
theorem txLive_split_half (tx : Loc) (γd : DBNames) (q : Qp) (T : bbolt.TxView) :
    txLive (GF := GF) tx γd q T ⊣⊢ txLive tx γd q.half T ∗ txLive tx γd q.half T := by
  conv => lhs; rw [← Qp.half_add_half q]
  exact (txLive_fractional tx γd T).fractional _ _

/-- A share of an open snapshot as two halves, both ways. -/
theorem snapOpenQ_half (sp : Loc) (D : Data) (γ : GName) (q : Qp) :
    snapOpenQ (GF := GF) sp D γ q ⊣⊢ snapOpenQ sp D γ q.half ∗ snapOpenQ sp D γ q.half := by
  unfold snapOpenQ
  constructor
  · iintro ⟨%tx, %γd, #Ha, Hg, Hl⟩
    icases (ghostVar_split_half (GF := GF) γ q (tx, γd)).1 $$ Hg with ⟨Hg1, Hg2⟩
    icases (txLive_split_half tx γd q _).1 $$ Hl with ⟨Hl1, Hl2⟩
    isplitl [Hg1 Hl1]
    · iexists tx, γd; iframe Ha Hg1 Hl1
    · iexists tx, γd; iframe Ha Hg2 Hl2
  · iintro ⟨⟨%tx, %γd, #Ha, Hg1, Hl1⟩, ⟨%tx', %γd', -, Hg2, Hl2⟩⟩
    ihave %Heq := ghostVar_agree γ (tx, γd) q.half (tx', γd') q.half $$ Hg1 Hg2
    cases Heq
    iexists tx, γd
    iframe Ha
    isplitl [Hg1 Hg2]
    · iapply (ghostVar_split_half (GF := GF) γ q (tx, γd)).2
      iframe Hg1 Hg2
    · iapply (txLive_split_half tx γd q _).2
      iframe Hl1 Hl2

end snap

end backend
end EtcdGrove
end Perennial
