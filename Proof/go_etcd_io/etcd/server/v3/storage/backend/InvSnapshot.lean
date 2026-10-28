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
  and `Close` read it). (D22 S-h, 2026-10-20) Fractional: `snapOpenQ sp D γ q`, the persistent
  `snapRO sp D γ` (opaque: `sp` is the snapshot of `D` named `γ`, as `InvBbolt.lean`'s predicates
  are axioms, its meaning what the snapshot's axioms say of it) with a share `q` of the ghost
  token `γ`; `WriteTo` and `Size` read at any share (the sender's goroutine streams while the
  sender reads the size), `Close` takes the whole (no read after it: bbolt's closed transaction
  has a nil `meta`, which `Size` dereferences). `snapOpen sp D` is the whole for some `γ`.
* `boltImage bs D` (opaque `Prop`): the bytes `bs` are a bbolt database file whose data is `D`
  (what `Tx.WriteTo` writes: its two meta pages and its data pages; many byte strings encode one
  `D`, by their page layout and free list). A file holding such bytes holds `D` (`fileHolds`):
  that is the receiver's half of the round trip, the transport's (D22 S-i).
* `pathOwn p` (opaque, exclusive): the program's right to the directory entry `p`: no other part
  of the program, and no other process, creates, removes or renames a file at `p` (the
  closed-world assumption of the data directory, as `netAddrFree` is of the addresses).
  `os.Rename` onto `p` needs it (else a `fileHolds p` could go stale under its holder); opening a
  database (`bolt.Open`) does not, and keeps the file open whatever then happens to its entry.
  `fileHolds p D` (`InvBbolt.lean`) is read as: the file at `p` holds `D`, and its holder may
  open it or rename it (exclusively, as a points-to).
* `writerOk w Wr`: the `io.Writer` `w`'s contract, by its client's predicate `Wr c bs` of the bytes
  written so far, `c` whether a `Write` call has returned (D22 S-h, 2026-10-20: a pipe's writer
  learns at its first `Write`'s return that its reader has started, `Spec/io/Pipe.lean`):
  `Write(p)` appends some prefix of `p`'s bytes, returns their number, and all of them unless it
  returns an error (`io.Writer`'s documentation).
* `readerStreams r Φ` (D22 S-i): the right to read the `io.Reader` `r`, whose complete streams
  satisfy `Φ`: the reader's half of a byte stream, as `writerOk` is the writer's.
* `viewAt γ vd`: the batch lock's quarter of the readers' view (`batchGhostAt`'s), the witness the
  snapshot's axiom hands its caller's observation (`backend.Snapshot.spec`): it agrees with the
  clients' shares (`bView`, of which the server's batch-lock resource holds one).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.backend.InvBackend

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace backend

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.backend

/-- **The bytes `bs` are a bbolt database file holding `D`** (opaque; see the file header). -/
opaque boltImage (bs : List w8) (D : Data) : Prop

section preds
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **`sp` is the snapshot of bbolt's committed data `D` named `γ`** (opaque, persistent by
`snapOpenQ`'s `□`; see the file header). -/
opaque snapRO (sp : Loc) (D : Data) (γ : GName) : IProp GF

/-- **A share `q` of the snapshot `sp` open over `D`** (see the file header). -/
def snapOpenQ (sp : Loc) (D : Data) (γ : GName) (q : Qp) : IProp GF :=
  iprop(□ snapRO sp D γ ∗ ghostVar γ q ())

/-- **The snapshot `sp` is open over bbolt's committed data `D`** (exclusive; see the file
header): the whole of it. -/
def snapOpen (sp : Loc) (D : Data) : IProp GF := iprop(∃ γ : GName, snapOpenQ sp D γ 1)

/-- A share of an open snapshot as two halves, both ways. -/
theorem snapOpenQ_half (sp : Loc) (D : Data) (γ : GName) (q : Qp) :
    snapOpenQ (GF := GF) sp D γ q ⊣⊢ snapOpenQ sp D γ q.half ∗ snapOpenQ sp D γ q.half := by
  unfold snapOpenQ
  constructor
  · iintro ⟨#Hro, Hg⟩
    icases (ghostVar_split_half (GF := GF) γ q ()).1 $$ Hg with ⟨Hg1, Hg2⟩
    iframe Hro Hg1 Hg2
  · iintro ⟨⟨#Hro, Hg1⟩, ⟨-, Hg2⟩⟩
    iframe Hro
    iapply (ghostVar_split_half (GF := GF) γ q ()).2
    iframe Hg1 Hg2

/-- **The directory entry `p` is the program's** (opaque, exclusive; see the file header). -/
opaque pathOwn (p : GoString) : IProp GF

/-- **The file system lets `src` be renamed onto `dst`** (opaque, a named premise about the
program's environment, D19a's first kind; D22 receiver epochs, S8d, 2026-10-24): `os.Rename(src,
dst)` of a file the program holds onto an entry it owns fails for no reason of the environment
(I/O, permissions, a full disk). `os.Rename`'s axiom gives `¬ renameOk src dst` on an error; the
premise excluding it is `storage.snapOpensOk`. -/
opaque renameOk (src dst : GoString) : Prop

/-- **The `io.Writer` `w`'s contract** (persistent), by `Wr c bs`, the bytes `bs` written so far
(`c`: whether a `Write` has returned): `Write(p)` of a slice holding `chunk` (read at `dq`, given
back) appends the first `k` bytes of `chunk` and returns `k`, all of them unless the error is
non-nil. -/
def writerOk (w : GoInterfaceOk) (Wr : Bool → List w8 → IProp GF) : IProp GF :=
  iprop(□ ∀ (p : GoSlice) (dq : DFrac) (chunk bs : List w8) (c : Bool),
    {{ p ↦*{dq} chunk ∗ Wr c bs }}
      (App (Val #(methods w.ty go!"Write" w.v)) (Val #p))
    {{ (n : w64) (err : GoInterface), RET (PairV #n #err);
        ∃ k : Nat, p ↦*{dq} chunk ∗ Wr true (bs ++ chunk.take k) ∗
          ⌜sint.Z n = k ∧ k ≤ chunk.length ∧ (err = GoInterface.nil → k = chunk.length)⌝ }})

instance writerOk_persistent (w : GoInterfaceOk) (Wr : Bool → List w8 → IProp GF) :
    Persistent (writerOk w Wr) := by
  unfold writerOk; infer_instance

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

/-- **The batch lock's quarter of the readers' view** at `vd` (see the file header). -/
def viewAt (γ : BNames) (vd : VData) : IProp GF := ghostVar γ.view (1 : Qp).half.half vd

end preds

end backend
end EtcdGrove
end Perennial
