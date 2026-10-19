/-
**The backend's snapshot and the database files** (D22 S-f, 2026-10-19; `notes/decisions.md`,
"D22 S-f carried out"): the vocabulary of the snapshot path's trust boundary at etcd's backend,
beside bbolt's (`InvBbolt.lean`). Lean-first (no Rocq counterpart). Nothing here touches the
bbolt proofs (`Proof`/`Spec` under `go_etcd_io/bbolt`): bbolt-level facts are stated as specs or
axioms of etcd's backend (`backend.Snapshot`, `snapshot.WriteTo`) and of the file system
(`os.Rename`).

* `snapOpen sp D` (opaque, exclusive): the `*snapshot` `sp` (`backend.go`'s `snapshot`: bbolt's
  read transaction, with the goroutine that warns while it is open) that `backend.Snapshot()`
  returned is open, and its read transaction reads bbolt's committed data `D` (`WriteTo`, `Size`
  and `Close` read it). An opaque predicate, as `InvBbolt.lean`'s are axioms: its meaning is
  what the snapshot's axioms say of it.
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
* `writerOk w Wr`: the `io.Writer` `w`'s contract, by its client's predicate `Wr bs` of the bytes
  written so far: `Write(p)` appends some prefix of `p`'s bytes, returns their number, and all of
  them unless it returns an error (`io.Writer`'s documentation).
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
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **The snapshot `sp` is open over bbolt's committed data `D`** (opaque, exclusive; see the file
header). -/
opaque snapOpen (sp : Loc) (D : Data) : IProp GF

/-- **The directory entry `p` is the program's** (opaque, exclusive; see the file header). -/
opaque pathOwn (p : GoString) : IProp GF

/-- **The `io.Writer` `w`'s contract** (persistent), by `Wr bs`, the bytes `bs` written so far:
`Write(p)` of a slice holding `chunk` (read at `dq`, given back) appends the first `k` bytes of
`chunk` and returns `k`, all of them unless the error is non-nil. -/
def writerOk (w : GoInterfaceOk) (Wr : List w8 → IProp GF) : IProp GF :=
  iprop(□ ∀ (p : GoSlice) (dq : DFrac) (chunk bs : List w8),
    {{ p ↦*{dq} chunk ∗ Wr bs }}
      (App (Val #(methods w.ty go!"Write" w.v)) (Val #p))
    {{ (n : w64) (err : GoInterface), RET (PairV #n #err);
        ∃ k : Nat, p ↦*{dq} chunk ∗ Wr (bs ++ chunk.take k) ∗
          ⌜sint.Z n = k ∧ k ≤ chunk.length ∧ (err = GoInterface.nil → k = chunk.length)⌝ }})

instance writerOk_persistent (w : GoInterfaceOk) (Wr : List w8 → IProp GF) :
    Persistent (writerOk w Wr) := by
  unfold writerOk; infer_instance

variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]

/-- **The batch lock's quarter of the readers' view** at `vd` (see the file header). -/
def viewAt (γ : BNames) (vd : VData) : IProp GF := ghostVar γ.view (1 : Qp).half.half vd

/-- The witness agrees with a client's share of the view. -/
theorem viewAt_bView_agree (γ : BNames) (q : Qp) (vd vd' : VData) :
    viewAt (GF := GF) γ vd ∗ bView γ q vd' ⊢ ⌜vd = vd'⌝ := by
  unfold viewAt bView
  iintro ⟨Ha, Hb, -⟩
  icombine Ha Hb gives %H
  ipureintro
  exact H.2

end preds

end backend
end EtcdGrove
end Perennial
