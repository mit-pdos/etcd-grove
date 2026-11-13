/- Lean-first (no Rocq counterpart).

# The crash-aware tail write (W6 of `notes/wal-fsext-plan.md`; "W6 implementation log")

The WAL's tail is crash-tracked: the invariant (`walInv`, `Inv.lean`) holds half of its `OsMeta` and
bytes, the handle the other half (`walTailW`, `Handle.lean`). A `pwrite` on it is two steps of the
extension (`PWriteStart`, `PWriteFinish`, `GooseLang/Ext/Fs/Write.lean`); each opens `walInv`, with
`notCrashed` (`wp_atomic_nc`, `GooseLang/Ext/Fs/NotCrashedAcc.lean`), and keeps its crash condition:

* **the start** (`wp_tailPWriteStart`): the handle's halves and the invariant's make the file's
  `OsMeta` and the written range whole; the step's token goes into the invariant with the halves of
  the bytes around it (a write in flight, `SegFl`, `segResF`), the layout's tail becoming the
  segment as the write announced it (`SegFl.Ok`: each byte of the range gets the candidate of its
  intended value, `ByteOk`'s announced case). The program keeps its halves of the bytes around the
  range and its half of the tail record, now with the write in flight;
* **the finish** (`wp_tailPWriteFinish`): the token back, the file idle again as the `k` bytes
  written leave it (`pwPost`, `finBytes`), the write position `wr + k`, halves split again.

Both rest on the pure layout lemmas `walsOk_announce`/`walsOk_finish`: the static relation and the
crash condition of the tail after the step, its bytes past `wr` the intended stream's (the record ties
the program's history to the invariant's), over zeros (F-Z, `TailZeros`). **The crash condition of
an append is the hard part** (any image mixing the old zeros and the new frames, under W1, decodes
to an image of the history: the encoding layer's prefix lemma).

The contract (`wal.tailWriter`): `walTailW` is an `io.writerStreamP` with the guard `tailOk` (a prefix
of the intended stream inside the preallocated size). Its proof: `(*os.File).Write` over a
`WriteAt` whose attempts are the two steps above (the loop of `os.File.WriteAt.wp_proof_crash`,
`LinuxFs/Proof/os/Crash.lean`, with these steps in place of `cfInv`'s; `os.File.Write.wp_spec`,
`Off.lean`, generalized over its `WriteAt` contract).

**Writes past the preallocated size are not covered** (`tailOk`'s second clause, `SegFl.Ok`'s first):
the layout's `wr ≤ old.length`, and a write in flight past the size has no ghost candidates for the
bytes it extends the file with (`cfMeta`'s zeros move to the write's end; the step's `OsMeta.pc`
past the size would be the source). The `Save` that crosses `SegmentSizeBytes` writes there.

Status: statements; the proofs are `sorry` (plans above).
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.Handle
public import LinuxFs.Proof.os.CrashWrite

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Iris.BI Fs WalEnc

section tail
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [W : WalGS GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.wal.Assumptions]
variable [os_sem : os.Assumptions] [ioutil_sem : go_etcd_io.etcd.pkg.v3.ioutil.Assumptions]

/-- **The program's part of the tail `i` while the write `fl` is in flight on it**: its key and half
of the tail record (with the write), and its halves of the bytes around the written range. -/
def walTailFl (dir : GoString) (γ : GName) (tg : TailG) (i : Ino) (fl : SegFl) : IProp GF :=
  letI := walAllG (W := W)
  iprop(walTailKey (W := W) dir γ ∗ ghostVar γ (1 : Qp).half tg ∗
    osBytes i 0 (DFrac.own (1 : Qp).half) (fl.bs.take fl.off) ∗
    osBytes i (fl.off + fl.data.length) (DFrac.own (1 : Qp).half)
      (fl.bs.drop (fl.off + fl.data.length)))

/-- **The first step of a `pwrite` on the tail** (see the file header): at the write position `wr`,
of the next bytes of the intended stream, inside the file. -/
theorem wp_tailPWriteStart (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString) (dir : GoString)
    (γ : GName) (H : List (WalOpG WalEnt)) (md : List w8) (cuts : List Nat) (wr : Nat)
    (m : OsMeta) (bs : List ByteG) (fd off : w64) (data : List w8) (dq : DFrac) (d : OsFd)
    (Φ : val → IProp GF)
    (hwr : d.writable = true) (hoff0 : 0 ≤ off.toInt) (hoff : off.toNat = wr) (hd : data ≠ [])
    (hin : wr + data.length ≤ m.size) (hS : data <+: (tailStream Mr H md cuts).drop wr) :
    ⊢ walAreaOk walCodec Mr R jr r -∗ osFd fd dq d -∗ walTailKey (W := W) dir γ -∗
      ghostVar γ (1 : Qp).half ((H, md, cuts, wr, d.ino, none) : TailG) -∗
      osMeta d.ino (DFrac.own (1 : Qp).half) m -∗ osBytes d.ino 0 (DFrac.own (1 : Qp).half) bs -∗
      (∀ t : Nat, ∀ n : Nat, osFd fd dq d -∗
        walTailFl dir γ (H, md, cuts, wr, d.ino, some ⟨t, wr, data, n, m, bs, none⟩) d.ino
          ⟨t, wr, data, n, m, bs, none⟩ -∗ Φ (osTokV t)) -∗
      WP (ExternalOp fsExt.name "PWriteStart" (Val (PairV (#fd) (PairV (#off) (#data))))) {{ Φ }} := by
  sorry

/-- **The second step of a `pwrite` on the tail** (see the file header): the `k` bytes written, the
write position past them, the file idle. -/
theorem wp_tailPWriteFinish (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString) (dir : GoString)
    (γ : GName) (H : List (WalOpG WalEnt)) (md : List w8) (cuts : List Nat) (i : Ino) (fl : SegFl)
    (Φ : val → IProp GF) :
    ⊢ walAreaOk walCodec Mr R jr r -∗
      walTailFl dir γ (H, md, cuts, fl.off, i, some fl) i fl -∗
      (∀ (k : Nat) (e : w64) (zs : List Cands),
        ⌜k ≤ fl.data.length ∧ ((k = fl.data.length ∨ 0 < k) ∧ e = 0 ∨ e ≠ 0)⌝ -∗
        walTailKey (W := W) dir γ -∗
        ghostVar γ (1 : Qp).half ((H, md, cuts, fl.off + k, i, none) : TailG) -∗
        osMeta i (DFrac.own (1 : Qp).half) (pwPost fl.m fl.off fl.data.length k) -∗
        osBytes i 0 (DFrac.own (1 : Qp).half) (finBytes fl.m fl.bs fl.off fl.data k fl.n zs) -∗
        Φ (PairV (#(W64 k)) (#e))) -∗
      WP (ExternalOp fsExt.name "PWriteFinish" (Val (osTokV fl.t))) {{ Φ }} := by
  sorry

/-- **The tail's writer** (see the file header): the tail file `f` of inode `i`, written from the
encoder's start `o0`, is a guarded stream of its intended bytes (`tailOk`); a failed write leaves
nothing the program keeps (the invariant holds what it wrote; the handle is lost). -/
theorem wal.tailWriter (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString) (f : Loc) (fd : w64)
    (name dir : GoString) (γ : GName) (i : Ino) (H : List (WalOpG WalEnt)) (md : List w8)
    (cuts : List Nat) (o0 sz : Nat) :
    ⊢ walAreaOk walCodec Mr R jr r -∗
      io.writerStreamP (wal.fileWi f) (tailOk Mr H md cuts o0 sz)
        (walTailW (W := W) f fd name dir γ i H md cuts o0 sz) (fun _ _ => iprop(True)) := by
  sorry

end tail

end WalFs
end EtcdGrove
end Perennial

end
