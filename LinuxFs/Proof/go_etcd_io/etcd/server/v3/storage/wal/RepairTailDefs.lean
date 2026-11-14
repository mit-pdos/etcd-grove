/- Lean-first (no Rocq counterpart).

# The tail `Repair` registers and truncates (W7 of `notes/wal-fsext-plan.md`; the W7-W12 log, thirteenth session)

`Repair` registers its WAL's tail pending after `openLast` (`walInvRegisterPendLaw`: the pending token
`walPendTok dir γ |old|`, kind `true`), reads it to the end (`io.Copy` into the `.broken` file), then
truncates it at the last record's end (`wr`) and fsyncs it. Its handle's tail is `walTailP` with the
offset as a parameter (`walTailPO`): after `io.Copy` the file's offset is its end, not `wr`, and neither
the truncate nor the fsync touches it.

* `TailMetaRW`: the tail after the truncate landed (`TailMetaR` with a resize window open: `lo ≤ size ≤
  hi`).
* `walTailPO`: `walTailP` with the offset `off` for `o0 + |out|` (`walTailP_po`).
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.HandlePend

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Iris.BI Fs WalEnc

/-- **The tail after `Repair`'s truncate landed** (until its fsync): all its bytes, no mappings, a resize
window open on it (a crash may leave any size from `lo` to `hi`). -/
def TailMetaRW (m : Fs.OsMeta) (bs : List Fs.ByteG) : Prop :=
  bs.length = m.size ∧ m.maps = ∅ ∧ m.lo ≤ m.size ∧ m.size ≤ m.hi

section handle
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [W : WalGS GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.wal.Assumptions]
variable [os_sem : os.Assumptions] [ioutil_sem : go_etcd_io.etcd.pkg.v3.ioutil.Assumptions]

/-- **The handle's tail, lent, at any offset** (see the file header): `walTailP … o0 sz [] k p tm` with
the file's offset `off`. -/
def walTailPO (f : Loc) (fd : w64) (name : GoString) (dir : GoString) (γ : GName) (i : Ino)
    (H : List (WalOpG WalEnt)) (md : List w8) (cuts : List Nat) (o0 sz : Nat) (k : Nat) (p : Bool)
    (off : w64) (tm : Fs.OsMeta → List Fs.ByteG → Prop) : IProp GF :=
  letI := walAllG (W := W)
  iprop(os.ownFile f fd name (DFrac.own 1) ∗ (∃ rd : Bool, osFd fd (DFrac.own 1) ⟨i, rd, true⟩) ∗
    os.ownOff f off ∗ walLentTokB (W := W) dir γ k p ∗
    ∃ (m : OsMeta) (bs : List ByteG),
    osMeta i (DFrac.own (1 : Qp).half) m ∗ osBytes i 0 (DFrac.own (1 : Qp).half) bs ∗
    ⌜m.size = sz ∧ tm m bs ∧ sz < 2 ^ 62 ∧ 0 ≤ fd.toInt ∧ LoWr m o0⌝ ∗
    ghostVar γ (1 : Qp).half ((H, md, cuts, o0, i, none) : TailG))

/-- `walTailP` at an empty `out` is `walTailPO` at the write position. -/
theorem walTailP_po (f : Loc) (fd : w64) (name : GoString) (dir : GoString) (γ : GName) (i : Ino)
    (H : List (WalOpG WalEnt)) (md : List w8) (cuts : List Nat) (o0 sz : Nat) (k : Nat) (p : Bool)
    (tm : Fs.OsMeta → List Fs.ByteG → Prop) :
    walTailP (W := W) f fd name dir γ i H md cuts o0 sz [] k p tm ⊣⊢
      walTailPO (W := W) f fd name dir γ i H md cuts o0 sz k p (W64 o0) tm := by
  unfold walTailP walTailPO
  simp only [List.length_nil, Nat.add_zero]
  exact .rfl

end handle

end WalFs
end EtcdGrove
end Perennial

end
