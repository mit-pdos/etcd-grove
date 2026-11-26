/- Lean-first (no Rocq counterpart).

# The tail `Repair` registers and truncates (W7 of `notes/wal-fsext-plan.md`; the W7-W12 log, thirteenth session)

`Repair` registers its WAL's tail pending after `openLast` (`walInvRegisterPendLaw`: the pending token
`walPendTok dir γ |old|`, kind `true`), reads it to the end (`io.Copy` into the `.broken` file), then
truncates it at the end of the frames it read (`tg`: `wr`, or past it the end of a pending run, P6) and
fsyncs it. Its handle's tail is `walTailP` with the
offset as a parameter (`walTailPO`): after `io.Copy` the file's offset is its end, not `wr`, and neither
the truncate nor the fsync touches it.

* `TailMetaRW`: the tail after the truncate landed (`TailMetaR` with a resize window open: `lo ≤ size ≤
  hi`).
* `TailMetaRP`: the tail before the truncate (`TailMetaR`), and, the target `tg` past `o0`, a nonzero
  byte in `[o0, tg)` (the length word of the run's first frame; P6, `walTail_truncSupR`'s tie), and the
  reader's stop at `o0` on the bytes below `tg` (`PendStop`: the run, then nothing); `TailMetaRWP`:
  `TailMetaRW` with that stop, what the fsync needs (`syncLay_anyE`).
* `walTailPO`: `walTailP` with the offset `off` for `o0 + |out|` (`walTailP_po`), without `LoWr` (P6: past
  the truncate to `tg > o0` the window's `lo` is `tg`; the truncate reads it off `TailMetaR`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.wal.HandlePend

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

/-- **The tail before `Repair`'s truncate to `tg`** (see the file header): the reader, from `o0` at the
chain value `c`, accepts a run of entry records in the bytes below `tg`, then nothing (`PendStop`). -/
def TailMetaRP [GooseExts] (Mr : WalMarshal) (c : w32) (o0 tg : Nat) (m : Fs.OsMeta) (bs : List Fs.ByteG) :
    Prop :=
  TailMetaR m bs ∧ (tg = o0 ∨ ∃ b x, o0 ≤ b ∧ b < tg ∧ bs[b]? = some x ∧ x.1 ≠ 0) ∧
    PendStop walCodec Mr ((bs.take tg).map (·.1)) o0 c

/-- **The tail after `Repair`'s truncate to `tg` landed**: `TailMetaRW`, and the reader's stop of
`TailMetaRP` on its bytes. -/
def TailMetaRWP [GooseExts] (Mr : WalMarshal) (c : w32) (o0 : Nat) (m : Fs.OsMeta) (bs : List Fs.ByteG) :
    Prop :=
  TailMetaRW m bs ∧ o0 ≤ m.size ∧ PendStop walCodec Mr (bs.map (·.1)) o0 c

theorem TailMetaRWP.tailMetaE [GooseExts] {Mr : WalMarshal} {c : w32} {o0 : Nat} {m : Fs.OsMeta}
    {bs : List Fs.ByteG} (h : TailMetaRWP Mr c o0 m bs) : TailMetaE Mr c o0 m bs :=
  ⟨h.1.1, h.1.2.1, h.2.1, h.2.2⟩

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
  iprop(os.ownFile f fd name (DFrac.own 1) ∗ (∃ (rd : Bool) (lo lk : Option Bool), osFd fd (DFrac.own 1) ⟨i, rd, true, lo, lk⟩ ∗
    fdLocks fd ⟨i, rd, true, lo, lk⟩) ∗
    os.ownOff f off ∗ walLentTokB (W := W) dir γ k p ∗
    ∃ (m : OsMeta) (bs : List ByteG),
    osMeta i (DFrac.own (1 : Qp).half) m ∗ osBytes i 0 (DFrac.own (1 : Qp).half) bs ∗
    ⌜m.size = sz ∧ tm m bs ∧ sz < 2 ^ 62 ∧ 0 ≤ fd.toInt⌝ ∗
    ghostVar γ (1 : Qp).half ((H, md, cuts, o0, i, none) : TailG))

/-- `walTailP` at an empty `out` is `walTailPO` at the write position (forgetting that the tail is locked,
`fdLocksW`). -/
theorem walTailP_po (f : Loc) (fd : w64) (name : GoString) (dir : GoString) (γ : GName) (i : Ino)
    (H : List (WalOpG WalEnt)) (md : List w8) (cuts : List Nat) (o0 sz : Nat) (k : Nat) (p : Bool)
    (tm : Fs.OsMeta → List Fs.ByteG → Prop) :
    walTailP (W := W) f fd name dir γ i H md cuts o0 sz [] k p tm ⊢
      walTailPO (W := W) f fd name dir γ i H md cuts o0 sz k p (W64 o0) tm := by
  unfold walTailP walTailPO
  rw [show ((o0 : Int) + (([] : List w8).length : Int)) = (o0 : Int) by simp]
  simp only [List.length_nil, Nat.add_zero]
  iintro ⟨Hf, ⟨%rd, %lo, %lk, Hfd, Hl⟩, Ho, Hk, %m, %bs, Hm, Hb, %hp, Hv⟩
  iframe Hf Ho Hk
  isplitl [Hfd Hl]
  · iexists rd, lo, lk; iframe Hfd; iapply fdLocksW_locks $$ Hl
  iexists m, bs
  iframe
  ipureintro; exact ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1⟩

end handle

end WalFs
end EtcdGrove
end Perennial

end
