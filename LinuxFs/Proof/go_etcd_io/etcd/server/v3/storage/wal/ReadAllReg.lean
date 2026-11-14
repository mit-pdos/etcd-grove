/- Lean-first (no Rocq counterpart).

# `ReadAll`'s tail registration (W3/W5 of `notes/wal-fsext-plan.md`, twenty-third session)

`ReadAll`'s tail, as the handle's: `walTailW_ofRead` (the decoder's stream state of the last file, a
key and the tail record as `walTailW`; the pending registration's form is `walTailP_ofRead`,
`ReadAllPend.lean`, over `walInvRegisterPendLaw`, `ReadAllRegPend.lean`, which replaced this file's
`walInvRegisterTailLaw`, 2026-11-14).

`walOpening_cutFrag`: the opening handle's lock token lends its pending-cut flag (`walCutFrag none`,
which the tail's fdatasync takes).
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.ReadAllInv
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.ReadDefs
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.Handle
import all LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.Ghost

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Fs WalEnc

section iris
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext] [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [W : WalGS GF]

/-- **The opening handle lends its pending-cut flag** (see the file header). -/
theorem walOpening_cutFrag (w : Loc) (dir : GoString) (s : w64 × w64) :
    walOpening (W := W) w dir s ⊢
      walCutFrag (W := W) none ∗ (walCutFrag (W := W) none -∗ walOpening (W := W) w dir s) := by
  unfold walOpening walHandleP walLockedTok
  iintro ⟨%γ, Hd, Hm, Hp, Ht, Hpk, Hc⟩
  iframe Hc
  iintro Hc
  iexists γ
  iframe

end iris

section tail
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext] [go.BasicIntoValInj]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [W : WalGS GF]
variable [sem : go.Semantics] [package_sem : go_etcd_io.etcd.server.v3.storage.wal.Assumptions]
variable [os_sem : os.Assumptions] [bufio_sem : _root_.Perennial.bufio.Assumptions]
variable [ioutil_sem : go_etcd_io.etcd.pkg.v3.ioutil.Assumptions]

/-- The write-mode open flags give a writable fd. -/
theorem openFd_write (i : Ino) : openFd i (walReadFlag true) = ⟨i, true, true⟩ := by
  unfold openFd walReadFlag; simp only [↓reduceIte]; congr <;> decide

/-- **The read tail as the handle's tail** (`walTailW`), at its write position `lay.wr` with
nothing written: the decoder's stream state of the last file, the registration's key and record. -/
theorem walTailW_ofRead (f : Loc) (fd : w64) (name dir : GoString) (γ : GName) (g : SegG) (d : WalDur)
    (lay : WalLay) (hfd : 0 ≤ fd.toInt) (hm : TailMeta g.om g.bs) (hsz : g.om.size ≤ 0xffffffff000) :
    os.ownFile f fd name (DFrac.own 1) ∗ osFd fd (DFrac.own 1) (openFd g.ino (walReadFlag true)) ∗
      os.ownOff f (W64 (lay.wr : Int)) ∗ walTailKey (W := W) dir γ ∗
      osMeta g.ino (DFrac.own (1 : Qp).half) g.om ∗ osBytes g.ino 0 (DFrac.own (1 : Qp).half) g.bs ∗
      (letI := walAllG (W := W); ghostVar γ (1 : Qp).half (tailG d lay g.ino none)) ⊢
    walTailW (W := W) f fd name dir γ g.ino d.H d.metadata lay.cuts lay.wr g.om.size [] := by
  iintro ⟨Hf, Hfd, Ho, Hk, Hm, Hb, Hv⟩
  unfold walTailW
  rw [openFd_write]
  rw [show ((lay.wr : Int) + (([] : List w8).length : Int)) = (lay.wr : Int) by simp]
  iframe Hf Ho Hk
  isplitl [Hfd]
  · iexists true; iexact Hfd
  iexists g.om, g.bs
  iframe Hm Hb
  isplitr
  · ipureintro; exact ⟨rfl, hm, by omega, hfd, hm.loWr _⟩
  · unfold tailG; iexact Hv

/-- A zero errno is no error. -/
theorem errnoErr_zero : errnoErr (W64 0) = interface.nil := by
  unfold errnoErr; simp

/-- A nonzero errno is an error. -/
theorem errnoErr_ne (e : w64) (h : e ≠ 0) : errnoErr e ≠ interface.nil := by
  unfold errnoErr; rw [if_neg h]; simp

end tail

end WalFs
end EtcdGrove
end Perennial
