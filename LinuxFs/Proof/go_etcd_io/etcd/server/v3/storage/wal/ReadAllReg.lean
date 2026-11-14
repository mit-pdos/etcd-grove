/- Lean-first (no Rocq counterpart).

# `ReadAll`'s tail registration (W3/W5 of `notes/wal-fsext-plan.md`, twenty-third session)

`ReadAll` in write mode makes the WAL's last segment its handle's tail: its `ZeroToEnd`, fdatasync and
encoder work on a registered tail (`walTailW`: the tail record `γ`, half in the invariant's
`walTailsRes`), so the tail is registered when the invariant is looked at, before the loop
(`walInv_readFiles`'s facts, `walTailsRes_register`'s registration). **`walInvRegisterTailLaw`** is that
look with the registration, a hypothesis of `WAL.ReadAll.wp_proof` until the invariant's
registration premise lands (I3b, branch `wal-tc14`: `walTailsRes_register`'s `TailZeros lay` relaxed to
`TailZeros lay ∨ lay.wr = lay.z0`). Its post: `walInv_readFiles`' facts; the holder's half of the
tails' authority with `dir ↦ γ`, the key, the program's half of the tail record `tailG d lay g.ino
none` (`g` the last segment); the last segment's `OsMeta` exact (`TailMeta`: nothing in flight on it,
its known zeros past the size), the invariant's at the pin (no handle held it).

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

/-- **The look at the invariant before `ReadAll`'s loop, registering the tail** (see the file
header). -/
def walInvRegisterTailLaw (C : WalCodec) (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString) : Prop :=
  ∀ (dir : GoString) (j : Ino) (X : List GoString) (hj0 : NamesH) (gs : List SegG) (gl : SegG),
    (∀ g ∈ gs, hj0.cur !! g.name = some (.file g.ino)) →
    (∃ kk, (walNames hj0.cur).drop kk = gs.map (·.name)) →
    (∀ g ∈ gs, g.om.size = g.bs.length) → gs.getLast? = some gl →
    ⊢ walInv (L := hG.goose_localGS) (W := W) C Mr R jr r -∗
      notCrashed (hC := hG.goose_localGS.goose_crashGS) -∗ walDirKey (W := W) dir j X -∗
      osNames (L := hG.goose_localGS) j (.except X) (DFrac.own (1 : Qp).half) hj0 -∗
      walTailsFrag (W := W) ∅ -∗
      ([∗list] g ∈ gs, osMeta (L := hG.goose_localGS) g.ino (DFrac.own (1 : Qp).half) g.om ∗
        osBytes (L := hG.goose_localGS) g.ino 0 (DFrac.own (1 : Qp).half) g.bs) ={⊤}=∗
      notCrashed (hC := hG.goose_localGS.goose_crashGS) ∗
      osNames (L := hG.goose_localGS) j (.except X) (DFrac.own (1 : Qp).half) hj0 ∗
      ([∗list] g ∈ gs, osMeta (L := hG.goose_localGS) g.ino (DFrac.own (1 : Qp).half) g.om ∗
        osBytes (L := hG.goose_localGS) g.ino 0 (DFrac.own (1 : Qp).half) g.bs) ∗
      ∃ (d : WalDur) (lay : WalLay) (kk : Nat) (γ : GName),
        walTailsFrag (W := W) (<[dir := γ]> (∅ : GMap GoString GName)) ∗ walTailKey (W := W) dir γ ∗
        (letI := walAllG (W := W); ghostVar γ (1 : Qp).half (tailG d lay gl.ino none)) ∗
        ⌜lay.j = j ∧ WalAbsD C Mr d lay hj0.cur ∧ TailExact lay ∧
          lay.wr = (segStream C Mr d lay.cuts lay.cuts.length).length ∧ lay.segs.drop kk = gs ∧
          TailMeta gl.om gl.bs⌝

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
  · ipureintro; exact ⟨rfl, hm, by omega, hfd⟩
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
