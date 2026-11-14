/- Lean-first (no Rocq counterpart).

# What `openLast` hands `Repair` (W7 of `notes/wal-fsext-plan.md`; the W7-W12 log, eighth session)

`walLastOpen C Mr R jr dir lf`: the pin of the WAL's last segment (`walPinLast`'s resources, `RepairPin.lean`,
with the segment named), a kept path to the WAL directory (`walInv_dirPath`'s), and the last segment's file
opened read-write and locked (`fileutil.LockFile(last, O_RDWR, 0600)`: the `*LockedFile` `lf`, its
`*os.File` at offset 0, the fd whole). `Repair`'s proof reads the segment through it (law L2), truncates
it (L4) and puts the pin back (L5).
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.RepairPin
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.ReadDefs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Fs WalEnc

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [W : WalGS GF]
variable [sem : go.Semantics]

/-- See the file header. -/
def walLastOpen (C : WalCodec) (Mr : WalMarshal) (R : Roots) (jr : Ino) (dir : GoString) (lf : Loc) :
    IProp GF :=
  iprop(∃ (d : WalDur) (lay : WalLay) (X : List GoString) (hj : NamesH) (gL : SegG) (f : Loc)
      (fd : w64) (qd : Qp),
    ⌜lay.jr = jr ∧ (∀ b ∈ X, walNameP b = false) ∧
      ClaimCoh hj lay.j (.except X) ∧ WalAbsD C Mr d lay hj.cur ∧ TailIdle C Mr d lay ∧
      (lay.segs.map (·.ino)).Nodup ∧ SegsNamed lay.segs hj.cur ∧ lay.segs.getLast? = some gL ∧
      0 ≤ fd.toInt⌝ ∗
    walDirKey (W := W) dir lay.j X ∗ walLockedTok (W := W) ∗
    (walTailsFrag (W := W) ∅ ∗ walNamesFrag (W := W) none) ∗
    walOutFrag (W := W) ⟨[gL.ino], [(lay.j, .except X)], []⟩ ∗
    segRes (L := hG.goose_localGS) gL ∗ osNames (L := hG.goose_localGS) lay.j (.except X) (DFrac.own (1 : Qp).half) hj ∗
    osPathS (L := hG.goose_localGS) R dir (DFrac.own qd) lay.j ∗
    fileutil.lockedFile lf f ∗ os.ownFile f fd (child dir gL.name) (DFrac.own 1) ∗
    os.ownOff f (W64 0) ∗ osFd (L := hG.goose_localGS) fd (DFrac.own 1) (openFd gL.ino (W64 2 ||| W64 0x80000)))

end defs

end WalFs
end EtcdGrove
end Perennial

end
