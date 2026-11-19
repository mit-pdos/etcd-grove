/-
**A piece of `run`'s premise** (`server.go`), Lean-first: the disk snapshot's storage from the
snapshot bundle (`srvSnapDisk_of_RO`). (restart3 A1, 2026-11-15: the restart-only `srvWinPend`, R2d'a
A7, `isServerRunC`'s `Hwpend`, deleted: the fork's window guard defers a merged snapshot inside the
replay window.) Until 2026-11-07 this file held `isServerRun`, `run`'s mode-off premise,
deleted with `RunOn.lean`'s `isServerRunOn` once `isServerRunC` (`AuthCompRows.lean`) stopped
using them (R2d'a swap batch 5; the hub owner's call). The vocabulary (`applyRes`, `applyStart`,
`srvMetaSnap`, ...) is `InvRunRes.lean`'s, the lease subsystem's premise (`lease.runCfg`)
`LeaseRun.lean`'s (2026-11-04, the lease-expiry plan's Part C, option (a)).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.LeaseRun

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

section snapDisk
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- (2026-10-31, #11) **The disk snapshot's storage, from the snapshot path's bundle and the raft
wrapper**: the bundle's storage over the snapshotter (`srvSnapRO`) is the wrapper's, whose WAL
contract is `isRaftNode`'s (`isRNWal`). (Restart S6a: the directory is `srvSnapDir_of_RO`'s.) -/
theorem srvSnapDisk_of_RO (s ci : Loc) (E : apply.AEnv GF) (γr : ReadNames) (γm : GName)
    (Er : RNEnv GF) (γn : RNNames GF) :
    srvSnapRO (GF := GF) s ci E γr γm ∗ isRaftNode Er γn (srvRAddr s) ⊢ srvSnapDisk s γr := by
  iintro ⟨#Hro, #Hrn⟩
  iunfold srvSnapRO at Hro
  icases Hro with ⟨%cfg, %ss, %hk, %lgh, %stp, %γd, %idm, %al, %ast, %lp, %cl, %ps, %dir, %d, %Hp,
    #HL, #Hzl, #HD, #HF, #HFg, #Hvo, #HQ, #HW, #HSs, #HSi, #HH, #HHi, #HSt, -⟩
  iunfold isRaftNode at Hrn
  iNamed Hrn
  icombine HSt Hst gives %Heq
  iunfold srvSnapDisk
  iexists stp
  iframe HSt
  rw [Heq]; iexact Hsti

end snapDisk

end EtcdGrove
end Perennial
