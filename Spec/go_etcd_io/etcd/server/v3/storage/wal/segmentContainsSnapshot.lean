/- The read-only probe of a segment strictly before a modern starting file. -/
module
public import Spec.go_etcd_io.etcd.server.v3.storage.wal.snapshotPrefix
public import Spec.go_etcd_io.etcd.server.v3.storage.wal.openWALFiles
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.ReadAllPrefixDecode

@[expose] public section
noncomputable section
namespace Perennial.EtcdGrove
open Iris Iris.BI Fs WalFs WalEnc
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext] [go.BasicIntoValInj]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [go.Semantics] [go_etcd_io.etcd.server.v3.storage.wal.Assumptions]

def wal.probeOwn (R : Roots) (dir : GoString) (j : Ino) (dq : DFrac) (qc : Qp)
    (N : NameSet) (dqn : DFrac) (hj : NamesH) (g : SegG) : IProp GF :=
  iprop(osPathS R dir dq j ∗ osCallPerm (callKey R dir) qc ∗ osNames j N dqn hj ∗
    segRes (L := hG.goose_localGS) g)

abbrev wal.segmentContainsSnapshot.spec (U : WalUnmarshal) : Prop :=
  ∀ (lg : Loc) (R : Roots) (dir : GoString) (j : Ino) (dq : DFrac) (qc : Qp)
    (N : NameSet) (dqn : DFrac) (hj : NamesH) (g : SegG) (index : w64),
    PathFits dir → N.Mem g.name → NameOk g.name → g.name.length ≤ 255 →
    hj.cur !! g.name = some (.file g.ino) → g.om.size = g.bs.length →
    ProbeBelow walCodec U (uint.nat index) [segImg g] 0 0#32 →
    wal.prefixFileMiss (iprop(isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.wal ∗
      zapLoggerOk lg ∗ osInv ∗ osSharedInv R ∗ wal.probeOwn R dir j dq qc N dqn hj g))
      lg dir g.name index

end Perennial.EtcdGrove
