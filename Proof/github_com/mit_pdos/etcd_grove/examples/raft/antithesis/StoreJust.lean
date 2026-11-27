/-
Lean-first (no Rocq counterpart). #33 parity B1: the `MemoryStorage` justifications of the driver's
detached storage reads (`node.storeBase`, `node.storeConf`): none, as nothing reads them. A defs
module, so that the two proofs share it without one proof importing the other (CLAUDE.md, "Import
tiers").
-/
module

public import Proof.go_etcd_io.raft.v3.InvMemstorage

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace AntHarness

open Iris Iris.BI go_etcd_io.raft.v3

section just
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]

/-- Justifications nothing reads (the detached `Snapshot` call names none). -/
def storeJ : MemJust GF where
  SV _ := iprop(True)
  B _ := iprop(True)
  DL _ := iprop(True)
  SV_pers _ := inferInstance
  B_pers _ := inferInstance
  B_timeless _ := inferInstance
  DL_pers _ := inferInstance

end just

end AntHarness
end EtcdGrove
end Perennial
