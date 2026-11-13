/-
`(*WAL).sync`: the encoder's `flush` (over the guarded writer) and the tail's `Fdatasync`, whose success raises the invariant's synced mark (`walSyncedLb`). Proved over the callees' specs (`sorry` while W6 is in progress). Lean-first.
-/
module

public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.WAL__sync
public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.encoder__encodeG

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI
open Fs WalEnc WalFs

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [W : WalGS GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.wal.Assumptions]
variable [os_sem : os.Assumptions] [ioutil_sem : go_etcd_io.etcd.pkg.v3.ioutil.Assumptions]

/-- See the file header. -/
theorem go_etcd_io.etcd.server.v3.storage.wal.WAL.sync.wp_proof (P : WalPbIn GF) (Mr : WalMarshal) :
    go_etcd_io.etcd.server.v3.storage.wal.WAL.sync.spec (W := W) P Mr := by
  sorry

end proof

end EtcdGrove
end Perennial
