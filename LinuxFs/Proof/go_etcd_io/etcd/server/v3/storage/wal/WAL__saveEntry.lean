/-
`(*WAL).saveEntry` over the tail's `encode` (`encode.specTail`) and two laws of `P` (`WalPbIn.MarshalEntLaw`:
`MustMarshalMessage` of an entry; `WalPbIn.GetIndexLaw`: `GetIndex`). Proved over the callees' specs (`sorry` while
W6 is in progress: the record's guard from `WalHS.Split` and the next record, as `snap_guard`; `recSize_tight`).
Lean-first.
-/
module

public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.WAL__saveEntry
public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.encoder__encodeTail

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
theorem go_etcd_io.etcd.server.v3.storage.wal.WAL.saveEntry.wp_proof (P : WalPbIn GF) (Mr : WalMarshal)
    (wp_encode : go_etcd_io.etcd.server.v3.storage.wal.encoder.encode.specTail (W := W) Mr)
    (wp_marshal : WalPbIn.MarshalEntLaw P Mr) (wp_getIndex : WalPbIn.GetIndexLaw P) :
    go_etcd_io.etcd.server.v3.storage.wal.WAL.saveEntry.spec (W := W) P Mr := by
  sorry

end proof

end EtcdGrove
end Perennial
