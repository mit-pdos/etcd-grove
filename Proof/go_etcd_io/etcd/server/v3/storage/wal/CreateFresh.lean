/-
`wal.Create.specFresh` (spec `Spec/go_etcd_io/etcd/server/v3/storage/wal/CreateFresh.lean`): the
instance of `wal.Create.spec` at the view predicate `wal.ExistFalseOk` (`notes/wal-units/fresh.md`).
Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.wal.Create
public import Spec.go_etcd_io.etcd.server.v3.storage.wal.CreateFresh

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

theorem wal.Create.wp_specFresh (P : WalPbIn GF) (Mr : WalMarshal)
    (wp_Create : wal.Create.spec (GF := GF) P Mr) : wal.Create.specFresh (GF := GF) P Mr :=
  fun lg R jr r dir nm mp md qp Q => wp_Create lg R jr r dir nm mp md qp Q wal.ExistFalseOk

end proof

end EtcdGrove
end Perennial
