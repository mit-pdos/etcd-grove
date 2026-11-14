/-
The proof of `LinuxFs/Spec/go_etcd_io/etcd/server/v3/storage/wal/OpenForRead.lean` (W5 of
`notes/wal-fsext-plan.md`): `openAtIndex`'s spec in read mode.
-/
module

public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.OpenForRead
public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.openAtIndex
import all LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.ReadDefs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode
open Fs WalEnc WalFs

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [W : WalGS GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.wal.Assumptions]

theorem go_etcd_io.etcd.server.v3.storage.wal.OpenForRead.wp_proof (Mr : WalMarshal)
    (wp_open : go_etcd_io.etcd.server.v3.storage.wal.openAtIndex.spec (W := W) Mr) :
    go_etcd_io.etcd.server.v3.storage.wal.OpenForRead.spec (W := W) Mr := by
  intro lg R jr r dir nm sp s qp Q hin hnmO hr hdl
  wp_start as ⟨#Hzap, #Hok, Hp, Hres, Hperm, #Hsp, Hu, Hau⟩
  try wp_auto
  wp_apply wp_open lg R jr r dir nm sp s false qp Q hin hnmO hr hdl $$ [Hp Hres Hperm Hu Hau]
    as %w %err ⟨Hp, Hres, %o, HQ, Hr⟩
  · iframe; iframe #
  iapply HΦ
  iframe Hp Hres
  icases Hr with (⟨%he, Hu, Hperm, -⟩ | ⟨%he, %ho, Hdf, Hl, Hrh, Hperm⟩)
  · iframe Hperm
    iexists o
    iframe HQ
    ileft
    iframe Hu
    ipureintro; exact he
  · iframe Hperm
    iexists o
    iframe HQ
    iright
    isplitr
    · ipureintro; exact he
    isplitr
    · ipureintro; exact ho
    unfold walReadOnlyF
    iframe

end proof

end EtcdGrove
end Perennial
