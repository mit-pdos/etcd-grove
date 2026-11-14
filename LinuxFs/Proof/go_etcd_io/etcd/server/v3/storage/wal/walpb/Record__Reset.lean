/-
The proof of `walpb.Record.Reset.spec`, over the trusted model `Record.Reset.impl`
(`LinuxFs/TrustedCode/go_etcd_io/etcd/server/v3/storage/wal/walpb.lean`: the store of `Record`'s
zero value; pending the user's review).
-/
module

public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.walpb.Record__Reset

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open WalEnc WalFs

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [go_etcd_io.etcd.server.v3.storage.wal.walpb.Assumptions]

/-- The model's type by name is the translation's `Record.ty`. -/
theorem walpb_model_Record_eq :
    go_etcd_io.etcd.server.v3.storage.wal.walpb.model.Record =
      go_etcd_io.etcd.server.v3.storage.wal.walpb.Record.ty := by
  unfold go_etcd_io.etcd.server.v3.storage.wal.walpb.Record.ty; rfl

theorem go_etcd_io.etcd.server.v3.storage.wal.walpb.Record.Reset.wp_proof :
    go_etcd_io.etcd.server.v3.storage.wal.walpb.Record.Reset.spec (GF := GF) (hG := hG) := by
  intro l
  wp_start as Hl
  iunfold ownRecAny at Hl
  icases Hl with ⟨%v, Hl⟩
  rw [walpb_model_Record_eq]
  wp_auto
  iapply HΦ
  rw [pbRecordC_blank]
  iexact Hl

end proof

end EtcdGrove
end Perennial
