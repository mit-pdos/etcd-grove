/-
`rec.Validate(crc)` (record.go:26-31, translated): `nil` iff the record's CRC is `crc`, else an
error (`fmt.Errorf` wrapping `ErrCRCMismatch`). Over `fmt.ErrorfErrs.spec` (a hypothesis,
`LinuxFs/Spec/fmt/ErrorfErrs.lean`). Proved in `LinuxFs/Proof/go_etcd_io/etcd/server/v3/storage/wal/walpb/Record__Validate.lean`.
W3a of `notes/wal-fsext-plan.md`; Lean-first.
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.walpb.Defs
public import LinuxFs.Spec.fmt.ErrorfErrs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI
open WalEnc WalFs

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [go_etcd_io.etcd.server.v3.storage.wal.walpb.Assumptions]

/-- See the file header. -/
abbrev go_etcd_io.etcd.server.v3.storage.wal.walpb.Record.Validate.spec : Prop :=
  ∀ (l : Loc) (r : WalRec) (crc : w32) (e : GoInterfaceOk),
  {{ isPkgInit (PROP := IProp GF) pkg_id.fmt ∗
      globalAddr go_etcd_io.etcd.server.v3.storage.wal.walpb.ErrCRCMismatch ↦□ GoInterface.ok e ∗
      errOk e ∗ ownRec l r }}
    (App (Val (l @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.wal.walpb.Record.ty @!! go!"Validate")) (Val #crc))
  {{ (err : GoInterface), RET #err; ownRec l r ∗
      (⌜err = GoInterface.nil ∧ r.crc = crc⌝ ∨
       ⌜r.crc ≠ crc⌝ ∗ ∃ ei : GoInterfaceOk, ⌜err = GoInterface.ok ei⌝ ∗ errOk ei) }}

end spec

end EtcdGrove
end Perennial
