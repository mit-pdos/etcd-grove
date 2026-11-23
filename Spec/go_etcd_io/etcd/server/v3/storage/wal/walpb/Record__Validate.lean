/-
`rec.Validate(crc)` (record.go:26-31, translated): `nil` iff the record's CRC is `crc`, else an
error (`fmt.Errorf` wrapping `ErrCRCMismatch`), which is not `t` and on which `errors.Is(_, t)` is false
(`errTreeNot`) for a pointer target `t` that is no `*fmt.wrapError` and of which `ErrCRCMismatch` is not (`io.EOF`,
for the decoder's reader: ledger 2026-11-14, "the error's identity"). `errors.Is` on it returns for every pointer
target, given that it does on `ErrCRCMismatch` (`errTreeTerm`; 2026-11-14, `wal-vsnap3`). Since 2026-11-22 these
facts are error trees (`Spec/errors/ErrTree.lean`; ledger 2026-11-22, "`fmt.ErrorfErrsNot.spec`/
`fmt.ErrorfErrsTerm.spec` -- premises no proof can use"), and the target's variable is no longer named. Over
`fmt.ErrorfErrsNot.spec` (proved, `Proof/fmt/ErrorfErrsNot.lean`). Proved in `Proof/go_etcd_io/etcd/server/v3/storage/wal/walpb/Record__Validate.lean`.
W3a of `notes/wal-fsext-plan.md`; Lean-first.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.wal.walpb.Defs
public import Spec.fmt.ErrorfErrsNot

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
  ∀ (l : Loc) (r : WalRec) (crc : w32) (e : GoInterfaceOk) (t : GoInterface),
  (∀ tii, t = interface.ok tii → _root_.Perennial.errors.IsPointerError tii ∧
    tii.ty ≠ go.GoType.PointerType _root_.Perennial.fmt.wrapError.ty) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.fmt ∗
      globalAddr go_etcd_io.etcd.server.v3.storage.wal.walpb.ErrCRCMismatch ↦□ GoInterface.ok e ∗
      errOk e ∗ errTreeNot (GoInterface.ok e) t ∗ errTreeTerm (GoInterface.ok e) ∗
      ownRec l r }}
    (App (Val (l @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.wal.walpb.Record.ty @!! go!"Validate")) (Val #crc))
  {{ (err : GoInterface), RET #err; ownRec l r ∗
      (⌜err = GoInterface.nil ∧ r.crc = crc⌝ ∨
       ⌜r.crc ≠ crc⌝ ∗ ∃ ei : GoInterfaceOk, ⌜err = GoInterface.ok ei⌝ ∗ errOk ei ∗
         errTreeNot (GoInterface.ok ei) t ∗ errTreeTerm (GoInterface.ok ei)) }}

end spec

end EtcdGrove
end Perennial
