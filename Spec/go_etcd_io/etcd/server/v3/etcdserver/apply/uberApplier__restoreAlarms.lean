/-
`apply.uberApplier.restoreAlarms` (uber_applier.go). Lean-first (no Rocq counterpart); the vocabulary is
`Proof/go_etcd_io/etcd/server/v3/etcdserver/apply/InvUber.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.InvUber

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver.apply go_etcd_io.etcd.api.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions]

/-- **`a.restoreAlarms()`**: `applyV3` is the base chain's applier wrapped as the alarm store's
answers ask (`capped` for a `NOSPACE` alarm, then `corrupt` for a `CORRUPT` one; the store's
answers are any slices: any `ns cr`). -/
abbrev apply.uberApplier.restoreAlarms.spec : Prop :=
  ∀ (p ast : Loc) (base a : GoInterface) (T : IProp GF) (z : Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗
      structFieldRef uberApplier go!"alarmStore" p ↦□ ast ∗ apply.alarmGetIs ast T z ∗ T ∗
      structFieldRef uberApplier go!"applyV3base" p ↦□ base ∗
      structFieldRef uberApplier go!"applyV3" p ↦ a }}
    (App (Val (p @!! go.GoType.PointerType uberApplier.ty @!! go!"restoreAlarms")) (Val #()))
  {{ RET #(); T ∗ ∃ (ns cr : Bool) (a' : GoInterface), ⌜z = true → ns = false ∧ cr = false⌝ ∗
      structFieldRef uberApplier go!"applyV3" p ↦ a' ∗
      □ (∀ E : AEnv GF, apply.applierSpec E (apply.baseChain E.authOn) base -∗
        apply.applierSpec E (apply.alarmChain E.authOn ns cr) a') ∗
      apply.alarmShape ns cr base a' }}

end spec

end EtcdGrove
end Perennial
