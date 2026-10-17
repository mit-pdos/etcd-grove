/-
`v3compactor.New` (`compactor.go`; etcd#18472 adds the argument `interval`, passed to both
compactors' constructors). Lean-first (no Rocq counterpart). (etcd#22095's verification has
another version of this spec, for its `auto-periodic` mode.)
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor.Defs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver.api

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem_ctx : context.Assumptions]
/-- What `New` returns for a mode (see `New.spec`). -/
def v3compactor.newResult (lg : Loc) (mode : GoString) (retention interval : w64) (rg c : GoInterface)
    (cmp err : GoInterface) : IProp GF :=
  if mode = go!"periodic" then
    iprop(⌜err = GoInterface.nil⌝ ∗ ∃ (pc lg' : Loc) (clk : GoInterface),
      ⌜cmp = GoInterface.ok ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor.Periodic.ty, #pc⟩ ∧ lg' ≠ null ∧
        (lg ≠ null → lg' = lg)⌝ ∗
      isPeriodic pc ⟨lg', clk, retention, interval, rg, c⟩ ∗ pdRevs pc [] ∗ pdReader pc ∗
      clockwork.isClock clk)
  else if mode = go!"revision" then
    iprop(⌜err = GoInterface.nil⌝ ∗ ∃ (rc lg' : Loc) (clk : GoInterface),
      ⌜cmp = GoInterface.ok ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor.Revision.ty, #rc⟩ ∧ lg' ≠ null ∧
        (lg ≠ null → lg' = lg)⌝ ∗
      isRevision rc ⟨lg', clk, retention, rvInterval interval, rg, c⟩ ∗ clockwork.isClock clk)
  else iprop(⌜cmp = GoInterface.nil ∧ err ≠ GoInterface.nil⌝)

/-- `New(lg, mode, retention, interval, rg, c)`: for `periodic`, a periodic compactor
(`isPeriodic`, with its revision window and a reader token) with period `retention` and the given
`interval`; for `revision`, a revision compactor (`isRevision`) with retention `int64(retention)`
and the wait `rvInterval interval` (`interval`, or 5 minutes for `0`); both over a real clock,
with the given revision getter and compactable and the given logger (a no-op one if it is `nil`),
and no error; for any other mode, no compactor and an error. In the periodic mode the retention
is at least 10 ns in absolute value (below that the periodic compactor's constructor panics:
`newPeriodic.spec`). -/
abbrev v3compactor.New.spec : Prop :=
  ∀ (lg : Loc) (mode : GoString) (retention interval : w64) (rg c : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor ∗
      context.isClosedchanInit ∗ ⌜mode = go!"periodic" → 10 ≤ sint.Z retention ∨ sint.Z retention ≤ -10⌝ }}
    (App (App (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor.New)) (Val #lg)) (Val #mode))
      (Val #retention)) (Val #interval)) (Val #rg)) (Val #c))
  {{ (cmp err : GoInterface), RET (PairV #cmp #err);
      v3compactor.newResult lg mode retention interval rg c cmp err }}

end spec

end EtcdGrove
end Perennial
