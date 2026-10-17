/-
`v3compactor.New` (`compactor.go`; etcd#22095 adds the mode `auto-periodic` and the arguments
`sg`, `maxBytes`). Lean-first (no Rocq counterpart).
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
def v3compactor.newResult (lg : Loc) (mode : GoString) (retention : w64) (rg c sg : GoInterface)
    (maxBytes : w64) (cmp err : GoInterface) : IProp GF :=
  if mode = go!"periodic" ∨ mode = go!"revision" then iprop(⌜err = GoInterface.nil ∧ cmp ≠ GoInterface.nil⌝)
  else if mode = go!"auto-periodic" then
    iprop(⌜err = GoInterface.nil⌝ ∗ ∃ (ac lg' : Loc) (clk : GoInterface),
      ⌜cmp = GoInterface.ok ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor.AutoPeriodic.ty, #ac⟩ ∧ lg' ≠ null ∧
        (lg ≠ null → lg' = lg)⌝ ∗
      isAutoPeriodic ac ⟨lg', clk, retention, maxBytes, rg, c, sg⟩ ∗ apClockOk clk)
  else iprop(⌜cmp = GoInterface.nil ∧ err ≠ GoInterface.nil⌝)

/-- `New(lg, mode, retention, rg, c, sg, maxBytes)`: for `periodic` and `revision`, some
compactor and no error; for `auto-periodic`, an auto-periodic compactor (`isAutoPeriodic`) over
a real clock (`apClockOk`) with the given retention (`int64(retention)`, a revision count),
quota, revision getter, compactable and size getter, and the given logger (a no-op one if it is
`nil`), and no error; for any other mode, no compactor and an error. In the periodic mode the
retention is at least 10 ns in absolute value (below that the periodic compactor's constructor
panics: `newPeriodic.spec`). -/
abbrev v3compactor.New.spec : Prop :=
  ∀ (lg : Loc) (mode : GoString) (retention : w64) (rg c sg : GoInterface) (maxBytes : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor ∗
      context.isClosedchanInit ∗ ⌜mode = go!"periodic" → 10 ≤ sint.Z retention ∨ sint.Z retention ≤ -10⌝ }}
    (App (App (App (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor.New)) (Val #lg)) (Val #mode))
      (Val #retention)) (Val #rg)) (Val #c)) (Val #sg)) (Val #maxBytes))
  {{ (cmp err : GoInterface), RET (PairV #cmp #err);
      v3compactor.newResult lg mode retention rg c sg maxBytes cmp err }}

end spec

end EtcdGrove
end Perennial
