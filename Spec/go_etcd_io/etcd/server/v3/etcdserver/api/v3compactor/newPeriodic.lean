/-
`v3compactor.newPeriodic` (`periodic.go`; etcd#18472 adds the argument `interval`). Lean-first
(no Rocq counterpart).
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
/-- `newPeriodic(lg, clock, h, interval, rg, c)` returns a periodic compactor (`isPeriodic`)
holding its arguments (`period = h`), with an empty revision window (`pdRevs`) and a reader token
of its mutex (`pdReader`), for a retention `h` of at least 10 ns in absolute value: below that,
`getRetryInterval` (`h / retryDivisor`) is `0` and `getRetentions` divides by it, a panic
(`issues/etcd-compaction-retention-duration.md`). -/
abbrev v3compactor.newPeriodic.spec : Prop :=
  ∀ (lg : Loc) (clk : GoInterface) (h interval : w64) (rg c : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor ∗ context.isClosedchanInit ∗ ⌜10 ≤ sint.Z h ∨ sint.Z h ≤ -10⌝ }}
    (App (App (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor.newPeriodic)) (Val #lg)) (Val #clk)) (Val #h))
      (Val #interval)) (Val #rg)) (Val #c))
  {{ (pc : Loc), RET #pc; isPeriodic pc ⟨lg, clk, h, interval, rg, c⟩ ∗ pdRevs pc [] ∗ pdReader pc }}

end spec

end EtcdGrove
end Perennial
