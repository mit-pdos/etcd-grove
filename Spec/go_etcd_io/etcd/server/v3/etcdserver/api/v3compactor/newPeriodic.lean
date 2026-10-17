/-
`v3compactor.newPeriodic`: the trust boundary (names only: the periodic compactor's constructor, which
etcd#22095 does not change). Lean-first (no Rocq counterpart).
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

/-- `newPeriodic(lg, clock, retention, rg, c)` returns some `*Periodic` (what it does is not
stated: `New`'s spec says nothing of the periodic compactor), for a retention of at least 10 ns
in absolute value: below that, `getRetryInterval` (`period / retryDivisor`) is `0` and
`getRetentions` divides by it, a panic (`issues/etcd-compaction-retention-duration.md`; found by
the review of etcd#22095's verification). -/
abbrev v3compactor.newPeriodic.spec : Prop :=
  ∀ (lg : Loc) (clk : GoInterface) (retention : w64) (rg c : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor ∗
      ⌜10 ≤ sint.Z retention ∨ sint.Z retention ≤ -10⌝ }}
    (App (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor.newPeriodic)) (Val #lg)) (Val #clk)) (Val #retention))
      (Val #rg)) (Val #c))
  {{ (p : Loc), RET #p; True }}

end spec

end EtcdGrove
end Perennial
