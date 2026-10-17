/-
`v3compactor.AutoPeriodic.shouldCompact` (`autoperiodic.go`, etcd#22095: the projection decision).
Lean-first (no Rocq counterpart); see `Proof/go_etcd_io/etcd/server/v3/etcdserver/api/v3compactor/Defs.lean`.
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

/-- `ac.shouldCompact(size, rate)` is `projected >= highWater` with
`highWater = AutoPeriodicHighWater * float64(ac.maxBytes)` and
`projected = float64(size) + rate * AutoPeriodicLeadTime.Seconds()`, in Go's float64 arithmetic
(Perennial's opaque `FloatOps`; `secs` is what `Seconds()` returns, opaque too). -/
abbrev v3compactor.AutoPeriodic.shouldCompact.spec : Prop :=
  ∀ (ac : Loc) (P : APParams) (tv : APTuning) (size rate : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor ∗ isAutoPeriodic ac P ∗ apTuning tv }}
    (App (App (Val (ac @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor.AutoPeriodic.ty @!! go!"shouldCompact")) (Val #size)) (Val #rate))
  {{ (b : Bool), RET #b; ⌜∃ secs : w64, b = float64Leb (float64Mul tv.hw (int64ToFloat64 P.maxBytes))
      (float64Add (int64ToFloat64 size) (float64Mul rate secs))⌝ }}

end spec

end EtcdGrove
end Perennial
