/-
`realClock.NewTimer(d)` (`cache/clock.go`). Lean-first (no Rocq counterpart); see `InvCache.lean`.
-/
module

public import Proof.go_etcd_io.etcd.cache.v3.InvCache

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.cache.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

/-- `rc.NewTimer(d)`: a `Timer` (`isTimer`): a `*realTimer` wrapping `time.NewTimer(d)`. So the
real clock is a `Clock` (`isClock`, `isClock_realClock`). -/
abbrev realClock.NewTimer.spec : Prop :=
  ∀ (rc : realClock) (d : time.Duration),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 }}
    (App (Val (rc @!! realClock.ty @!! go!"NewTimer")) (Val #d))
  {{ (t : GoInterfaceOk), RET #(GoInterface.ok t); isTimer t }}

end spec

end EtcdGrove
end Perennial
