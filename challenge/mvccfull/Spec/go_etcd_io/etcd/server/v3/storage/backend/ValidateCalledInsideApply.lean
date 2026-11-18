/-
`ValidateCalledInsideApply` (`verify.go`): the trust boundary (`verify.go` is names-only: it reads `ETCD_VERIFY`
and the call stack). Go: it returns if the lock checks are off (`ETCD_VERIFY` neither `all` nor
`lock`); with them on, it checks that it is called inside the apply loop (`.applyEntries` on the stack) and otherwise calls `lg.Panic`.
Stated as returning: this assumes the lock checks are off, as in production (a deployment
assumption: a run with `ETCD_VERIFY=lock` may stop where this says it returns).
Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.backend.Base
public import Proof.go_etcd_io.etcd.client.pkg.v3.verify.Env

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.backend

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- `ValidateCalledInsideApply(lg)` returns (the lock checks off).
(Sweep repairs 1, B4, 2026-11-07: with `ETCD_VERIFY` off, `envVerifyOff`, from program start; until
then assumed unconditionally, false of a run with `ETCD_VERIFY=all`, `lock` or `assert`: Go
`examples/sweeprepairs/b1`, `TestB4On`.) -/
abbrev backend.ValidateCalledInsideApply.spec : Prop :=
  ∀ (lg : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
      -- (sweep repairs 1, B4) `ETCD_VERIFY` off for the run (`envVerifyOff`)
      envVerifyOff }}
    (App (Val (@! ValidateCalledInsideApply)) (Val #lg))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
