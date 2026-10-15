/-
`ValidateCalledOutSideApply` (`verify.go`): the trust boundary (`verify.go` is names-only: it reads `ETCD_VERIFY`
and the call stack). Go: it returns if the lock checks are off (`ETCD_VERIFY` neither `all` nor
`lock`); with them on, it checks that it is called outside the apply loop (no `.applyEntries` on the stack) and otherwise calls `lg.Panic`.
Stated as returning: this assumes the lock checks are off, as in production (a deployment
assumption: a run with `ETCD_VERIFY=lock` may stop where this says it returns).
Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.backend.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.backend

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- `ValidateCalledOutSideApply(lg)` returns (the lock checks off). -/
abbrev backend.ValidateCalledOutSideApply.spec : Prop :=
  ∀ (lg : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend }}
    (App (Val (@! ValidateCalledOutSideApply)) (Val #lg))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
