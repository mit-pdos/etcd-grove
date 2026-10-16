/-
`v2stats.NewLeaderStats(lg, id)`: names-only. Lean-first (no Rocq counterpart); the server-construction unit, stage N0 (2026-10-16, D13:
`notes/decisions.md`), for `NewServer`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvServer

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- `NewLeaderStats(lg, id)` returns some `*LeaderStats` (a fresh allocation). -/
abbrev v2stats.NewLeaderStats.spec : Prop :=
  ∀ (lg : Loc) (id : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v2stats }}
    (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.api.v2stats.NewLeaderStats))
      (Val #lg)) (Val #id))
  {{ (p : Loc), RET #p; True }}

end spec

end EtcdGrove
end Perennial
