/-
`newCorruptionChecker(lg, s, storage)` (`corrupt.go`): names-only. Lean-first (no Rocq counterpart); the server-construction unit, stage N0 (2026-10-16, D13:
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
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- `newCorruptionChecker(lg, s, storage)` returns some `*corruptionChecker` (a fresh
allocation). -/
abbrev newCorruptionChecker.spec : Prop :=
  ∀ (lg s : Loc) (h : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver }}
    (App (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.newCorruptionChecker)) (Val #lg))
      (Val #s)) (Val #h))
  {{ (c : Loc), RET #c; True }}

end spec

end EtcdGrove
end Perennial
