/-
`v2stats.NewServerStats(name, id)` (`server.go`): names-only. Lean-first (no Rocq counterpart); the server-construction unit, stage N0 (2026-10-16, D13:
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
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- `NewServerStats(name, id)` returns some `*ServerStats`, not nil (a fresh allocation,
`&ServerStats{…}`; the non-nil result since unit N4, 2026-10-17: the transport uses it). -/
abbrev v2stats.NewServerStats.spec : Prop :=
  ∀ (name id : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v2stats }}
    (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.api.v2stats.NewServerStats))
      (Val #name)) (Val #id))
  {{ (p : Loc), RET #p; ⌜p ≠ null⌝ }}

end spec

end EtcdGrove
end Perennial
