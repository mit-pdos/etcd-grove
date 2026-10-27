/-
`v2stats.NewLeaderStats(lg, id)`: names-only. Lean-first (no Rocq counterpart); the server-construction unit, stage N0 (2026-10-16, D13:
`notes/decisions.md`), for `NewServer`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v2stats.Defs

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

/-- `NewLeaderStats(lg, id)` returns some `*LeaderStats`, not nil (a fresh allocation, `&LeaderStats{…}`;
the non-nil result since unit N4, 2026-10-17: the transport's `AddPeer` dereferences it), with its
mutex (`v2stats.isLeaderStats`) and its followers' map (`v2stats.lsFollowers`, owned; D43 M5a,
2026-10-26: the transport's `AddPeer` and `removePeer` write it). -/
abbrev v2stats.NewLeaderStats.spec : Prop :=
  ∀ (lg : Loc) (id : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v2stats }}
    (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.api.v2stats.NewLeaderStats))
      (Val #lg)) (Val #id))
  {{ (p : Loc), RET #p; ⌜p ≠ null⌝ ∗ v2stats.isLeaderStats p ∗ v2stats.lsFollowers p 1 }}

end spec

end EtcdGrove
end Perennial
