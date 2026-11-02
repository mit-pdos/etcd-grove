/- Lean-first (no Rocq counterpart).

`s.add(c)` (cluster.go): one more on the counter `c`, one of the statistics' (`isStats`), each in an
invariant of its own (2026-11-01, durability stage II: kvreconf's `Stats.add.spec`, at kvdurable's
counters; `persist` and `snapshot` count with it).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.kvdurable.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvdurable

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt durableExt]
variable [go_gctx : GoGlobalContext] [go.IntoValInj GoString]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvdurable.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions] [AllG GF] [KdStor GF]

/-- See the file header. -/
abbrev Stats.add.spec : Prop :=
  ∀ (s c : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.kvdurable ∗
      inv kdStatsN iprop(∃ v : w64, sync.atomic.ownUint64 c (DFrac.own 1) v) }}
    (App (Val (s @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.kvdurable.Stats.ty
      @!! go!"add")) (Val #c))
  {{ RET #(); True }}

end spec

end kvdurable
end EtcdGrove
end Perennial
