/- Lean-first (no Rocq counterpart).

`toHS(h)` (`examples/etcd/wal/wal.go`): a fresh `*raftpb.HardState` with its three cells set, as the
raftpb instance's hard state (`walRaftP.hsIn`, frozen: `Save` reads it) of `h`'s model (`absHs`).
-/
module

public import WalTester.Proof.github_com.mit_pdos.etcd_grove.examples.etcd.wal.Rep
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.RaftModel.Pb

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_wal

open Iris Iris.BI github_com.mit_pdos.etcd_grove.examples.etcd.wal

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.wal.Assumptions]

/-- See the file header. -/
abbrev toHS.spec : Prop :=
  ∀ (h : THs),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.wal }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.wal.toHS)) (Val #h))
  {{ (p : Loc), RET #p; (walRaftP (GF := GF)).hsIn p (absHs h) }}

end spec

end etcd_wal
end EtcdGrove
end Perennial
