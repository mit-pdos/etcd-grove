/- Lean-first (no Rocq counterpart).

`fromRaft(re)` (`examples/etcd/wal/wal.go`): of a raftpb instance's entry of model `m` (`walRaftP.entIn`,
as `ReadAll` returns them), the entry `tFromRaft m` (`FromRaft.lean`); no panic.
-/
module

public import WalTester.Proof.github_com.mit_pdos.etcd_grove.examples.etcd.wal.Rep
public import WalTester.Proof.github_com.mit_pdos.etcd_grove.examples.etcd.wal.FromRaft
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
abbrev fromRaft.spec : Prop :=
  ∀ (re : Loc) (m : EntryM),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.wal ∗
      (walRaftP (GF := GF)).entIn re m }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.wal.fromRaft)) (Val #re))
  {{ RET #(tFromRaft m); True }}

end spec

end etcd_wal
end EtcdGrove
end Perennial
