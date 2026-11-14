/- Lean-first (no Rocq counterpart).

`toRaft(e)` (`examples/etcd/wal/wal.go`): a fresh `*raftpb.Entry` (`Index`, `Term`, `Type` set,
`EntryNormal`; `Data` the non-nil `entData(e)`), as the raftpb instance's entry (`walRaftP.entIn`:
frozen at its canonical content, below Go's allocation limit) of `e`'s model (`absEnt`). `e.size`
positive (an empty `Data` is a non-nil empty slice, not the canonical `nil`) and below `2^40` (the
allocation limit; the tester's sizes are at most 140000, `tEntWf`).
-/
module

public import LinuxFs.Proof.github_com.mit_pdos.etcd_grove.examples.etcd.wal.Rep
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.RaftModel.Pb

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
abbrev toRaft.spec : Prop :=
  ∀ (e : TEnt), 0 < uint.nat e.size' → uint.nat e.size' < 2 ^ 40 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.wal }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.wal.toRaft)) (Val #e))
  {{ (l : Loc), RET #l; (walRaftP (GF := GF)).entIn l (absEnt e) }}

end spec

end etcd_wal
end EtcdGrove
end Perennial
