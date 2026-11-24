/-
Lean-first (no Rocq counterpart). #33 S4, specs first (`notes/antithesis-s4-design.md` §2).

`(*Cluster).Events()`: the recorder's stream (`c.rec.Events()`). From the run's end (`runOver`), a
slice holding the final stream, which the checker accepts at `cfg3`, within the Go `int`'s budget
(`Stream.Bounded`) and the configuration changes' (`Stream.ConfBounded`, which `check.Run` also
takes; the approved shape had only the first two).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.HarnessDefs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace AntHarness

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Assumptions]
variable [check_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Assumptions]

/-- See the file header. -/
abbrev Cluster.Events.spec : Prop :=
  ∀ (c : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis ∗ runOver c }}
    (App (Val (c @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Cluster.ty @!! go!"Events")) (Val #()))
  {{ (sl : GoSlice), RET #sl; ∃ evs : List AntCheck.Event, AntCheck.eventsRO sl evs ∗
      ⌜AntCheck.Accepts AntSim.cfg3 evs ∧ AntCheck.Stream.Bounded evs ∧
        AntCheck.Stream.ConfBounded AntSim.cfg3 evs⌝ }}

end spec

end AntHarness
end EtcdGrove
end Perennial
