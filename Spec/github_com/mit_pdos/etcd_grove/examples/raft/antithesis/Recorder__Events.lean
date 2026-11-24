/-
Lean-first (no Rocq counterpart). #33 S4, specs first (`notes/antithesis-s4-design.md` §2).

`(*Recorder).Events()`: under the lock, a copy of the stream. From the final stream (`recDone`,
which agrees with the lock's half), a fresh slice holding it.
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
abbrev Recorder.Events.spec : Prop :=
  ∀ (γr : GName) (r : Loc) (evs : List AntCheck.Event),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis ∗ isRecorder γr r ∗ recDone γr evs }}
    (App (Val (r @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Recorder.ty @!! go!"Events")) (Val #()))
  {{ (sl : GoSlice), RET #sl; AntCheck.eventsRO sl evs ∗ recDone γr evs }}

end spec

end AntHarness
end EtcdGrove
end Perennial
