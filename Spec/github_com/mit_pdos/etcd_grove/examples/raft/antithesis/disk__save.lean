/-
Lean-first (no Rocq counterpart). #33 parity B1, specs first (`notes/antithesis-parity-design.md` §3;
the vocabulary is `HarnessRun.lean`'s).
`(*disk).save(hs, ents)`: the hard state if any, and the entries replacing the log from the first
one's index on (`saveW`); a write that does not continue the log panics (`SaveOk`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.HarnessRun

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
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Assumptions]
variable [check_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Assumptions]

/-- See the file header. -/
abbrev disk.save.spec : Prop :=
  ∀ (d : Loc) (w : AntSim.DurW) (hp : Loc) (oh : Option HardStateM) (sl : GoSlice) (els : List Loc)
    (es : List EntryM), SaveOk w es →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis ∗
      diskOwn d w ∗ hsOptRO hp oh ∗ sl ↦*□ els ∗ [∗list] p;e ∈ els;es, entRO p e }}
    (App (App (Val (d @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.antithesis.disk.ty @!! go!"save")) (Val #hp)) (Val #sl))
  {{ RET #(); diskOwn d (saveW w oh es) }}

end spec

end AntHarness
end EtcdGrove
end Perennial
