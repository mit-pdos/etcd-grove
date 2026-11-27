/-
Lean-first (no Rocq counterpart). #33 parity B1, specs first (`notes/antithesis-parity-design.md` §3;
the vocabulary is `HarnessBase.lean`'s).
`firstIndex(ents)`: the first entry's index, `0` for none (`firstIdx`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.HarnessBase

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
abbrev firstIndex.spec : Prop :=
  ∀ (sl : GoSlice) (dq : DFrac) (els : List Loc) (es : List EntryM),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis ∗
      sl ↦*{dq} els ∗ [∗list] p;e ∈ els;es, entRO p e }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.raft.antithesis.firstIndex)) (Val #sl))
  {{ RET #(firstIdx es); sl ↦*{dq} els ∗ [∗list] p;e ∈ els;es, entRO p e }}

end spec

end AntHarness
end EtcdGrove
end Perennial
