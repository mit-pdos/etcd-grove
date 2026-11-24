/-
Lean-first (no Rocq counterpart). #33 S4, specs first (`notes/antithesis-s4-design.md` §2).

`entriesOf(es)` of normal entries (`AllNormal`): a fresh `[]check.Entry` of `entOfE` of each.
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
variable [raft_sem : go_etcd_io.raft.v3.Assumptions]

/-- See the file header. -/
abbrev entriesOf.spec : Prop :=
  ∀ (sl : GoSlice) (dq : DFrac) (els : List Loc) (es : List EntryM), AllNormal es →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis ∗ sl ↦*{dq} els ∗ [∗list] p;e ∈ els;es, entRO p e }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.raft.antithesis.entriesOf)) (Val #sl))
  {{ (out : GoSlice), RET #out; sl ↦*{dq} els ∗ AntCheck.logRO out (es.map entOfE) }}

end spec

end AntHarness
end EtcdGrove
end Perennial
