/- Lean-first (no Rocq counterpart).

# `lib/etcdstart`: the definitions its top-level statement is written in

The program the example's top-level theorem is about, and the other definitions its statement
names, moved here unchanged out of `Adequacy.lean` so that the statement
(`Spec/.../TopLevelRobustness.lean`) imports no proof (CLAUDE.md, "Import tiers").
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.RevokeLevels
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.read.Metrics
public import Proof.runtime.Start
public import Proof.runtime.Threads

@[expose] public section

noncomputable section

section

set_option linter.unusedSectionVars false

namespace Perennial

namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section adequacy

variable [GooseExts] [GooseInterp]

variable [GooseSemantics] [GoGlobalContext]

variable {GF : BundledGFunctors}

/-- **A ghost-state instance at the local context `lctx`** (the examples state their hypotheses
over every instance whose Go local context is the semantics' own). -/
abbrev heapWith (hG : HeapGS .hasLC GF) (lctx : GoLocalContext) : HeapGS .hasLC GF :=
  ⟨hG.goose_globalGS, { hG.goose_localGS with goose_go_local_context := lctx }⟩

end adequacy
end EtcdGrove
end Perennial

end

end
