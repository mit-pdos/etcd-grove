/- Lean-first (no Rocq counterpart).

# `raft/antithesis`: the top-level robustness result, proved

`raft_antithesis_robust_msgs.spec`, stated in
`Spec/github_com/mit_pdos/etcd_grove/examples/raft/antithesis/TopLevelRobustness.lean`, from
`antithesis_adequate_of` (`Adequacy.lean`) and the linked `Main` (`Link.lean`'s `AntHarness.wp_Main`,
at a storage model `Main.spec` does not mention: `memStorageModel`).

**Interim (parity B1, in progress).** The driver's proof of `node.drain` is not finished: its
spec is a hypothesis of the Link's results reaching it (`h_antithesis_node__drain`,
`etc/link-lean-first-antithesis.txt`'s `?` line), and so of this theorem, at every ghost state,
semantics, package assumptions, storage model and storage registry. It goes when the proof lands
(its `?` line replaced by its callees), and then the theorem is the statement's, with no hypothesis.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.TopLevelRobustness
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Adequacy
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Link
public import Proof.go_etcd_io.raft.v3.MemstorageInstance

@[expose] public section

noncomputable section

set_option pp.fullNames true

set_option linter.unusedSectionVars false

namespace Perennial

namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section closed

attribute [local instance] trivialExts trivialExtsSemantics trivialExtsInterp trivialExts_hasExt

variable [go_gctx : GoGlobalContext]

/-- A driver function's spec at `antGF`, at every ghost state, semantics, package assumptions,
storage model and storage registry: the form of the Link's pending hypotheses here. -/
abbrev antPending (spec : ∀ [hG : HeapGS HasLC.hasLC antGF] [go.Semantics]
    [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Assumptions] [StorageModel antGF]
    [AntHarness.AntStor antGF], Prop) : Prop :=
  ∀ [hG : HeapGS HasLC.hasLC antGF] [go.Semantics]
    [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Assumptions] [StorageModel antGF]
    [AntHarness.AntStor antGF], spec

/-- `raft_antithesis_robust_msgs.spec`
(`Spec/github_com/mit_pdos/etcd_grove/examples/raft/antithesis/TopLevelRobustness.lean`), over the
spec of the driver function not proved yet (see the file header). -/
theorem raft_antithesis_robust_msgs
    (h_drain : antPending (AntHarness.node.drain.spec (GF := antGF))) :
    raft_antithesis_robust_msgs.spec := by
  intro lctx sem package_sem hLog σ g
  have wp_Main : antMainSpec := by
    intro hG _ _
    letI : MemStorReg antGF := ⟨default⟩
    letI : StorageModel antGF := memStorageModel
    intro _
    exact AntHarness.wp_Main (GF := antGF) (hG := hG) h_drain
  exact
    Robustness.Robust.of_single_below fun hf n κs t2 σ2 hn Hsteps =>
      (antithesis_adequate_of wp_Main σ g hf.1 hf.2.1 hf.2.2 n hn κs t2 σ2 Hsteps).2

end closed
end EtcdGrove
end Perennial

end
