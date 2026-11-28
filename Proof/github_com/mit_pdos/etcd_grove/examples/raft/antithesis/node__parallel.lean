/-
Lean-first (no Rocq counterpart). #33 parity B2, driver group E: the proof of
`Spec/github_com/mit_pdos/etcd_grove/examples/raft/antithesis/node__parallel.lean`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.node__parallel
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.b2i
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.withByRole
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.DrainB2ParWriteWp
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.DrainB2Quiet
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.DrainB2Holds
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.DrainB2Loop
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.DrainB1Ext
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.ParallelLaws
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Sim.MemView

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace AntHarness

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section pure
variable [GooseExts]

/-- `RsView` reads only the view's disk, delivered and unreported committed entries, raft state and
pre-vote flag. -/
theorem rsView_congr {rs : RNState} {v v' : AntSim.NodeView} (h : RsView rs v)
    (hd : v'.dur = v.dur) (hdl : v'.delivered = v.delivered) (hce : v'.ce = v.ce) (hr : v'.r = v.r)
    (hpre : v'.pre = v.pre) : RsView rs v' := by
  unfold RsView AntSim.roleS AntSim.NodeView.ps at *
  rw [hd, hdl, hce, hr, hpre]; exact h

/-- B1's `RsView` is `RsViewB2`'s. -/
theorem rsViewB2_of {md : H.Mode} {rs : RNState} {v : AntSim.NodeView} (h : RsView rs v) :
    RsViewB2 md rs v := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  exact ⟨h3, h4, h6, h7, fun _ => ⟨h1, h2, h5, h8⟩⟩

/-- `ViewNormal` reads only the view's full log and cause. -/
theorem viewNormal_congr {v v' : AntSim.NodeView} (h : ViewNormal v) (hr : v'.r.full = v.r.full)
    (hc : v'.cause = v.cause) : ViewNormal v' := by
  unfold ViewNormal at *
  rw [hr, hc]; exact h

end pure

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [AntStor GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Assumptions]
variable [check_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Assumptions]

end proof

end AntHarness
end EtcdGrove
end Perennial
