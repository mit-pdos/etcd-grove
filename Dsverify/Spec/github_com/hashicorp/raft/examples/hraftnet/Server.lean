/-
`hraftnet.Server`'s spec (the hraft kit's server machine, `server.go`; notes/dsv-hraft.md, S5d).
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.ServerShare
public import Dsverify.Proof.github_com.hashicorp.raft.Threads.QTok

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Net

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.examples.hraftnet.Assumptions]
variable [π : NetProtoGS] [rsem : github_com.hashicorp.raft.Assumptions]

open github_com.hashicorp.raft.examples.hraftnet

/-- `Server(j)`, `1 ≤ j ≤ 6`: server machine `j` (its share of the deployment, `srvShare K j`, and a
thread token): waits for the drawn first configuration, takes its package of the drawn protocol, runs
raft (bootstrapped with servers `1..n0` if `j ≤ n0`) with the register as its FSM, serves its
transport's receiver and its API, then sleeps forever. -/
abbrev github_com.hashicorp.raft.examples.hraftnet.Server.spec : Prop :=
  ThreadBoundLe GF (2 ^ 28) →
  ∀ (K : HK GF) (j : Nat), 1 ≤ j → j ≤ 6 →
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft.examples.hraftnet ∗
        srvShare K j ∗ srvBoot ∗ ⌜receiptBound GF ≤ 2 ^ 64 ∧ threadBound GF ≤ 2 ^ 31⌝ ∗ threadTok }}
      (App (Val (@! Server)) (Val #(W64 (j : Int))))
    {{ RET #(); True }}

end spec

end Perennial
