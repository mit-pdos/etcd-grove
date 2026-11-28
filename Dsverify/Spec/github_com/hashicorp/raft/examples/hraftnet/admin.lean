/-
`hraftnet.admin`'s spec (the hraft kit's orchestrator, notes/dsv-hraft.md, S5g).
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.OrchDefs

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

/-- `admin()`: forever, a random membership change, transfer or snapshot asked of a server, with what
the admin knows (`adminCtx`). It never returns. -/
abbrev github_com.hashicorp.raft.examples.hraftnet.admin.spec : Prop :=
  ∀ (K : HK GF),
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft.examples.hraftnet ∗
        net.rpc.codecSet (hraftCodec (GF := GF)) ∗ adminCtx K ∗ ⌜receiptBound GF ≤ 2 ^ 64⌝ }}
      (App (Val (@! admin)) (Val #()))
    {{ RET #(); False }}

end spec

end Perennial
