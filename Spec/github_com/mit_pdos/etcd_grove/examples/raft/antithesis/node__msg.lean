/-
Lean-first (no Rocq counterpart). #33 parity B1, specs first (`notes/antithesis-parity-design.md` §3;
the vocabulary is `HarnessRun.lean`'s).
`(*node).msg(m)`: `msgOf(m, m.To, Nodes)`.
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
variable [AntStor GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Assumptions]
variable [check_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Assumptions]

/-- See the file header. -/
abbrev node.msg.spec : Prop :=
  ∀ (c : Loc) (γ : AntNames) (n : Loc) (j : Fin γ.R.N) (ml : Loc) (dq dqe : DFrac) (cap : Bool) (st : MsgSt), st.msg.Type' ≠ MsgSnap → AllNormal st.ents →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis ∗
      antCluster c γ ∗ nodeRO c γ n j ∗ msgPtsC ml dq dqe cap st }}
    (App (Val (n @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.antithesis.node.ty @!! go!"msg")) (Val #ml))
  {{ (g : AntCheck.G.Msg), RET #g; msgPtsC ml dq dqe cap st ∗ AntCheck.msgRO g (msgOfSt st st.msg.To') ∗
      ⧗ st.ents.length }}

end spec

end AntHarness
end EtcdGrove
end Perennial
