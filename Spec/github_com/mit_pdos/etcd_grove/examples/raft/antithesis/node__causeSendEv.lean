/-
Lean-first (no Rocq counterpart). #33 parity B2, statements (round 1: nothing proves `node.causeSendEv.spec` yet;
`notes/antithesis-parity-design.md` §3.5, §4; the vocabulary is `HarnessDur.lean`'s).
`(*node).causeSendEv(by, m, cause)`: `sendEv`'s report with the message its `Ready` answered
(`cause`, the empty list for none).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.HarnessDur

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
abbrev node.causeSendEv.spec : Prop :=
  ∀ (c : Loc) (γ : AntNamesB2) (n : Loc) (j : Fin γ.R.N) (by_ : GoString) (ml cl : Loc) (dq dqe : DFrac)
    (cap : Bool) (st : MsgSt) (o : Option AntCheck.Msg), st.msg.Type' ≠ MsgSnap → AllNormal st.ents →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis ∗
      antClusterB2 c γ ∗ nodeROB2 c γ n j ∗ msgPtsC ml dq dqe cap st ∗ causeRO cl o }}
    (App (App (App (Val (n @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.antithesis.node.ty @!! go!"causeSendEv")) (Val #by_)) (Val #ml)) (Val #cl))
  {{ (p : Loc), RET #p; msgPtsC ml dq dqe cap st ∗ eventOwn p (causeSendEvM by_ st o) ∗ ⧗ st.ents.length }}

end spec

end AntHarness
end EtcdGrove
end Perennial
