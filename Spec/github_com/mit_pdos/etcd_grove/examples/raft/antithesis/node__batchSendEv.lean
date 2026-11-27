/-
Lean-first (no Rocq counterpart). #33 parity B2, statements (round 1: nothing proves `node.batchSendEv.spec` yet;
`notes/antithesis-parity-design.md` §3.5, §4; the vocabulary is `HarnessDur.lean`'s).
`(*node).batchSendEv(by, m)`: `sendEv`'s report with `b`.
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
abbrev node.batchSendEv.spec : Prop :=
  ∀ (c : Loc) (γ : AntNamesB2) (n : Loc) (j : Fin γ.R.N) (by_ : GoString) (ml : Loc) (dq dqe : DFrac)
    (cap : Bool) (st : MsgSt), st.msg.Type' ≠ MsgSnap → AllNormal st.ents →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis ∗
      antClusterB2 c γ ∗ nodeROB2 c γ n j ∗ msgPtsC ml dq dqe cap st }}
    (App (App (Val (n @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.antithesis.node.ty @!! go!"batchSendEv")) (Val #by_)) (Val #ml))
  {{ (p : Loc), RET #p; msgPtsC ml dq dqe cap st ∗ eventOwn p (batchSendEvM by_ st) ∗ ⧗ st.ents.length }}

end spec

end AntHarness
end EtcdGrove
end Perennial
