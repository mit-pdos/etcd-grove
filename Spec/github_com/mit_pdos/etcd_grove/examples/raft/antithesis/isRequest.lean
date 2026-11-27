/-
Lean-first (no Rocq counterpart). #33 parity B2, statements (round 1: nothing proves `isRequest.spec` yet;
`notes/antithesis-parity-design.md` §3.5, §4; the vocabulary is `HarnessDur.lean`'s).
`isRequest(m)`: an append request or a heartbeat (`parallel` sends those before the write).
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
abbrev isRequest.spec : Prop :=
  ∀ (ml : Loc) (dq dqe : DFrac) (cap : Bool) (st : MsgSt),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis ∗ msgPtsC ml dq dqe cap st }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.raft.antithesis.isRequest)) (Val #ml))
  {{ RET #(isRequestTy st.msg.Type'); msgPtsC ml dq dqe cap st }}

end spec

end AntHarness
end EtcdGrove
end Perennial
