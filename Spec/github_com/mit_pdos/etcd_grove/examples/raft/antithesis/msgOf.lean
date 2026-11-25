/-
Lean-first (no Rocq counterpart). #33 parity B1, specs first (`notes/antithesis-parity-design.md` §3;
the vocabulary is `HarnessBase.lean`'s).
`msgOf(m, to, n)` of a message holding `st` (read through its getters, given back), not a
`MsgSnap` (batch B3's), its entries normal: `msgOfSt st to`, with a receipt per entry.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.HarnessBase

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
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Assumptions]
variable [check_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Assumptions]

/-- See the file header. -/
abbrev msgOf.spec : Prop :=
  ∀ (ml : Loc) (dq dqe : DFrac) (cap : Bool) (st : MsgSt) (to nn : w64), st.msg.Type' ≠ MsgSnap → AllNormal st.ents →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis ∗
      msgPtsC ml dq dqe cap st }}
    (App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.raft.antithesis.msgOf)) (Val #ml)) (Val #to)) (Val #nn))
  {{ (g : AntCheck.G.Msg), RET #g; msgPtsC ml dq dqe cap st ∗ AntCheck.msgRO g (msgOfSt st to) ∗
      ⧗ st.ents.length }}

end spec

end AntHarness
end EtcdGrove
end Perennial
