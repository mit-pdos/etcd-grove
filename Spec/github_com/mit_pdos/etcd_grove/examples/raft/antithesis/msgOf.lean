/-
Lean-first (no Rocq counterpart). #33 S4, specs first (`notes/antithesis-s4-design.md` §2).

`msgOf(m, to)` of a message holding `st` (read through its getters, given back), not a `MsgSnap`
(the harness's scope: no snapshot), its entries normal (`entryOf` panics otherwise): the `check.Msg`
value of `msgOfSt st to`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.HarnessDefs

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
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Assumptions]
variable [check_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions]

/-- See the file header. -/
abbrev msgOf.spec : Prop :=
  ∀ (ml : Loc) (dq dqe : DFrac) (cap : Bool) (st : MsgSt) (to : w64),
  st.msg.Type' ≠ MsgSnap → AllNormal st.ents →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis ∗ msgPtsC ml dq dqe cap st }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.raft.antithesis.msgOf)) (Val #ml)) (Val #to))
  {{ (g : AntCheck.G.Msg), RET #g; msgPtsC ml dq dqe cap st ∗ AntCheck.msgRO g (msgOfSt st to) }}

end spec

end AntHarness
end EtcdGrove
end Perennial
