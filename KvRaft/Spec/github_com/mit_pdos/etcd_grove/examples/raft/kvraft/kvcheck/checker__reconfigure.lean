/- Lean-first (no Rocq counterpart).

`c.reconfigure(stop)` (`examples/raft/kvraft/kvcheck/kvcheck.go`): until `stop` is closed (a broadcast
channel, `sleep`'s), asks a random replica to propose a random configuration change (`ReqConf`,
`kvraft.PutConfChange`'s payload of `randomChange(conf())`); its answers are not looked at. The protocol's
fact of a change request (`F.confOk`) must hold of every payload: at the top level it is `True` (the store's
conf policy decides at the commit, `ConfDefs.lean`).
-/
module

public import KvRaft.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.kvcheck.Client

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace raft_kvcheck

open Iris Iris.BI Net kvraft go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [NetProtoGS]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvraft.kvcheck.Assumptions]
variable [field_sem : net.FieldAssumptions]

/-- See the file header. -/
abbrev checker.reconfigure.spec : Prop :=
  ∀ (F : KvFacts GF) (c : Loc) (γ : CheckerCnt GF) (ls : List GoString) (stop : Loc) (γc : ChanNames),
  (∀ pl, F.confOk pl) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.kvcheck ∗
      isCheckerP F c γ ls ∗ ownBroadcastChan stop γc iprop(True) .Unknown }}
    (App (Val (c @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.kvraft.kvcheck.checker.ty
      @!! go!"reconfigure")) (Val #stop))
  {{ RET #(); True }}

end spec

end raft_kvcheck
end EtcdGrove
end Perennial
