/- Lean-first (no Rocq counterpart).

`c.disrupt(stop)` (`examples/raft/kvnet/kvcheck/kvcheck.go`): until `stop` is closed (a broadcast channel,
`sleep`'s), asks a random replica to transfer leadership, campaign or forget the leader (`ReqDisrupt`,
`kvnet.EncodeDisrupt`'s payload, the request's fact `reqOk_disrupt`); its answers are not looked at.
-/
module

public import KvNet.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.kvcheck.Client

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace raft_kvcheck

open Iris Iris.BI Net raft_kvnet go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [NetProtoGS]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvnet.kvcheck.Assumptions]

/-- See the file header. -/
abbrev checker.disrupt.spec : Prop :=
  ∀ (F : KvFacts GF) (c : Loc) (γ : CheckerCnt GF) (ls : List GoString) (stop : Loc) (γc : ChanNames),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.kvcheck ∗
      isCheckerP F c γ ls ∗ ownBroadcastChan stop γc iprop(True) .Unknown }}
    (App (Val (c @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.kvnet.kvcheck.checker.ty
      @!! go!"disrupt")) (Val #stop))
  {{ RET #(); True }}

end spec

end raft_kvcheck
end EtcdGrove
end Perennial
