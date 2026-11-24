/- Lean-first (no Rocq counterpart).

`c.conf()` (`examples/raft/kvnet/kvcheck/kvcheck.go`): asks a random replica for its status
(`ReqStatus`, no payload); if it answers and the answer decodes (`kvnet.GetStatus`, any bytes), stores
the status's configuration as `lastConf` and returns it, else returns nil. Either way the result is a
nil or read-only conf state (`csOpt … DFrac.discard`, what `randomChange` takes).
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
abbrev checker.conf.spec : Prop :=
  ∀ (F : KvFacts GF) (c : Loc) (γ : CheckerCnt GF) (ls : List GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.kvcheck ∗
      isCheckerP F c γ ls }}
    (App (Val (c @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.kvnet.kvcheck.checker.ty
      @!! go!"conf")) (Val #()))
  {{ (p : Loc), RET #p; ∃ cs : ConfStateM, csOpt p DFrac.discard cs }}

end spec

end raft_kvcheck
end EtcdGrove
end Perennial
