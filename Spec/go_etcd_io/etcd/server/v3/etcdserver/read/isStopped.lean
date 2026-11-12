/-
`read.isStopped(err)` (read.go). Lean-first (no Rocq counterpart); the request path's unit 4a, see
`Proof/go_etcd_io/etcd/server/v3/etcdserver/read/Inv.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.read.Inv

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver.read

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.read.Assumptions]

/-- `isStopped(err)` of an error `errors.Is` can take (`applyErrIs`): whether it is raft's or the
server's `ErrStopped`: if `false`, it is not raft's (`errors.Is(err, target)` is true when `err`
is `target`; k8s etcd3 7c-2 part 2, S3b; until then the result was not specified). -/
abbrev read.isStopped.spec : Prop :=
  ∀ (err : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.read ∗
      applyErrIs err }}
    (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.read.isStopped)) (Val #err))
  {{ (b : Bool), RET #b;
      ∀ e : GoInterface, ⌜b = false⌝ -∗ globalAddr go_etcd_io.raft.v3.ErrStopped ↦□ e -∗
        ⌜err ≠ e⌝ }}

end spec

end EtcdGrove
end Perennial
