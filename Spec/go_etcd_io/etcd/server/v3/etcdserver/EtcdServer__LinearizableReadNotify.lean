/-
`(*EtcdServer).LinearizableReadNotify(ctx)` (`interface.go:46-48`): `s.read.LinearizableReadNotify(ctx)`.

**Users**: the corruption checker's hasher (`corrupt.go:187`), the version monitor
(`version/version.go:42,72`, from `monitorClusterVersions`), `ensureLeadership`, `MemberList`, the
snippet `etcdserverreq/read.go` `ReqReadAfterWrite`.

**Proof sketch**: the read-only field `s.read` (`srvStarted`: 2c's `Read.readAt s.read γ.raft
(srvApplied s γ)`, which `start` made from `readNew_init` with `readEnv` proved from the server's
method specs); `Read.LinearizableReadNotify.spec`.

**Changes**: verify round (A7-provability F4, completeness F3): new here (the old tree's
`EtcdServer__LinearizableReadNotify.lean`), stated at the history: a `nil` return gives a committed
log extending the caller's lower bound `l0` that the member has applied.

**Margin**: none.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.ApiApply

set_option autoImplicit false
set_option linter.iris.dupNamespace false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace EtcdServer

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions]

/-- **A linearizable read barrier**: `nil` once the member has applied a committed log extending
`l0` (committed when the call began), or a read path error (indefinite). -/
def EtcdServer.LinearizableReadNotify.spec : Prop :=
  ∀ (s : Loc) (γ : Names) (id : Nat) (ctx : GoInterface) (l0 : List Raft.LogEntry),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      srvNode s γ id ∗ srvStarted s γ id ∗ Context.ctxOk ctx ∗ Raft.committedLb γ.raft l0 ∗
      threadTok }}
    (App (Val (s @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.EtcdServer.ty @!!
      go!"LinearizableReadNotify")) (Val #ctx))
  {{ (err : GoInterface), RET #err; threadTok ∗
      ((⌜err = GoInterface.nil⌝ ∗ ∃ l : List Raft.LogEntry, Raft.committedLb γ.raft l ∗
          srvApplied s γ l.length ∗ ⌜Raft.opsOf l0 <+: Raft.opsOf l⌝) ∨
       Read.readErr err) }}

end spec
end EtcdServer
end EtcdGrove
end Perennial
