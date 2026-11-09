/-
`(*EtcdServer).ApplyWaitCommit()` (`server.go:629-631`): `s.applyWait.Wait(s.getCommittedIndex())`.

**Users**: none of the request path's specs; cited by `waitAppliedIndex`'s sketch.

**Proof sketch**: `getCommittedIndex` (an atomic load: any value), then `timeList.Wait.spec` as in
`ApplyWait`.

**Changes**: verify round (A7-provability F7): new.

**Margin**: the index waited for is not tied to the committed log.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.ApiApply
public import Spec.go_etcd_io.etcd.pkg.v3.wait.Api

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

/-- **`ApplyWaitCommit()`** (`server.go:629-631`): `ApplyWait` at the committed index it loads
(any value: the ready handler's atomic). Users: v3rpc's maintenance `Status`'s callers in etcd's
tests only (no snippet). Verify round (A7-provability F7: cited by `waitAppliedIndex`'s sketch). -/
def EtcdServer.ApplyWaitCommit.spec : Prop :=
  ∀ (s : Loc) (γ : Names) (id : Nat),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      srvNode s γ id ∗ srvStarted s γ id }}
    (App (Val (s @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.EtcdServer.ty @!!
      go!"ApplyWaitCommit")) (Val #()))
  {{ (ch : Loc), RET #ch; ∃ d : w64, Wait.timeChan ch (fun d' => srvApplied s γ (uint.nat d')) d }}

end spec
end EtcdServer
end EtcdGrove
end Perennial
