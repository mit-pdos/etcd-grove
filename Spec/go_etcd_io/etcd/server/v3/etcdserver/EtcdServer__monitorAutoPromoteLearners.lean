/-
`(*EtcdServer).monitorAutoPromoteLearners()` (`server.go`, PR `etcd-io/etcd#21744`): the background
monitor goroutine attached by `s.Start()` when `features.AutoPromoteLearners` is enabled.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__tryAutoPromoteLearners
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRead

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- Persistent server and package resources read by `EtcdServer.monitorAutoPromoteLearners`:
`srvAutoPromotePre s lg`, `s.firstCommitInTerm ↦□ fc`, `s.stopping ↦□ stc` (`stopChan stc`),
`s.lead`'s atomic invariant (`srvLeadInv s`), and `monitorVersionInterval ↦□ mvi`. -/
def srvMonitorAutoPromotePre (s lg fc stc : Loc) : IProp GF :=
  iprop(srvAutoPromotePre s lg ∗
    srvFirstCommitAddr s ↦□ fc ∗
    srvStoppingAddr s ↦□ stc ∗ stopChan stc ∗
    srvLeadInv s ∗
    (∃ mvi : _root_.Perennial.time.Duration, globalAddr monitorVersionInterval ↦□ mvi))

instance srvMonitorAutoPromotePre_persistent (s lg fc stc : Loc) :
    Persistent (srvMonitorAutoPromotePre (GF := GF) s lg fc stc) := by
  unfold srvMonitorAutoPromotePre; infer_instance

/-- **`s.monitorAutoPromoteLearners()`**: logs startup at `Info`, then loops selecting on
`s.firstCommitInTerm.Receive()`, `time.After(monitorVersionInterval)`, and `s.stopping`. On
`s.stopping` it logs shutdown at `Info` and returns; on the other two cases it checks `s.isLeader()`
and, when leader, calls `s.tryAutoPromoteLearners()`. Takes and returns a reader slot of `s.lgMu`
(`srvLgReader s`) and a reader slot of `s.firstCommitInTerm` (`notifyReader fc`). -/
abbrev EtcdServer.monitorAutoPromoteLearners.spec : Prop :=
  ∀ (s lg fc stc : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      srvMonitorAutoPromotePre s lg fc stc ∗ srvLgReader s ∗ notifyReader fc }}
    (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"monitorAutoPromoteLearners")) (Val #()))
  {{ RET #(); srvLgReader s ∗ notifyReader fc }}

end defs

end EtcdGrove
end Perennial
