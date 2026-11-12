/-
`(*EtcdServer).restoreAlarms()` (`server.go`: `v3alarm.NewAlarmStore` over the server's backend,
stored in `s.alarmStore`). Lean-first (no Rocq counterpart); the server-construction unit, stage
N0 (2026-10-16, D13: `notes/decisions.md`), for `NewServer`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvBoot

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- `s.restoreAlarms()` over the real backend `d` (`s.be`), its alarm bucket in the table
(`d.P.has`) and empty in a part of any bucket set `S` containing it, with a pooled reader's resource
and the caller's thread token: the alarm store `NewAlarmStore` made (its lock, `isAlarmStore`, and
the apply contract at the backend's batch lock `Pk` and any frozen hook, as
`v3alarm.NewAlarmStore.spec` gives; unit N4, 2026-10-17: at any batch-lock invariant and hook until
then, false; D22 receiver epochs, S7c: on whichever backend the store's user's half `alarmBeOn`
names) in `s.alarmStore`, no error, the part **idle**. (2026-11-02, the backend-auth-split stage:
until then also an error arm, the field unchanged, which `NewAlarmStore` never takes, and the
writer's half `rbOwn`.) -/
abbrev EtcdServer.restoreAlarms.spec : Prop :=
  ∀ (s lg : Loc) (d : mvcc.KBReal) (W Pk : IProp GF) (qo : Qp) (a0 : Loc) (dq : DFrac)
    (S : GoString → Prop) (r : GMap GoString backend.BktData),
  S go!"alarm" → d.P.has mvcc.alarmBI →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      srvLgAddr s ↦□ lg ∗ ⌜lg ≠ null⌝ ∗
      srvBeAddr s ↦{dq} (interface.mkOk
        (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.backend.ty) #d.be :
          GoInterface) ∗
      backend.isBackend d.γB d.P W Pk d.be ∗ backend.bOpen d.γB qo ∗ backend.wbTok d.γB ∗
      backend.bkRPool d.γB d.P d.be ∗ threadTok ∗
      backend.rbPart d.γB S r ∗ ⌜(r.lookup go!"alarm").getD ∅ = ∅⌝ ∗ srvAlarmStoreAddr s ↦ a0 }}
    (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"restoreAlarms")) (Val #()))
  {{ (err : GoInterface), RET #err; ⌜err = GoInterface.nil⌝ ∗ backend.bOpen d.γB qo ∗
      backend.bkRPool d.γB d.P d.be ∗ threadTok ∗
      backend.rbOwnIn d.γB S (r.insert go!"alarm" ∅) ∗
      srvBeAddr s ↦{dq} (interface.mkOk
        (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.backend.ty) #d.be :
          GoInterface) ∗
      ∃ a : Loc, ⌜a ≠ null⌝ ∗ srvAlarmStoreAddr s ↦ a ∗
        isAlarmStore a ∗ alarmEmpty a d.be ∗ alarmApplyOk a }}

end spec

end EtcdGrove
end Perennial
