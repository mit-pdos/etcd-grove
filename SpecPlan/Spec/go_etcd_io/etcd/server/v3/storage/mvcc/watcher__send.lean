/-
`(*watcher).send(wr)` (internal): the events filtered by the watcher's filters; nothing sent (`true`)
when filtering dropped them all; else a non-blocking send on the watcher's channel: `false` when
full.

**Proof sketch.** Each filter (`filterOk`) on each event; `verify.Verify` (off outside tests; its
check holds: the fork's fix of `issues/etcd-watch-resume-below-start-revision.md`); a `select` with a
`default` on `w.ch` (the stream's channel; `wsSendable` gives the facts its protocol requires of
the filtered response; a send moves the response's events to the channel).
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.storage.mvcc.WatchInternal
public import SpecPlan.Spec.go_uber_org.zap.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Mvcc

open Iris Iris.BI EtcdModel EtcdWire go_etcd_io.etcd.server.v3.storage.mvcc Classical

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

def watcher.send.spec : Prop :=
  ∀ (w : Loc) (ι : WsNames) (id : w64) (W : WatcherM) (rc : WRec) (wr : WatchResponse) (r : WResp),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗ watcherAt w ι id W ∗ wRecAt w rc ∗ ⌜rc.ch = wsChanOf ι⌝ ∗ wrespAt wr r ∗
      wsSendable w r }}
    (App (Val (w @!! go.GoType.PointerType watcher.ty @!! go!"send")) (Val #wr))
  {{ (b : Bool), RET #b; wRecAt w rc ∗ (if b then True else wrespAt wr r ∗ wsSendable w r) }}

end spec

end Mvcc
end EtcdGrove
end Perennial
