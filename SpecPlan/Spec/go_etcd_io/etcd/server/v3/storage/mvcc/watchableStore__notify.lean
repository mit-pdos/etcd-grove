/-
`(*watchableStore).notify(rev, evs)` (internal; under `s.mu`, from `watchableStoreTxnWrite.End`): each
synced watcher of an event's key is sent its events of `rev` (filtered), or becomes a victim with
them (out of the synced group); every such watcher's `minRev` set past `rev`.

**Proof sketch.** `newWatcherBatch(&s.synced, evs)` (its spec: one revision per batch, every event's
revision being `rev`: the `lg.Panic` unreachable); for each watcher `w.send` with `Revision: rev`
(`wsSendable` from the lock's contents and the new notified history `h`, whose last revision is
`rev`: a synced watcher's position is below `rev` and none of its events lie between); a failure:
`victim`, `synced.delete`, the batch kept; `minRev = rev + 1`; `addVictim`.
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

def watchableStore.notify.spec : Prop :=
  ∀ (s : Loc) (γ : MvccName) (rev : w64) (evs : GoSlice) (ps : List Loc) (es : List EvM)
    (h : KVHist),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗ wsInv s γ ∗ wsMu s γ ∗ evs ↦*□ ps ∗ ([∗list] p; e ∈ ps; es, evOwn p e) ∗ mvccLb γ h ∗
      ⌜sint.Z rev = h.rev ∧ es = (h.eventsAt h.rev).map (evOf h.rev)⌝ }}
    (App (App (Val (s @!! go.GoType.PointerType watchableStore.ty @!! go!"notify")) (Val #rev)) (Val #evs))
  {{ RET #(); wsMu s γ ∗ [∗list] p; e ∈ ps; es, evOwn p e }}

end spec

end Mvcc
end EtcdGrove
end Perennial
