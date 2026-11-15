/-
`parseEvent(e)` (`k8s.io/apiserver/pkg/storage/etcd3/event.go:66-84`) of a delivered watch event
`e` (non-nil, with a non-nil `Kv`: etcd's events always are, `mvcc.evRd`) that is the state's event
`ev` (`eventIs`) with its `PrevKv` pointer read at the state `σ`
(`prevKvOk`): a fresh `*event`, owned, holding `ev` (`kEvIs`'s `.ev` case: its previous value the
key's record before, for an event that is not a create), or, only for a non-create event without
`PrevKv` (Q5, `issues/etcd-watch-prevkv-before-created.md`), an error `fmt.Errorf` made. Proved
(k8s 7f-5a-P step 3). Lean-first (no Rocq counterpart).
-/
module

public import Proof.k8s_io.apiserver.pkg.storage.etcd3.WatchDefs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.api.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : k8s_io.apiserver.pkg.storage.etcd3.Assumptions]

/-- See the file header. -/
abbrev parseEvent.spec : Prop :=
  ∀ (p : Loc) (e : EvModel) (ev : mvcc.EvM) (o : OpFull) (σ : KVState),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.etcd3 ∗
      ⌜p ≠ null ∧ e.kv ≠ null⌝ ∗ EtcdGrove.eventAt p e ∗ eventIs e ev ∗
      structFieldRef mvccpb.Event go!"PrevKv" p ↦□ e.prevKv ∗ prevKvOk o σ ev e.prevKv }}
    (App (Val (@! k8s_io.apiserver.pkg.storage.etcd3.parseEvent)) (Val #p))
  {{ (q : Loc) (err : GoInterface), RET (PairV #q #err);
      (⌜err = GoInterface.nil⌝ ∗ ∃ x : k8s_io.apiserver.pkg.storage.etcd3.event, q ↦ x ∗
        kEvIs σ x (KRaw.ev ev)) ∨
      (⌜err ≠ GoInterface.nil ∧ e.prevKv = null ∧ ¬ v3rpc.evIsCreate ev⌝ ∗ kFmtErr err) }}

end spec

end k8s
end EtcdGrove
end Perennial
