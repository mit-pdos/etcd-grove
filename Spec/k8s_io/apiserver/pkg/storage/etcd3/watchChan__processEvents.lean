/-
`(*watchChan).processEvents(wg)` (`k8s.io/apiserver/pkg/storage/etcd3/watcher.go:546-553`): by the
`ConcurrentWatchObjectDecode` gate (any value: `Enabled` of a queried feature returns some `b`), the
concurrent branch (`concurrentProcessEvents`) or `wg.Add(1); go serialProcessEvents(wg)`; either way at most
two top-level slots of `run`'s wait group, whose `Done`s pass the alive fraction to `run`'s `Wait`
(k8s 7f-5b, `notes/k8s-7f5b-draft.md` §4). Lean-first (no Rocq counterpart).
-/
module

public import Proof.k8s_io.apiserver.pkg.storage.etcd3.WatchCons

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : k8s_io.apiserver.pkg.storage.etcd3.Assumptions]

/-- See the file header. -/
abbrev watchChan.processEvents.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions] [go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
    (Obj : Type) [DecidableEq Obj] [Pos.Countable Obj] (wc sp : Loc) (c : StoreCfg GF Obj)
    (W : WatchSpec GF Obj) (γk : KVNames) (γ : KWatchNames) (cd : context.ContextDesc (IProp GF))
    (sel : Obj → Bool) (emp : Bool) (inS : GoString → Bool) (m : KWatchMode)
    (Q : Nat → KVState → IProp GF) (procd alive : GName) (ctx : GoInterfaceOk) (kp : GoString)
    (recur : Bool) (q : Qp) (wg : Loc) (n : Nat) (P : IProp GF),
  (∀ lb σ, Q lb σ ⊢ ⌜kvWfHist c σ ∧ kvWritesDec c σ ∧ kvRevFits σ.rev⌝) →
  (∀ lb lb' σ σ', Q lb σ ∗ Q lb' σ' ⊢ ⌜kvSameHist σ σ'⌝) →
  n + 2 ≤ 3 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.etcd3 ∗
      kWcCons wc sp c W γk γ cd sel emp inS m Q procd alive ctx kp recur ∗
      kProcSt γ procd alive q ∗ rwg.rwgAdder rwgN 3 wg n P }}
    (App (Val (wc @!! go.GoType.PointerType k8s_io.apiserver.pkg.storage.etcd3.watchChan.ty @!!
      go!"processEvents")) (Val #wg))
  {{ RET #(); ∃ n' : Nat, rwg.rwgAdder rwgN 3 wg n' iprop(P ∗ kResAlive alive q) }}

end spec

end k8s
end EtcdGrove
end Perennial
