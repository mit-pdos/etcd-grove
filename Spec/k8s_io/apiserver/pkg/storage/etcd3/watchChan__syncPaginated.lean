/-
`(*watchChan).syncPaginated()` (`k8s.io/apiserver/pkg/storage/etcd3/watcher.go:325-380`): the watch's
initial events, the key-values in scope at one revision, read page by page (`KV.Get` with
`WithLimit(defaultWatcherMaxLimit)` and the scope's range when recursive, the pages after the first at
the first page's revision), each queued on `incomingEventChan` as `parseKV`'s raw event; `initialRev`
set to the first page's revision. Stated (k8s 7f-5a-P step 5) for a watch with initial events, with the
producer's state (`kProdSt`, nothing queued yet) and the caller's read updates from `lbf`, at least the
requested revision: the first page's linearizable read fires `Q lbf` at `σ0`, the start point is
`σ0.rev` (`kStartOk`), and the producer has queued (or, the context done, dropped) the initial raw
events at it (`kInitRaws`); or an error the watcher's error paths accept (`kErrOk`: the client's, after
`interpretListError`, or its own `fmt.Errorf`). Lean-first (no Rocq counterpart).
-/
module

public import Proof.k8s_io.apiserver.pkg.storage.etcd3.WatchProd

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
abbrev watchChan.syncPaginated.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions] [go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
    (Obj : Type) [DecidableEq Obj] [Pos.Countable Obj] (wc sp : Loc) (c : StoreCfg GF Obj)
    (W : WatchSpec GF Obj) (γk : KVNames) (γ : KWatchNames) (cd : context.ContextDesc (IProp GF))
    (sel : Obj → Bool) (emp : Bool) (inS : GoString → Bool) (m : KWatchMode)
    (Q : Nat → KVState → IProp GF) (procd alive : GName) (ctx : GoInterfaceOk) (kp : GoString)
    (recur : Bool) (r0 : w64) (lbf : Nat) (q : Qp),
  (∀ lb σ, Q lb σ ⊢ ⌜lb ≤ σ.rev ∧ kvWf c σ ∧ kvWfHist c σ ∧ kvKeysShort σ⌝) →
  (∀ lb lb' σ σ', Q lb σ ∗ Q lb' σ' ⊢ ⌜kvSameHist σ σ'⌝) →
  c.K.live →
  m.forceInit = true → m.req ≤ lbf →
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.etcd3 ∗ levelTok 0 ∗ (isStore sp c ∗
      storeWatchOk sp c W γk ∗ kWcProd wc sp c W γ cd sel emp inS m Q procd alive ctx kp recur ∗
      structFieldRef k8s_io.apiserver.pkg.storage.etcd3.watchChan go!"initialRev" wc ↦ r0 ∗
      readAus c γk (Q lbf) ∗ (□ ∀ lb σ, □ Q lb σ -∗ |==> readAus c γk (Q σ.rev)) ∗
      kProdSt γ cd [] ∗ dghostVar γ.prodEx (DFrac.own q) false) }}
    (App (Val (wc @!! go.GoType.PointerType k8s_io.apiserver.pkg.storage.etcd3.watchChan.ty @!!
      go!"syncPaginated")) (Val #()))
  {{ (err : GoInterface), RET #err; levelTok 0 ∗ (dghostVar γ.prodEx (DFrac.own q) false ∗
      ((⌜err = GoInterface.nil⌝ ∗ ∃ (lb0 : Nat) (σ0 : KVState), □ Q lb0 σ0 ∗
          ⌜kStartOk m σ0 σ0.rev ∧ kvRevFits σ0.rev⌝ ∗
          structFieldRef k8s_io.apiserver.pkg.storage.etcd3.watchChan go!"initialRev" wc ↦
            W64 (σ0.rev : Int) ∗
          kProdSt γ cd (kInitRaws inS σ0 σ0.rev)) ∨
       (kErrOk err ∗ ∃ r : w64,
          structFieldRef k8s_io.apiserver.pkg.storage.etcd3.watchChan go!"initialRev" wc ↦ r))) }}

end spec

end k8s
end EtcdGrove
end Perennial
