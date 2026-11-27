/-
`(*watchChan).sync()` (`k8s.io/apiserver/pkg/storage/etcd3/watcher.go:309-323`): with the
`EtcdRangeStream` feature off (`rangeStreamOff`, the Draft's premise), `syncPaginated()`. Stated as
`syncPaginated`'s spec with that premise (k8s 7f-5a-P step 5). Lean-first (no Rocq counterpart).
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
abbrev watchChan.sync.spec : Prop :=
  ∀ [go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
    (Obj : Type) [DecidableEq Obj] [Pos.Countable Obj] (wc sp : Loc) (c : StoreCfg GF Obj)
    (W : WatchSpec GF Obj) (γk : KVNames) (γ : KWatchNames) (cd : context.ContextDesc (IProp GF))
    (sel : Obj → Bool) (emp : Bool) (inS : GoString → Bool) (m : KWatchMode)
    (Q : Nat → KVState → IProp GF) (procd alive : GName) (ctx : GoInterfaceOk) (kp : GoString)
    (recur : Bool) (r0 : w64) (lbf : Nat) (q : Qp),
  (∀ lb σ, Q lb σ ⊢ ⌜lb ≤ σ.rev ∧ kvWf c σ ∧ kvWfHist c σ ∧ kvKeysShort σ⌝) →
  (∀ lb lb' σ σ', Q lb σ ∗ Q lb' σ' ⊢ ⌜kvSameHist σ σ'⌝) →
  (∀ x ∈ c.ms, noRefusalAt x.addr) →
  m.forceInit = true → m.req ≤ lbf →
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.etcd3 ∗ levelTok 0 ∗ (rangeStreamOff ∗
      isStore sp c ∗
      storeWatchOk sp c W γk ∗ kWcProd wc sp c W γ cd sel emp inS m Q procd alive ctx kp recur ∗
      structFieldRef k8s_io.apiserver.pkg.storage.etcd3.watchChan go!"initialRev" wc ↦ r0 ∗
      readAus c γk (Q lbf) ∗ (□ ∀ lb σ, □ Q lb σ -∗ |==> readAus c γk (Q σ.rev)) ∗
      kProdSt γ cd [] ∗ dghostVar γ.prodEx (DFrac.own q) false) }}
    (App (Val (wc @!! go.GoType.PointerType k8s_io.apiserver.pkg.storage.etcd3.watchChan.ty @!!
      go!"sync")) (Val #()))
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
