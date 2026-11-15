/-
Lean-first (no Rocq counterpart).

`kubernetes.Client.Get` at the latest revision (`opts.Revision' = 0`), as the store's unary paths
call it (`GetOptions{}`): `Client.Get.spec` (restated at any revision by k8s 7e-1, the Draft's §3.1)
with the revision read the state's own (`KVState.readRev_zero`), its error's future-revision
soundness dropped (a read at the latest revision has none). The statement is the one
`Client.Get.spec` had before 7e-1, so the store's callers are unchanged.
-/
module

public import Spec.go_etcd_io.etcd.client.v3.kubernetes.Client__Get

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kubernetes

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

/-- A range at revision `0` reads the current revision. -/
theorem KVState.readRev_zero (σ : KVState) : σ.readRev (W64 0) = σ.rev := by
  simp [KVState.readRev]

theorem modAtRev_zero [GooseExts] (key : GoString) (σ : KVState) :
    modAtRev key σ (W64 0) = modAt key σ := by
  unfold modAtRev modAt
  rw [KVState.readRev_zero]
  rfl

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.kubernetes.Assumptions]

/-- **`Client.Get` at the latest revision** (see the file header). -/
theorem Client.Get.latest (h : Client.Get.spec (GF := GF) (hG := hG))
    [go_etcd_io.etcd.cache.v3.Assumptions] [go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
    (kc : go_etcd_io.etcd.client.v3.kubernetes.Client)
    (ms : List (client.SrvAt GF)) (V : client.WEnv GF) (ci : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) (key : GoString)
    (opts : go_etcd_io.etcd.client.v3.kubernetes.GetOptions) (Q : w64 → w64 → KVState → IProp GF)
    (hrev : opts.Revision' = W64 0) (hk : key.length ≤ opKeyMax) :
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.kubernetes ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗
      isNewClient kc.Client' (ms.map client.SrvAt.addr) V ∗
      ([∗list] x ∈ ms, client.kvRegsAt x) ∗ ctxOk ci cd ∗ ctxErrClient ci cd ∗
      (∀ R m, |==> □ [∧list] x ∈ ms, ⌜Q R m = fun _ => iprop(True)⌝ ∨ kvReadAu x.γr.kv (Q R m)) }}
    (App (App (App (Val (kc @!! go_etcd_io.etcd.client.v3.kubernetes.Client.ty @!! go!"Get"))
      (Val #(GoInterface.ok ci))) (Val #key)) (Val #opts))
  {{ (resp : go_etcd_io.etcd.client.v3.kubernetes.GetResponse) (err : GoInterface),
      RET (PairV #resp #err);
      (⌜err = GoInterface.nil⌝ ∗ ∃ σ : KVState, □ Q (W64 (σ.rev : Int)) (modAt key σ) σ ∗
        ⌜resp.Revision' = W64 (σ.rev : Int) ∧ kvRevFits σ.rev ∧
          ∀ v ∈ σ.kvs, v.value.length ≤ etcdKeyMax⌝ ∗
        kvOut resp.KV' (mvcc.findKey key σ.kvs)) ∨
      ⌜err ≠ GoInterface.nil⌝ ∗ ⌜clientErr err⌝ ∗ go_etcd_io.etcd.cache.v3.statusErrOk err ∗
        go_etcd_io.etcd.cache.v3.errCellOk err }} := by
  have h0 : 0 ≤ sint.Z opts.Revision' := by rw [hrev]; decide
  iintro %Φ Hpre HΦ
  iapply (h kc ms V ci cd key opts Q h0 hk) $$ [Hpre]
  · iexact Hpre
  inext
  iintro %resp %err Hout
  iapply HΦ
  icases Hout with (⟨%Herr, %σ, #HQ, %Hσ, #Hkv⟩ | ⟨%Herr, %Hce, #Hse, #Hcl, -⟩)
  · ileft
    isplitl []
    · ipureintro; exact Herr
    iexists σ
    have e1 : modAtRev key σ opts.Revision' = modAt key σ := by rw [hrev]; exact modAtRev_zero key σ
    have e2 : (σ.at (σ.readRev opts.Revision')).kvs = σ.kvs := by
      rw [hrev, KVState.readRev_zero]; rfl
    rw [e1, e2] at *
    obtain ⟨h1, -, h3, h4⟩ := Hσ
    iframe HQ Hkv
    ipureintro; exact ⟨h1, h3, h4⟩
  · iright
    iframe Hse Hcl
    ipureintro; exact ⟨Herr, Hce⟩

end proof

end kubernetes
end EtcdGrove
end Perennial
