/-
Proof of `Spec/go_etcd_io/etcd/client/v3/concurrency/Mutex__IsOwner.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.concurrency.Mutex__IsOwner
public import Spec.go_etcd_io.etcd.client.v3.CreateRevision
public import Spec.go_etcd_io.etcd.client.v3.Compare

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace concurrency

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.client.v3.concurrency

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.concurrency.Assumptions]

theorem Mutex.IsOwner.wp_proof (hCR : CreateRevision.spec (GF := GF) (hG := hG))
    (hCmp : Compare.spec (GF := GF) (hG := hG)) :
    Mutex.IsOwner.spec (GF := GF) (hG := hG) := by
  intro m st
  wp_start as Hst
  unfold mutexState
  icases Hst with ⟨Hk, Hr, Hh⟩
  wp_auto
  wp_apply hCR st.key as %c #Hc
  (try wp_auto)
  wp_apply hCmp c (cmpKeyM .create st.key) (go!"=") .eq _ (.num st.rev) $$ [$Hc] as %c' #Hc'
  · ipureintro
    refine ⟨by decide, st.rev, Or.inl rfl, rfl⟩
  iapply HΦ
  iframe
  iexact Hc'

end proof

end concurrency
end EtcdGrove
end Perennial
