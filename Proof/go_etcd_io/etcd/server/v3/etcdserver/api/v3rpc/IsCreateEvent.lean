/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.IsCreateEvent

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.api
  go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- A key-value points-to as its revisions' fields. -/
theorem v3rpc.kv_revs (l : Loc) (v : mvccpb.KeyValue) (dq : DFrac) :
    (l ↦{dq} v : IProp GF) ⊢
      l.[mvccpb.KeyValue, go!"CreateRevision"] ↦{dq} v.CreateRevision' ∗
        l.[mvccpb.KeyValue, go!"ModRevision"] ↦{dq} v.ModRevision' := by
  iintro H
  icases typedPointsto_split _ _ _ $$ H with H
  simp only [TypedPointsto.typedPointstoDef]
  iNamed H
  iframe CreateRevision ModRevision

theorem v3rpc.IsCreateEvent.wp_proof : v3rpc.IsCreateEvent.spec (GF := GF) (hG := hG) := by
  intro e ev
  wp_start as #Hev
  iunfold mvcc.evIs at Hev
  icases Hev with ⟨%p, %q, %st, %uf, %sc, %Hn, #He, #Hkv, -⟩
  iunfold mvcc.kvPtrFixed at Hkv
  icases Hkv with ⟨%ks, %vs, %st', %uf', %sc', -, -, #Hp⟩
  icases mvcc.event_fields _ _ _ $$ He with ⟨#HT, #HK, -⟩
  icases v3rpc.kv_revs _ _ _ $$ Hp with ⟨#HC, #HM⟩
  wp_auto
  unfold mvcc.evType
  cases hd : ev.del
  · simp only [Bool.false_eq_true, ↓reduceIte, decide_true]
    wp_auto
    iapply HΦ
    ipureintro
    simp
  · simp only [↓reduceIte, show decide (W32 1 = W32 0) = false from by decide]
    wp_auto
    iapply HΦ
    ipureintro
    simp

end proof

end EtcdGrove
end Perennial
