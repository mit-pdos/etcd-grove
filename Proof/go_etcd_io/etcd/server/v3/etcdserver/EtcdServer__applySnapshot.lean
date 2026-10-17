/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__applySnapshot.lean`. Lean-first (no Rocq
counterpart); the request path's unit 4b (2026-10-13).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__applySnapshot
public import Spec.go_etcd_io.raft.v3.IsEmptySnap
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__setAppliedIndex
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__setTerm

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem EtcdServer.applySnapshot.wp_proof
    (hIES : IsEmptySnap.spec (GF := GF) (hG := hG))
    (_hSAI : EtcdServer.setAppliedIndex.spec (GF := GF) (hG := hG))
    (_hST : EtcdServer.setTerm.spec (GF := GF) (hG := hG)) :
    EtcdServer.applySnapshot.spec (GF := GF) (hG := hG) := by
  intro s ep ap
  wp_start as #Hsn
  ihave #Hrpkg : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 $$ []
  · iPkgInit
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_apply (wp_IsEmptySnap_nil hIES) $$ [$Hrpkg]
  (try wp_auto)
  iapply HΦ
  itrivial

/-- **The leader snapshot's publication** (etcd-io/etcd#22529, 2026-10-17; not part of the linked
results: the snapshot path of `applySnapshot` is outside its spec, see the file
`notes/pr-verify/etcd-22529.md`). The PR's `s.setAppliedIndex(ep.appliedi)`, after the snapshot
moved `ep.appliedi` from the applied index `ai` to the snapshot's index `si > ai` (the Go code panics
otherwise) and restored the KV to the log `Ls` of the committed raft log through `si` (mvcc's
certificate `idxCert`, extending the log `L₀` applied through `ai`): it publishes `si` as the
applied index, with `Ls` as its log, and leaves the apply thread's half at `si`, the index `ep.appliedi`
now holds (what `srvApplyRes` and the next `applyEntries` take). The old code, which skipped
the store, left the half at `ai` while `ep.appliedi = si`. -/
theorem EtcdServer.applySnapshot.publish_ok
    (hSAI : EtcdServer.setAppliedIndex.spec (GF := GF) (hG := hG))
    (s : Loc) (E : apply.AEnv GF) (γr : ReadNames) (ai si : w64) (L₀ Ls : mvcc.Log)
    (hlt : uint.Z ai < uint.Z si) (hp : L₀ <+: Ls) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        srvAppliedInv s E γr ∗ srvAppliedOwn γr ai ∗ appliedLogAt γr ai L₀ ∗ kvLogAt γr si Ls ∗
        mvcc.idxCert E.γ.idx Ls }}
      (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"setAppliedIndex")) (Val #si))
    {{ RET #(); srvAppliedOwn γr si ∗ appliedAtLeast γr si ∗ appliedLogAt γr si Ls }} := by
  wp_start_folded as ⟨#Hinv, Hown, #HL₀, #HkA, #Hc⟩
  imod applied_predeposit_gt s E γr ai si L₀ Ls hlt hp $$ Hinv Hown HL₀ HkA with Hpre
  wp_apply (hSAI s E γr ai si Ls) $$ [Hpre] as ⟨Hao, #Hlb, #Hlog⟩
  · iframe #; iframe Hpre
  iapply HΦ
  iframe Hao Hlb Hlog

end proof

end EtcdGrove
end Perennial
