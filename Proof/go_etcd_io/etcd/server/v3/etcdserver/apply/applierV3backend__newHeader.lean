/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart). (Strict M1, 2026-11-05: the
KV's `Rev()` by `KV.Rev.contract` at the KV's type, from `shapes.law`, at the writer's read update,
`envAus`.)
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.applierV3backend__newHeader
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.ApiLemmas

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.apply go_etcd_io.etcd.api.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions]

theorem apply.applierV3backend.newHeader.wp_proof
    (hsh : mvcc.api.shapes.law (GF := GF) (hG := hG)) :
    apply.applierV3backend.newHeader.spec (GF := GF) (hG := hG) := by
  intro E p log c
  -- ours' proof (`KV.Rev.contract` at `envAus`'s read update) with `lean`'s stronger post (2.11a:
  -- `hdrFields`, the `Revision` the log's last, `E.Nx log` in place of `certOk`, from `envAus`'s
  -- writer facts)
  wp_start as ⟨#Hb, Htt, Hsw⟩
  iunfold apply.applyTok at Htt
  icases Htt with ⟨Htt, Hmr⟩
  iunfold apply.backendIs at Hb
  icases Hb with ⟨%opts, #Hopts, #Hok⟩
  iunfold apply.backendOptsOk at Hok
  icases Hok with ⟨%Hlg, #Hkv, -, #Haus, -, -, -, #Hcl, #Hrs, -⟩
  iStructNamed Hopts
  iunfold apply.isCluster at Hcl
  icases Hcl with ⟨%Hcn, -, #HID, -⟩
  iunfold apply.isRaftStatus at Hrs
  icases Hrs with ⟨%ri, %Hri, #HMem, #HLead, #HTerm⟩
  iunfold apply.isApplyKV at Hkv
  icases Hkv with #Hkv
  icases txn.isMvcc_shape hsh opts.KV' E.γ $$ Hkv with ⟨%Hsh, -⟩
  obtain ⟨kty, kvv, Hkveq, -, -, hRevC, -⟩ := Hsh
  ihave Hkv' : □ mvcc.api.isMvcc (interface.mkOk kty kvv) E.γ $$ []
  · rw [← Hkveq]; imodintro; iexact Hkv
  icases Hkv' with #Hkv'
  iunfold apply.envAus at Haus
  icases Haus with ⟨-, #HauR, -, -, #Hfacts, -⟩
  ihave Hau := HauR $$ %log %c %(srvApi.wSt E.γs log c) Hsw []
  · iintro Hsw; iexact Hsw
  iunfold srvApi.auRead at Hau
  ihave #Hmi : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc $$ []
  · iPkgInit
  wp_auto
  wp_apply HID as %cid -
  rw [Hri]
  wp_auto
  wp_apply HMem as %mid -
  rw [Hkveq]
  simp only [interface.mkOk]
  wp_apply (hRevC E.γ _) $$ [$Hkv' $Htt $Hmr $Hau] as %v ⟨Htt, Hmr, %σ, ⟨%Hσ, Hsw⟩, %Hv⟩
  -- the writer's facts: its log's witness, reachable (so at least `NewStore`'s two revisions)
  imod Hfacts $$ %log %c Hsw with ⟨Hsw, Hnx, -, %Hreach⟩
  have Hlen2 : 2 ≤ log.length := txn.reach_len (srvApi.stAt log c) Hreach.1
  wp_apply HTerm as %tm -
  wp_apply HLead as %ld -
  irename «$r0» => Hh
  generalize «$r0_ptr» = h at *
  ihave %Hhn := typedPointsto_not_null $$ Hh
  iStructNamed Hh
  iapply HΦ
  iunfold apply.applyTok
  iframe Htt Hmr Hsw Hnx
  isplitr
  · ipureintro; exact Hhn
  isplitl [ClusterId MemberId RaftTerm LeaderId]
  · iunfold apply.hdrFields
    iexists _, _, _, _
    iframe
  -- `v` is the read state's revision, `log.length - 1` at `σ = stAt log c`
  subst Hσ
  have hrv : ((srvApi.stAt log c).rev : Int) = (log.length : Int) - 1 := by
    simp only [srvApi.stAt, mvcc.api.MvccState.rev]; omega
  rw [← hrv, ← Hv]
  iframe Revision
  ipureintro; exact ⟨Hlen2, Hreach.2⟩

end proof

end EtcdGrove
end Perennial
