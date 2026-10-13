/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__DeleteRange.lean`.
Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__DeleteRange
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__raftRequest
public import Spec.go_etcd_io.etcd.api.v3.etcdserverpb.DeleteRangeRequest__GetKey
public import Spec.go_etcd_io.etcd.api.v3.etcdserverpb.DeleteRangeRequest__GetRangeEnd
public import Spec.go_etcd_io.etcd.pkg.v3.traceutil.Tracer__Start
public import Spec.go_opentelemetry_io.otel.trace.WithAttributes
public import Spec.go_opentelemetry_io.otel.«attribute».String
public import Spec.context.WithValue
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.ProposerLemmas
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.WrapLemmas

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem EtcdServer.DeleteRange.wp_proof
    (hRR : EtcdServer.raftRequest.spec (GF := GF) (hG := hG))
    (hGK : DeleteRangeRequest.GetKey.spec (GF := GF) (hG := hG))
    (hGE : DeleteRangeRequest.GetRangeEnd.spec (GF := GF) (hG := hG))
    (hTS : traceutil.Tracer.Start.spec (GF := GF) (hG := hG))
    (hWA : trace.WithAttributes.spec (GF := GF) (hG := hG))
    (hAS : «attribute».String.spec (GF := GF) (hG := hG))
  :
    EtcdServer.DeleteRange.spec (GF := GF) (hG := hG) := by
  intro s E ρ ctx cd r op
  wp_start as ⟨#Hsrv, Hrd, Hcred, #Hctx, #Hdel⟩
  wp_apply wp_with_defer as %defer defer
  ihave Hinit : (srvInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hinit with ⟨-, ⟨-, -, -, ⟨%tr, #Htr⟩, -⟩, -⟩
  ihave #Hdel' := Hdel
  iunfold txn.deleteRangeRequestIs at Hdel'
  icases Hdel' with ⟨%Hrn, %ksl, %esl, %k, %e, %pk, #HK, #Hk, #HE, #He, -⟩
  (try wp_auto)
  wp_apply hGK r ksl $$ []
  · iframe #; ipureintro; exact Hrn
  (try wp_auto)
  wp_apply wp_bytes_to_string $$ [Hk] as -
  · iexact Hk
  (try wp_auto)
  wp_apply hAS as %kv -
  (try wp_auto)
  wp_apply hGE r esl $$ []
  · iframe #; ipureintro; exact Hrn
  (try wp_auto)
  wp_apply wp_bytes_to_string $$ [He] as -
  · iexact He
  (try wp_auto)
  wp_apply hAS as %kv2 -
  (try wp_auto)
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %asl ⟨-, -⟩
  (try wp_auto)
  wp_apply hWA as %opt -
  (try wp_auto)
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %osl ⟨-, -⟩
  (try wp_auto)
  wp_apply hTS tr ctx cd _ _ $$ [] as %ctx1 %sp ⟨⟨%vs1, #Hctx1t, Hctx1w⟩, #Hsp⟩
  · iframe #; iunfold mvcc.txnCtx; iright; iexact Hctx
  ihave #Hctx1 := Hctx1w $$ Hctx
  iunfold trace.isSpan at Hsp
  icases Hsp with ⟨%si, %Hsi, #HEnd, -, -⟩
  subst Hsi
  (try wp_auto)
  ihave ⟨Hirr, %Hirrn⟩ := typedPointsto_not_null_dup _ _ _ $$ «$a1»
  iStructNamed Hirr
  ipersist ID
  ipersist Range
  ipersist Put
  ipersist DeleteRange
  ipersist Txn
  ipersist Compaction
  ipersist LeaseGrant
  ipersist LeaseRevoke
  ipersist Alarm
  ipersist LeaseCheckpoint
  ipersist AuthEnable
  ipersist AuthDisable
  ipersist AuthStatus
  ipersist Authenticate
  ipersist AuthUserAdd
  ipersist AuthUserDelete
  ipersist AuthUserGet
  ipersist AuthUserChangePassword
  ipersist AuthUserGrantRole
  ipersist AuthUserRevokeRole
  ipersist AuthUserList
  ipersist AuthRoleList
  ipersist AuthRoleAdd
  ipersist AuthRoleDelete
  ipersist AuthRoleGet
  ipersist AuthRoleGrantPermission
  ipersist AuthRoleRevokePermission
  ipersist ClusterVersionSet
  ipersist ClusterMemberAttrSet
  ipersist DowngradeInfoSet
  ipersist DowngradeVersionTest
  ihave #HirrNo : irrNoHdrIs «$a1_ptr» (irrDeleteRange op) $$ []
  · iunfold irrNoHdrIs
    simp only [irrDeleteRange, apply.irrEmpty, apply.optReqIs, apply.presentIs, apply.irrField]
    isplitr
    · ipureintro; exact Hirrn
    isplitr
    · have h0 : (W64 0 : w64) = 0 := by decide
      rw [h0]; iexact ID
    repeat (isplitr; · iexists _; iframe #; try (ipureintro; simp))
    iexists _; iframe #; try (ipureintro; simp)
  (try wp_auto)
  wp_apply hRR s E ρ ctx1 _ «$a1_ptr» (irrDeleteRange op) rfl $$ [Hrd Hcred Header] as %resp %err ⟨Hrd, Hres⟩
  · iframe # Hrd Hcred
    iexists _; iexact Header
  (try wp_auto)
  icases Hres with (⟨%Herr, %hm, %rq', %Hwire, Hok⟩ | ⟨%Hre, #HaE, Hfail⟩)
  · subst Herr
    iunfold appliedOk at Hok
    icases Hok with ⟨%x, %x', %o, %skip, %Hstep, Hans, #Hcert⟩
    have Hk : apply.dispatchKind rq' = .deleteRange := by
      rw [Hwire.2.2.1]; simp [apply.dispatchKind, apply.withHeader, irrDeleteRange, apply.irrEmpty]
    iunfold apply.dispatchAnswer at Hans
    rw [Hk] at *
    icases Hans with ⟨%op', %pr, %Hop, Hpo⟩
    obtain ⟨Hop', Hresp⟩ := Hop
    subst Hresp
    ihave %Hap := apply.deleteAnswerIs_nil _ _ _ _ $$ Hpo
    obtain ⟨log', rfl⟩ := Hap
    simp only [apply.deleteAnswerIs]
    icases Hpo with ⟨Hpo, Hhdr⟩
    (try wp_auto)
    wp_apply HEnd
    (try wp_auto)
    iapply HΦ
    iframe Hrd
    ileft
    isplitr
    · ipureintro; rfl
    iexists hm, rq', op', x, x', .applied log' false, skip
    iframe Hpo Hhdr Hcert
    ipureintro
    refine ⟨Hwire, Hop', ?_, Hstep, log', rfl⟩
    intro Hnz
    have Hrq : rq' = apply.withHeader (irrDeleteRange op) hm := by
      refine (Hwire.2.2.2 ?_)
      simpa [irrNoZeroEnd, apply.withHeader, irrDeleteRange, apply.irrEmpty] using Hnz
    subst Hrq
    simp [apply.withHeader, irrDeleteRange] at Hop'
    exact Hop'.symm
  · obtain ⟨rfl, Hne⟩ := Hre
    (try wp_auto)
    rcases err with ei | _
    · (try wp_auto)
      wp_apply HEnd
      (try wp_auto)
      iapply HΦ
      iframe Hrd
      iright
      isplitr
      · ipureintro; exact ⟨rfl, Hne⟩
      iframe HaE Hfail
    · exact absurd rfl Hne

end proof

end EtcdGrove
end Perennial
