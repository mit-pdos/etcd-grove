/-
Lean-first (no Rocq counterpart).

The proof of `(*store).Create`: the prepared key, tracing (no-ops), the object's resource
version cleared and its encoding transformed (the contract), then `OptimisticPut` through the
client with each member's update made from the caller's (`k8sAu1_kvAu1`, `stepOk_create`), and the
answer by the transaction's verdict (`create_out`): the object decoded at the new revision, or
"key exists".
-/
module

public import Spec.k8s_io.apiserver.pkg.storage.etcd3.store__Create
public import Proof.k8s_io.apiserver.pkg.storage.etcd3.Steps
public import Spec.k8s_io.apiserver.pkg.storage.etcd3.store__prepareKey
public import Spec.k8s_io.apiserver.pkg.storage.NewKeyExistsError
public import Spec.k8s_io.apiserver.pkg.storage.NewInternalError
public import Spec.k8s_io.apiserver.pkg.storage.etcd3.getTypeName
public import Spec.k8s_io.apiserver.pkg.storage.etcd3.txnError
public import Spec.k8s_io.apiserver.pkg.storage.etcd3.metrics.RecordEtcdRequest
public import Spec.k8s_io.component_base.tracing.Start
public import Spec.k8s_io.component_base.tracing.Span__AddEvent
public import Spec.k8s_io.component_base.tracing.Span__End
public import Spec.go_opentelemetry_io.otel.attribute.String
public import Spec.go_opentelemetry_io.otel.attribute.Int
public import Spec.k8s_io.apiserver.pkg.audit.GetAuditIDTruncated
public import Spec.k8s_io.apiserver.pkg.storage.etcd3.metrics.OperationLatencyTracker__Record
public import Spec.go_etcd_io.etcd.client.v3.kubernetes.Client__OptimisticPut
public import Perennial.Proof.time.Link

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 16384

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apiserver.pkg.storage.etcd3.Assumptions]

theorem store.Create.wp_proof
    (wp_prepareKey : store.prepareKey.spec (GF := GF) (hG := hG))
    (wp_getTypeName : getTypeName.spec (GF := GF) (hG := hG))
    (wp_txnError : txnError.spec (GF := GF) (hG := hG))
    (wp_NewKeyExistsError : storage.NewKeyExistsError.spec (GF := GF) (hG := hG))
    (wp_NewInternalError : storage.NewInternalError.spec (GF := GF) (hG := hG))
    (wp_Start : tracing.Start.spec (GF := GF) (hG := hG))
    (wp_AddEvent : tracing.Span.AddEvent.spec (GF := GF) (hG := hG))
    (wp_End : tracing.Span.End.spec (GF := GF) (hG := hG))
    (wp_String : «attribute».String.spec (GF := GF) (hG := hG))
    (wp_Int : «attribute».Int.spec (GF := GF) (hG := hG))
    (wp_GetAuditIDTruncated : audit.GetAuditIDTruncated.spec (GF := GF) (hG := hG))
    (wp_RecordEtcdRequest : metrics.RecordEtcdRequest.spec (GF := GF) (hG := hG))
    (wp_kPut : kubernetes.Client.OptimisticPut.spec (GF := GF) (hG := hG)) :
    store.Create.spec (GF := GF) (hG := hG) := by
  intro _ _ Obj _ sp c ci cd key obj o rv out o0 rv0 k Ψ hk hrv
  wp_start as ⟨#Hst, #Hctx, #Hce, Hobj, Hout, Hau⟩
  iunfold isStore at Hst
  icases Hst with ⟨%Hsp, #Fcl, #Fcodec, #Fvi, #Fti, #Fdi, #Fpp, #Frp, #Fgr, #Fmt, #Flt, %Hlt, #Hkc,
    #Hcl, #Hone, #Hregs, #Hcon⟩
  ihave #Ptr : isPkgInit (PROP := IProp GF) pkg_id.k8s_io.component_base.tracing $$ []
  · iPkgInit
  ihave #Pat : isPkgInit (PROP := IProp GF) pkg_id.go_opentelemetry_io.otel.«attribute» $$ []
  · iPkgInit
  ihave #Pau : isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.audit $$ []
  · iPkgInit
  ihave #Pme : isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.etcd3.metrics $$ []
  · iPkgInit
  ihave #Pti : isPkgInit (PROP := IProp GF) pkg_id.time $$ []
  · iPkgInit
  ihave #Pku : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.kubernetes $$ []
  · iPkgInit
  ihave #Pcl : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 $$ []
  · iPkgInit
  ihave #Psg : isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage $$ []
  · iPkgInit
  ihave Fgr' := Fgr
  iStructNamed Fgr'
  ihave Hkc' := Hkc
  iStructNamed Hkc'
  iunfold contractOk at Hcon
  icases Hcon with ⟨-, #Henc, #Hver, #Htr, #Hdec, #Hzero⟩
  ihave %Hobjn := c.S.objAt_ne_nil obj o rv $$ Hobj
  wp_bind (App (Val wrapDefer) _)
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_apply wp_prepareKey sp c.resourcePrefix c.pathPrefix key false $$ [] as %pk %perr %Hpk
  · iframe #
  rw [hk] at Hpk
  obtain ⟨rfl, rfl⟩ := Hpk
  (try wp_auto)
  wp_apply wp_GetAuditIDTruncated as %aid -
  wp_apply wp_String as %kv0 -
  wp_apply wp_String as %kv1 -
  (try wp_auto)
  wp_apply wp_getTypeName obj $$ [] as %tn -
  · iframe #
    ipureintro; exact Hobjn
  wp_apply wp_String as %kvt -
  (try wp_auto)
  wp_apply wp_String as %kv2 -
  (try wp_auto)
  wp_apply wp_String as %kv3 -
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %asl ⟨Hasl, -⟩
  wp_apply wp_Start ci cd _ _ $$ [] as %ci' %spn ⟨%Hspn, #Hctx', #Hce'⟩
  · iframe #
  (try wp_auto)
  iunfold versionerOk at Hver
  icases Hver with ⟨#HvORV, #HvPrep, #HvUpd, #HvParse⟩
  wp_apply HvORV $$ [$Hobj] as %n %verr Hobj %Hn
  rw [hrv] at Hn
  obtain ⟨rfl, rfl⟩ := Hn
  (try wp_auto)
  wp_apply HvPrep $$ [$Hobj] as %perr ⟨Hobj, %Hperr⟩
  subst Hperr
  (try wp_auto)
  wp_apply wp_AddEvent spn _ _ $$ []
  · iframe #
    ipureintro; exact Hspn
  (try wp_auto)
  iunfold encodeOk at Henc
  wp_apply Henc $$ [$Hobj] as %dsl %eerr Hobj Henc'
  icases Henc' with (⟨%Heerr, Hdsl⟩ | ⟨%Heerr, #Hes⟩)
  · subst Heerr
    ipersist Hdsl
    (try wp_auto)
    wp_apply wp_Int as %kvl -
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %lsl ⟨Hlsl, -⟩
    (try wp_auto)
    wp_apply wp_AddEvent spn _ _ $$ []
    · iframe #
      ipureintro; exact Hspn
    (try wp_auto)
    iunfold transformerOk at Htr
    icases Htr with ⟨-, #HtrTo⟩
    wp_apply HtrTo $$ [$Hdsl] as %vsl %terr Htres
    icases Htres with (⟨%Hterr, %v, %Hv, #Hvsl⟩ | ⟨%Hterr, #Htes⟩)
    · subst Hterr
      (try wp_auto)
      wp_apply wp_AddEvent spn _ _ $$ []
      · iframe #
        ipureintro; exact Hspn
      (try wp_auto)
      wp_apply _root_.Perennial.time.wp_Now as %t0 -
      (try wp_auto)
      have hpfx : c.pfx <+: c.pathPrefix ++ k := prepareKeyM_prefix _ _ _ _ _ hk
      have hdv : c.S.dec v = some (o, true) := c.S.dec_toS_encode o v Hv
      have hm : ∀ (i : Nat) (x : client.SrvAt GF), c.ms[i]? = some x →
          k8sAu1 (GF := GF) x.γr.kv c (fun s => (s.create (E := Empty) (c.pathPrefix ++ k) o 0).1) Ψ ⊢
          kvOpAu1 x.γr.kv (.txn (kubernetes.optPutTxn (c.pathPrefix ++ k) v (W64 0) false))
            (fun σ => iprop(Ψ σ ∗ ⌜kvWf c σ ∧ σ.rev + 2 < 2 ^ 63⌝ ∗ kvSeen c.γh σ)) :=
        fun i x hx => by
          iintro HAU
          unfold kvOpAu1
          iapply (k8sAu1_kvAu1 x.γr.kv c _ _ Ψ (stepOk_create c _ v o hpfx hdv)) $$ HAU
      ihave Hau' := (BigAndL.bigAndL_mono hm) $$ Hau
      rw [method_unfold (t := go.GoType.PointerType go_etcd_io.etcd.client.v3.kubernetes.Client.ty)
        (m := go!"OptimisticPut")]
      wp_call
      (try wp_auto)
      wp_apply (wp_kPut (go_etcd_io.etcd.client.v3.kubernetes.Client.mk c.cl
          (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.v3.kubernetes.Client.ty)
            #c.kc)) c.ms c.V ci' cd (c.pathPrefix ++ k) vsl v (W64 0)
          ⟨false, zero_val _⟩ (fun σ => iprop(Ψ σ ∗ ⌜kvWf c σ ∧ σ.rev + 2 < 2 ^ 63⌝ ∗ kvSeen c.γh σ)) rfl) $$ [Hau']
        as %resp %perr Hput
      · iframe #
        iexact Hau'
      (try wp_auto)
      wp_apply wp_txnError as %te -
      (try wp_auto)
      wp_apply wp_RecordEtcdRequest
      (try wp_auto)
      icases Hput with (⟨%Hpe, %σ, ⟨HΨ, %Hwfσ, -⟩, %Hσ, Hkvo⟩ | ⟨%Hpe, %Hpce, #Hpse, #Hpcl⟩)
      · -- the transaction ran at σ
        subst Hpe
        obtain ⟨hsucc, hrevσ, hb⟩ := Hσ
        (try wp_auto)
        wp_apply wp_AddEvent spn _ _ $$ []
        · iframe #
          ipureintro; exact Hspn
        (try wp_auto)
        have hout := create_out c σ Hwfσ.1 _ v o hpfx hdv
        have hsucc' : resp.Succeeded' = (txn.srvRunTxn (W64 ((σ.rev + 1 : Nat) : Int)) σ.kvs
            (kubernetes.optPutTxn (c.pathPrefix ++ k) v (W64 0) false)).1 := hsucc
        rw [← hsucc'] at hout
        cases hs : resp.Succeeded'
        · -- the key exists
          rw [hs] at hout
          (try wp_auto)
          wp_apply wp_NewKeyExistsError (c.pathPrefix ++ k) (W64 0) as %ep Hep
          ipersist Hep
          (try wp_auto)
          wp_apply wp_End spn _ $$ []
          · iframe #
            ipureintro; exact Hspn
          (try wp_auto)
          iapply HΦ
          isplitl [Hobj]
          · iexists o, []; iexact Hobj
          iright
          iexists σ
          iframe HΨ
          rw [hout]
          simp only [Bool.false_eq_true, ↓reduceIte, respIs, storageErrIs]
          isplitl []
          · iexists ep
            iframe Hep
            ipureintro; rfl
          iexists o0, rv0
          iexact Hout
        · -- created
          rw [hs] at hout
          simp only [↓reduceIte] at hout
          ihave %Houtn := c.S.objAt_ne_nil out o0 rv0 $$ Hout
          cases out with
          | nil => exact absurd rfl Houtn
          | ok oi =>
            (try wp_auto)
            iunfold decoderOk at Hdec
            wp_apply Hdec $$ [$Hdsl] [$Hout] as %derr Hdres
            rw [c.S.decode_encode]
            icases Hdres with ⟨%Hderr, Hout⟩
            subst Hderr
            (try wp_auto)
            wp_apply wp_Int as %kvl2 -
            wp_apply wp_slice_literal
            isplitr
            · ipureintro; rfl
            iintro %lsl2 ⟨Hlsl2, -⟩
            (try wp_auto)
            wp_apply wp_AddEvent spn _ _ $$ []
            · iframe #
              ipureintro; exact Hspn
            (try wp_auto)
            wp_apply wp_End spn _ $$ []
            · iframe #
              ipureintro; exact Hspn
            (try wp_auto)
            iapply HΦ
            isplitl [Hobj]
            · iexists o, []; iexact Hobj
            iright
            iexists σ
            iframe HΨ
            rw [hout]
            simp only [respIs]
            rw [← hrevσ]
            iframe Hout
      · -- the client failed
        cases perr with
        | nil => exact absurd rfl Hpe
        | ok ei =>
          (try wp_auto)
          iunfold go_etcd_io.etcd.cache.v3.statusErrOk at Hpse
          ihave ⟨#Hes, -, -⟩ := Hpse $$ %ei %rfl
          iunfold go_etcd_io.etcd.cache.v3.errorStringSpec at Hes
          wp_apply Hes as %estr
          wp_apply wp_String as %kve -
          wp_apply wp_slice_literal
          isplitr
          · ipureintro; rfl
          iintro %esl ⟨Hesl, -⟩
          (try wp_auto)
          wp_apply wp_AddEvent spn _ _ $$ []
          · iframe #
            ipureintro; exact Hspn
          (try wp_auto)
          wp_apply wp_End spn _ $$ []
          · iframe #
            ipureintro; exact Hspn
          (try wp_auto)
          iapply HΦ
          isplitl [Hobj]
          · iexists o, []; iexact Hobj
          ileft
          isplitl []
          · iapply (unkErr_client c _ (by nofun) Hpce) $$ Hpcl
            iunfold go_etcd_io.etcd.cache.v3.statusErrOk
            iexact Hpse
          iexists o0, rv0
          iexact Hout
    · -- the transformer failed
      cases terr with
      | nil => exact absurd rfl Hterr
      | ok ti' =>
        (try wp_auto)
        ihave #Hes := go_etcd_io.etcd.cache.v3.errStrOk_elim ti' $$ Htes
        iunfold go_etcd_io.etcd.cache.v3.errorStringSpec at Hes
        wp_apply Hes as %estr
        wp_apply wp_String as %kve -
        wp_apply wp_slice_literal
        isplitr
        · ipureintro; rfl
        iintro %esl ⟨Hesl, -⟩
        (try wp_auto)
        wp_apply wp_AddEvent spn _ _ $$ []
        · iframe #
          ipureintro; exact Hspn
        (try wp_auto)
        wp_apply wp_NewInternalError ti' $$ [] as %ie -
        · iframe #
          iunfold go_etcd_io.etcd.cache.v3.errorStringSpec
          iexact Hes
        (try wp_auto)
        wp_apply wp_End spn _ $$ []
        · iframe #
          ipureintro; exact Hspn
        (try wp_auto)
        iapply HΦ
        isplitl [Hobj]
        · iexists o, []; iexact Hobj
        ileft
        isplitl []
        · iapply unkErr_internal
        iexists o0, rv0
        iexact Hout
  · -- the encoding failed
    obtain ⟨Heerr, Hee⟩ := Heerr
    cases eerr with
    | nil => exact absurd rfl Heerr
    | ok ee =>
      (try wp_auto)
      ihave #Hes := go_etcd_io.etcd.cache.v3.errStrOk_elim ee $$ Hes
      iunfold go_etcd_io.etcd.cache.v3.errorStringSpec at Hes
      wp_apply wp_Int as %kvl -
      wp_apply Hes as %estr
      wp_apply wp_String as %kve -
      wp_apply wp_slice_literal
      isplitr
      · ipureintro; rfl
      iintro %esl ⟨Hesl, -⟩
      (try wp_auto)
      wp_apply wp_AddEvent spn _ _ $$ []
      · iframe #
        ipureintro; exact Hspn
      (try wp_auto)
      wp_apply wp_End spn _ $$ []
      · iframe #
        ipureintro; exact Hspn
      (try wp_auto)
      iapply HΦ
      isplitl [Hobj]
      · iexists o, []; iexact Hobj
      ileft
      isplitl []
      · iapply (unkErr_enc c _ (by nofun) Hee)
      iexists o0, rv0
      iexact Hout

end proof

end k8s
end EtcdGrove
end Perennial
