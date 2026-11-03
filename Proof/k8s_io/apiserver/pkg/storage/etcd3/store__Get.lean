/-
Lean-first (no Rocq counterpart).

The proof of `(*store).Get`: the prepared key, tracing (no-ops), the client's `Get`
(`kubernetes.Client.Get`: the state `σ` the read update fired at), then the answer by the key's
key-value at `σ`: none (the zero object or "not found"), or its value through the transformer and
the decoder (the contract), which by the caller's `kvWf` succeed, giving the model's item.
-/
module

public import Spec.k8s_io.apiserver.pkg.storage.etcd3.store__Get
public import Spec.k8s_io.apiserver.pkg.storage.etcd3.store__prepareKey
public import Spec.k8s_io.apiserver.pkg.storage.etcd3.store__validateMinimumResourceVersion
public import Spec.k8s_io.apiserver.pkg.storage.NewKeyNotFoundError
public import Spec.k8s_io.component_base.tracing.Start
public import Spec.k8s_io.component_base.tracing.Span__AddEvent
public import Spec.k8s_io.component_base.tracing.Span__End
public import Spec.go_opentelemetry_io.otel.attribute.String
public import Spec.go_opentelemetry_io.otel.attribute.Int
public import Spec.k8s_io.apiserver.pkg.audit.GetAuditIDTruncated
public import Spec.k8s_io.apiserver.pkg.storage.etcd3.metrics.OperationLatencyTracker__Record
public import Spec.go_etcd_io.etcd.client.v3.kubernetes.Client__Get
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
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apiserver.pkg.storage.etcd3.Assumptions]

theorem store.Get.wp_proof
    (wp_prepareKey : store.prepareKey.spec (GF := GF) (hG := hG))
    (wp_validateMin : store.validateMinimumResourceVersion.spec (GF := GF) (hG := hG))
    (wp_NewKeyNotFoundError : storage.NewKeyNotFoundError.spec (GF := GF) (hG := hG))
    (wp_Start : tracing.Start.spec (GF := GF) (hG := hG))
    (wp_AddEvent : tracing.Span.AddEvent.spec (GF := GF) (hG := hG))
    (wp_End : tracing.Span.End.spec (GF := GF) (hG := hG))
    (wp_String : «attribute».String.spec (GF := GF) (hG := hG))
    (wp_Int : «attribute».Int.spec (GF := GF) (hG := hG))
    (wp_GetAuditIDTruncated : audit.GetAuditIDTruncated.spec (GF := GF) (hG := hG))
    (wp_Record : metrics.OperationLatencyTracker.Record.spec (GF := GF) (hG := hG))
    (wp_kGet : kubernetes.Client.Get.spec (GF := GF) (hG := hG)) :
    store.Get.spec (GF := GF) (hG := hG) := by
  intro _ _ Obj _ sp c ci cd key opts out o0 rv0 k Q hk hkl hrv hQ
  wp_start as ⟨#Hst, #Hctx, #Hce, Hout, Hau⟩
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
  wp_auto
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
  wp_apply _root_.Perennial.time.wp_Now as %t0 -
  (try wp_auto)
  rw [method_unfold (t := go.GoType.PointerType go_etcd_io.etcd.client.v3.kubernetes.Client.ty)
    (m := go!"Get")]
  wp_call
  (try wp_auto)
  wp_apply (wp_kGet (go_etcd_io.etcd.client.v3.kubernetes.Client.mk c.cl
      (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.v3.kubernetes.Client.ty) #c.kc))
      c.ms c.V ci' cd (c.pathPrefix ++ k) (zero_val _) Q rfl) $$ [Hau]
    as %resp %gerr Hget
  · iframe #
    iexact Hau
  (try wp_auto)
  wp_apply wp_Record c.lt gerr t0 $$ []
  · iframe #
    ipureintro; exact Hlt
  icases Hget with (⟨%Hgerr, %σ, #HQ, %Hσ, #Hkv⟩ | ⟨%Hgerr, %Hgce, #Hgse, #Hgcl⟩)
  · -- the client read the state σ
    subst Hgerr
    obtain ⟨hrevσ, hb⟩ := Hσ
    ihave %Hwf := (hQ _ _ σ) $$ HQ
    have hpfx : c.pfx <+: c.pathPrefix ++ k := prepareKeyM_prefix _ _ _ _ _ hk
    (try wp_auto)
    wp_apply wp_AddEvent spn _ _ $$ []
    · iframe #
      ipureintro; exact Hspn
    (try wp_auto)
    rw [hrv]
    wp_apply wp_validateMin sp _
    (try wp_auto)
    iunfold contractOk at Hcon
    icases Hcon with ⟨-, #Henc, #Hver, #Htr, #Hdec, #Hzero⟩
    cases hf : mvcc.findKey (c.pathPrefix ++ k) σ.kvs with
    | none =>
      iunfold kubernetes.kvOut at Hkv
      icases Hkv with %HKV
      have hn := c.abs_none σ _ hf
      wp_if_destruct
      · cases hig : opts.IgnoreNotFound'
        · -- not found
          (try wp_auto)
          wp_apply wp_NewKeyNotFoundError (c.pathPrefix ++ k) resp.Revision' as %ep Hep
          ipersist Hep
          (try wp_auto)
          wp_apply wp_End spn _ $$ []
          · iframe #
            ipureintro; exact Hspn
          (try wp_auto)
          iapply HΦ
          iright
          iexists σ
          iframe HQ
          have hg : (c.abs σ).get (E := Empty) (c.pathPrefix ++ k) 0 false =
              .err (.notFound (c.pathPrefix ++ k) σ.rev) := by
            unfold KSt.get
            rw [hn]
            simp only [gt_iff_lt, Nat.not_lt_zero, ↓reduceIte, Bool.false_eq_true]
            rfl
          rw [hg]
          simp only [respIs, storageErrIs]
          isplitl []
          · iexists ep
            rw [← hrevσ]
            iframe Hep
            ipureintro; rfl
          iexists o0, rv0
          iexact Hout
        · -- the zero object
          (try wp_auto)
          iunfold zeroOk at Hzero
          wp_apply Hzero $$ [$Hout] as %zerr ⟨%Hz, Hout⟩
          (try wp_auto)
          wp_apply wp_End spn _ $$ []
          · iframe #
            ipureintro; exact Hspn
          (try wp_auto)
          iapply HΦ
          iright
          iexists σ
          iframe HQ
          have hg : (c.abs σ).get (E := Empty) (c.pathPrefix ++ k) 0 true = .zero := by
            unfold KSt.get
            rw [hn]
            simp
          rw [hg]
          simp only [respIs]
          iframe Hout
          ipureintro; exact Hz
      · exact absurd HKV Hif
    | some v =>
      iunfold kubernetes.kvOut at Hkv
      icases Hkv with ⟨%HKV, #Hkvv⟩
      obtain ⟨o, bc, hd⟩ := c.dec_of_wf σ Hwf _ hpfx v hf
      obtain ⟨d, st, hfs, hdc, -⟩ := ObjCodec.dec_some _ _ _ _ hd
      have hit := c.abs_some σ _ hpfx v hf o bc hd
      wp_if_destruct
      · exact absurd Hif HKV
      iunfold txn.kvIs at Hkvv
      icases Hkvv with ⟨%ksl, %vsl, #Hkey, #Hksl, #Hcrev, #Hmod, #Hver, #Hval, #Hvsl, #Hlease⟩
      (try wp_auto)
      iunfold transformerOk at Htr
      icases Htr with ⟨#HtrFrom, -⟩
      wp_apply HtrFrom $$ [$Hvsl] as %dsl %st' %terr Htres
      rw [hfs]
      icases Htres with ⟨%Hterr, #Hdsl⟩
      obtain ⟨rfl, rfl⟩ := Hterr
      (try wp_auto)
      wp_apply wp_AddEvent spn _ _ $$ []
      · iframe #
        ipureintro; exact Hspn
      (try wp_auto)
      iunfold decoderOk at Hdec
      wp_apply Hdec $$ [$Hdsl] [$Hout] as %derr Hdres
      rw [hdc]
      icases Hdres with ⟨%Hderr, Hout⟩
      subst Hderr
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
      wp_apply wp_End spn _ $$ []
      · iframe #
        ipureintro; exact Hspn
      (try wp_auto)
      iapply HΦ
      iright
      iexists σ
      iframe HQ
      have hg : (c.abs σ).get (E := Empty) (c.pathPrefix ++ k) 0 opts.IgnoreNotFound' =
          .obj o (uint.nat v.modRev) := by
        unfold KSt.get
        rw [hit]
        simp
      rw [hg]
      simp only [respIs]
      rw [W64_uint_nat]
      iframe Hout
  · -- the client failed
    cases gerr with
    | nil => exact absurd rfl Hgerr
    | ok ei =>
      (try wp_auto)
      iunfold go_etcd_io.etcd.cache.v3.statusErrOk at Hgse
      ihave ⟨#Hes, -, -⟩ := Hgse $$ %ei %rfl
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
      ileft
      isplitl []
      · iapply (unkErr_client c _ (by nofun) Hgce) $$ Hgcl
        iunfold go_etcd_io.etcd.cache.v3.statusErrOk
        iexact Hgse
      iexists o0, rv0
      iexact Hout

end proof

end k8s
end EtcdGrove
end Perennial
