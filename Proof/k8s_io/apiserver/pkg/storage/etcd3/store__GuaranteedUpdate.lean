/-
Lean-first (no Rocq counterpart).

The proof of `(*store).GuaranteedUpdate`: the prepared key, tracing (no-ops), the destination's
`reflect.Value`, the initial read (`getCurrentState`), then the loop, whose invariant is the
store's reading `s` of the key's key-value at a state `σ` the caller's update fired at as a read
(`rdOk`), with the caller's token `W` (as `conditionalDelete`'s). Each iteration runs `tryUpdate`
(`updateState`): an error is the model's answer at `σ` (`update_err`); otherwise the result's
encoding is either the stored data, not stale, and the store skips the write (the model's no-op at
`σ`, `update_skip`), or `updateOnce` either answers (an error, or the write) or, on a conflict,
gives the next iteration's reading.
-/
module

public import Spec.k8s_io.apiserver.pkg.storage.etcd3.store__GuaranteedUpdate
public import Spec.k8s_io.apiserver.pkg.storage.etcd3.store__prepareKey
public import Spec.k8s_io.apiserver.pkg.storage.etcd3.store__getCurrentState
public import Spec.k8s_io.apiserver.pkg.storage.etcd3.store__updateState
public import Spec.k8s_io.apiserver.pkg.storage.etcd3.store__updateOnce
public import Spec.k8s_io.apiserver.pkg.storage.etcd3.refreshOnError
public import Spec.k8s_io.apiserver.pkg.storage.etcd3.getTypeName
public import Spec.k8s_io.apiserver.pkg.storage.Preconditions__Check
public import Spec.k8s_io.apimachinery.pkg.conversion.EnforcePtr
public import Spec.k8s_io.component_base.tracing.Start
public import Spec.k8s_io.component_base.tracing.Span__AddEvent
public import Spec.k8s_io.component_base.tracing.Span__End
public import Spec.go_opentelemetry_io.otel.attribute.String
public import Spec.go_opentelemetry_io.otel.attribute.Int
public import Spec.k8s_io.apiserver.pkg.audit.GetAuditIDTruncated
public import Perennial.Proof.bytes.Link

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

theorem store.GuaranteedUpdate.wp_proof
    (wp_prepareKey : store.prepareKey.spec (GF := GF) (hG := hG))
    (wp_getTypeName : getTypeName.spec (GF := GF) (hG := hG))
    (wp_EnforcePtr : conversion.EnforcePtr.spec (GF := GF) (hG := hG))
    (wp_getCur : store.getCurrentState.spec (GF := GF) (hG := hG))
    (wp_Check : storage.Preconditions.Check.spec (GF := GF) (hG := hG))
    (wp_updateState : store.updateState.spec (GF := GF) (hG := hG))
    (wp_updateOnce : store.updateOnce.spec (GF := GF) (hG := hG))
    (wp_refresh : refreshOnError.spec (GF := GF) (hG := hG))
    (wp_Start : tracing.Start.spec (GF := GF) (hG := hG))
    (wp_AddEvent : tracing.Span.AddEvent.spec (GF := GF) (hG := hG))
    (wp_End : tracing.Span.End.spec (GF := GF) (hG := hG))
    (wp_String : «attribute».String.spec (GF := GF) (hG := hG))
    (wp_Int : «attribute».Int.spec (GF := GF) (hG := hG))
    (wp_GetAuditIDTruncated : audit.GetAuditIDTruncated.spec (GF := GF) (hG := hG)) :
    store.GuaranteedUpdate.spec (GF := GF) (hG := hG) := by
  intro _ _ Obj _ E _ sp c ci cd key dest o0 rv0 f uf W Q Φu k hk
  wp_start as ⟨#Hst, #Hctx, #Hce, Hout, HW, #Hau, #Hup⟩
  ihave Hst' := Hst
  iunfold isStore at Hst'
  icases Hst' with ⟨%Hsp, #Fcl, #Fcodec, #Fvi, #Fti, #Fdi, #Fpp, #Frp, #Fgr, #Fmt, #Flt, %Hlt,
    #Hkc, #Hcl, #Hone, #Hregs, %Hwl, #Hcon⟩
  iunfold contractOk at Hcon
  icases Hcon with ⟨%Hty, #Henc, #Hver, #Htr, #Hdec, #Hzero⟩
  ihave #Ptr : isPkgInit (PROP := IProp GF) pkg_id.k8s_io.component_base.tracing $$ []
  · iPkgInit
  ihave #Pat : isPkgInit (PROP := IProp GF) pkg_id.go_opentelemetry_io.otel.«attribute» $$ []
  · iPkgInit
  ihave #Pau : isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.audit $$ []
  · iPkgInit
  ihave #Pcv : isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apimachinery.pkg.conversion $$ []
  · iPkgInit
  ihave #Psg : isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage $$ []
  · iPkgInit
  ihave #Pby : isPkgInit (PROP := IProp GF) pkg_id.bytes $$ []
  · iPkgInit
  ihave Fgr' := Fgr
  iStructNamed Fgr'
  ihave #Hrd := k8sAusRW_read c.ms c (updStep (c.pathPrefix ++ k) c.S.zero f) W Q Φu $$ Hau
  have hR : ∀ σ, rdOk (GF := GF) c Q σ ⊢ ⌜kvWf c σ⌝ := fun σ => by
    iintro #H
    iunfold rdOk at H
    icases H with ⟨-, %h, -⟩
    ipureintro; exact h.1
  have hpfx : c.pfx <+: c.pathPrefix ++ k := prepareKeyM_prefix _ _ _ _ _ hk
  ihave %Hptr := c.S.objAt_ptr dest o0 rv0 $$ Hout
  obtain ⟨p, hp, rfl⟩ := Hptr
  ihave %Hdn := c.S.objAt_ne_nil _ o0 rv0 $$ Hout
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
  wp_apply wp_getTypeName _ $$ [] as %tn -
  · iframe #
    ipureintro; exact Hdn
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
  wp_apply wp_EnforcePtr c.S.objTy p $$ [] as %v %eerr %Hen'
  · iframe #
    ipureintro; exact hp
  obtain ⟨rfl, Hv⟩ := Hen'
  (try wp_auto)
  wp_apply (wp_getCur Obj sp c ci' cd go!"updateGet" (c.pathPrefix ++ k) v p (rdOk c Q) hpfx hR)
    $$ [] as %gf #Hgf
  · iframe #
    ipureintro; exact Hv
  (try wp_auto)
  iunfold getStateOk at Hgf
  wp_apply Hgf as %st %err Hr
  icases Hr with (#Herr | ⟨%σ, #Hrdσ, Hat⟩)
  · ihave %Hne := unkErr_ne c err $$ Herr
    cases err with
    | nil => exact absurd rfl Hne
    | ok ei =>
      (try wp_auto)
      wp_apply wp_End spn _ $$ []
      · iframe #
        ipureintro; exact Hspn
      (try wp_auto)
      iapply HΦ
      iunfold updOut
      ileft
      isplitr
      · iexact Herr
      iexists o0, rv0
      iexact Hout
  · unfold stAt
    cases hf : mvcc.findKey (c.pathPrefix ++ k) σ.kvs with
    | none =>
      icases Hat with ⟨%Hst0, Herr⟩
      iunfold storageErrIs at Herr
      icases Herr with ⟨%ep, %Hep, #Hep⟩
      subst Hep
      (try wp_auto)
      wp_apply wp_End spn _ $$ []
      · iframe #
        ipureintro; exact Hspn
      (try wp_auto)
      iapply HΦ
      iunfold updOut
      iright
      iright
      iexists σ
      iunfold rdOk at Hrdσ
      icases Hrdσ with ⟨#HQ, %Hwf, -⟩
      rw [update_none c σ _ hf]
      iframe HQ HW
      isplitr
      · ipureintro; rfl
      simp only [respIs, storageErrIs]
      isplitl []
      · iexists ep
        iframe Hep
        ipureintro; rfl
      iexists o0, rv0
      iexact Hout
    | some kv =>
      icases Hat with ⟨%Herr, %s0, Hos, %Hs0⟩
      subst Herr
      (try wp_auto)
      wp_apply wp_AddEvent spn _ _ $$ []
      · iframe #
        ipureintro; exact Hspn
      (try wp_auto)
      ihave HI : (∃ (st : Loc) (s : OState Obj) (σ : KVState) (kv : EtcdKv),
          "origState" ∷ origState_ptr ↦ st ∗ "Hos" ∷ ownState c st s ∗
          "#Hrdσ" ∷ rdOk c Q σ ∗
          "%Hkv" ∷ ⌜mvcc.findKey (c.pathPrefix ++ k) σ.kvs = some kv ∧ stOfKv c kv s⌝ ∗
          "HW" ∷ W ∗ "Hout" ∷ c.S.objAt (interface.mkOk (go.GoType.PointerType c.S.objTy) #p) o0 rv0 :
          IProp GF) $$ [origState Hos HW Hout]
      · iexists st, s0, σ, kv
        iframe origState Hos HW Hout Hrdσ
        ipureintro; exact ⟨hf, Hs0⟩
      iclear Hrdσ
      clear hf Hs0 σ kv s0 st
      wp_for HI
      obtain ⟨hkv, hs⟩ := Hkv
      iunfold ownState at Hos
      icases Hos with ⟨%x, %m, %dsl, %Hstn, Hstp, Hobj, #Hdsl, Hm⟩
      (try wp_auto)
      wp_apply wp_Check
      (try wp_auto)
      ihave Hos : ownState c st s $$ [Hstp Hobj Hm]
      · iunfold ownState
        iexists x, m, dsl
        iframe Hstp Hobj Hdsl Hm
        ipureintro; exact Hstn
      wp_apply wp_updateState Obj E sp c st s f uf $$ [$Hos] as %ret %ttl %uerr ⟨⟨%x', Hx⟩, Hres⟩
      · iframe #
      cases hfr : f s.o (uint.nat s.rev) with
      | error e =>
        isimp only [hfr] at Hres
        icases Hres with %Huerr
        cases uerr with
        | nil => exact absurd rfl Huerr.1
        | ok ei =>
          (try wp_auto)
          wp_apply wp_refresh Obj c st s (GoInterface.ok ei) gf x' hs.2.2.2 $$ [$Hx]
            as %st' %err' ⟨%Heq, Hx⟩
          obtain ⟨rfl, rfl⟩ := Heq
          (try wp_auto)
          wp_for_post
          wp_apply wp_End spn _ $$ []
          · iframe #
            ipureintro; exact Hspn
          (try wp_auto)
          iapply HΦ
          iunfold updOut
          iright
          iright
          iexists σ
          ihave Hrd' := Hrdσ
          iunfold rdOk at Hrd'
          icases Hrd' with ⟨#HQ, %Hwf, -⟩
          rw [update_err c σ _ hpfx kv hkv s hs c.S.zero f e hfr]
          iframe HQ HW
          isplitr
          · ipureintro; rfl
          simp only [respIs]
          isplitr
          · ipureintro; exact ⟨by nofun, Huerr.2⟩
          iexists o0, rv0
          iexact Hout
      | ok o' =>
        isimp only [hfr] at Hres
        icases Hres with ⟨%Huerr, Hret⟩
        obtain ⟨rfl, rfl⟩ := Huerr
        (try wp_auto)
        wp_apply wp_AddEvent spn _ _ $$ []
        · iframe #
          ipureintro; exact Hspn
        (try wp_auto)
        iunfold encodeOk at Henc
        wp_apply Henc $$ [$Hret] as %esl %eerr Hret Henc'
        icases Henc' with (⟨%Heerr, Hesl⟩ | ⟨%Heerr, #Hes⟩)
        · subst Heerr
          ipersist Hesl
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
          iunfold ownStateX at Hx
          icases Hx with ⟨%m', %dsl', %Hstn', Hstp, #Hdsl', Hm⟩
          (try wp_auto)
          have hcur := hs.2.2.2
          cases hst : s.stale
          · simp only [Bool.not_false]
            (try wp_auto)
            wp_apply bytes.wp_Equal esl dsl' DFrac.discard DFrac.discard _ _ $$ [] as ⟨-, -⟩
            · iframe #
            cases hq : decide (c.S.encode o' = s.data)
            · (try simp only [hq])
              have hw : (!s.stale && decide (c.S.encode o' = s.data)) = false := by
                rw [hst, hq]; rfl
              (try wp_auto)
              ihave Hx : ownStateX c st s x' $$ [Hstp Hm]
              · iunfold ownStateX
                (try rw [hst])
                iexists m', dsl'
                iframe Hstp Hdsl' Hm
                ipureintro; exact Hstn'
              wp_apply (wp_updateOnce Obj E sp c ci' cd spn (c.pathPrefix ++ k)
                  (interface.mkOk (go.GoType.PointerType c.S.objTy) #p) o0 rv0 st s x' esl σ kv v p c.S.zero f o' W Q Φu
                  hpfx hkv hs hfr hw) $$ [$Hx $Hout $HW] as %st' %ok %uerr Hd
              · iframe #
                ipureintro; exact ⟨Hspn, Hv⟩
              icases Hd with (⟨#Hde, Hout⟩ | ⟨%Hok, %σ', HΦu, Hresp⟩ | ⟨%Hok, HW, Hout, %σ', #Hrd', Hat⟩)
              · -- an error
                ihave %Hne := unkErr_ne c uerr $$ Hde
                cases uerr with
                | nil => exact absurd rfl Hne
                | ok ei =>
                  (try wp_auto)
                  wp_for_post
                  wp_apply wp_End spn _ $$ []
                  · iframe #
                    ipureintro; exact Hspn
                  (try wp_auto)
                  iapply HΦ
                  iunfold updOut
                  ileft
                  iframe Hout
                  iexact Hde
              · -- written
                obtain ⟨rfl, rfl⟩ := Hok
                (try wp_auto)
                wp_for_post
                wp_apply wp_End spn _ $$ []
                · iframe #
                  ipureintro; exact Hspn
                (try wp_auto)
                iapply HΦ
                iunfold updOut
                iright
                ileft
                iexists σ'
                iframe HΦu Hresp
              · -- a conflict
                subst Hok
                unfold stAt
                cases hf' : mvcc.findKey (c.pathPrefix ++ k) σ'.kvs with
                | none =>
                  icases Hat with ⟨%Hst0, Herr⟩
                  iunfold storageErrIs at Herr
                  icases Herr with ⟨%ep, %Hep, #Hep⟩
                  subst Hep
                  (try wp_auto)
                  wp_for_post
                  wp_apply wp_End spn _ $$ []
                  · iframe #
                    ipureintro; exact Hspn
                  (try wp_auto)
                  iapply HΦ
                  iunfold updOut
                  iright
                  iright
                  iexists σ'
                  ihave Hrd'' := Hrd'
                  iunfold rdOk at Hrd''
                  icases Hrd'' with ⟨#HQ, %Hwf, -⟩
                  rw [update_none c σ' _ hf']
                  iframe HQ HW
                  isplitr
                  · ipureintro; rfl
                  simp only [respIs, storageErrIs]
                  isplitl []
                  · iexists ep
                    iframe Hep
                    ipureintro; rfl
                  iexists o0, rv0
                  iexact Hout
                | some kv' =>
                  icases Hat with ⟨%Herr, %s', Hos', %Hs'⟩
                  subst Herr
                  (try wp_auto)
                  wp_for_post
                  iframe
                  iexists st', s', σ', kv'
                  iframe Hos' HW Hout Hrd'
                  iframe
                  ipureintro; exact ⟨hf', Hs'⟩
            · -- the store skips the write: the model's no-op at σ
              have hn : (!s.stale && decide (c.S.encode o' = s.data)) = true := by
                rw [hst, hq]; rfl
              simp only [hcur, hst, Bool.not_true, Bool.not_false]
              (try wp_auto)
              iunfold decoderOk at Hdec
              wp_apply Hdec $$ [$Hdsl'] [$Hout] as %derr Hdres
              rw [hs.2.2.1]
              icases Hdres with ⟨%Hderr, Hout⟩
              subst Hderr
              (try wp_auto)
              wp_for_post
              wp_apply wp_End spn _ $$ []
              · iframe #
                ipureintro; exact Hspn
              (try wp_auto)
              iapply HΦ
              iunfold updOut
              iright
              iright
              iexists σ
              ihave Hrd' := Hrdσ
              iunfold rdOk at Hrd'
              icases Hrd' with ⟨#HQ, %Hwf, -⟩
              rw [update_skip c σ _ hpfx kv hkv s hs c.S.zero f o' hfr hn]
              iframe HQ HW
              isplitr
              · ipureintro; rfl
              simp only [respIs]
              rw [W64_uint_nat]
              iframe Hout
          · simp only [Bool.not_true]
            have hw : (!s.stale && decide (c.S.encode o' = s.data)) = false := by
              rw [hst]; rfl
            (try wp_auto)
            ihave Hx : ownStateX c st s x' $$ [Hstp Hm]
            · iunfold ownStateX
              (try rw [hst])
              iexists m', dsl'
              iframe Hstp Hdsl' Hm
              ipureintro; exact Hstn'
            wp_apply (wp_updateOnce Obj E sp c ci' cd spn (c.pathPrefix ++ k)
                (interface.mkOk (go.GoType.PointerType c.S.objTy) #p) o0 rv0 st s x' esl σ kv v p c.S.zero f o' W Q Φu
                hpfx hkv hs hfr hw) $$ [$Hx $Hout $HW] as %st' %ok %uerr Hd
            · iframe #
              ipureintro; exact ⟨Hspn, Hv⟩
            icases Hd with (⟨#Hde, Hout⟩ | ⟨%Hok, %σ', HΦu, Hresp⟩ | ⟨%Hok, HW, Hout, %σ', #Hrd', Hat⟩)
            · -- an error
              ihave %Hne := unkErr_ne c uerr $$ Hde
              cases uerr with
              | nil => exact absurd rfl Hne
              | ok ei =>
                (try wp_auto)
                wp_for_post
                wp_apply wp_End spn _ $$ []
                · iframe #
                  ipureintro; exact Hspn
                (try wp_auto)
                iapply HΦ
                iunfold updOut
                ileft
                iframe Hout
                iexact Hde
            · -- written
              obtain ⟨rfl, rfl⟩ := Hok
              (try wp_auto)
              wp_for_post
              wp_apply wp_End spn _ $$ []
              · iframe #
                ipureintro; exact Hspn
              (try wp_auto)
              iapply HΦ
              iunfold updOut
              iright
              ileft
              iexists σ'
              iframe HΦu Hresp
            · -- a conflict
              subst Hok
              unfold stAt
              cases hf' : mvcc.findKey (c.pathPrefix ++ k) σ'.kvs with
              | none =>
                icases Hat with ⟨%Hst0, Herr⟩
                iunfold storageErrIs at Herr
                icases Herr with ⟨%ep, %Hep, #Hep⟩
                subst Hep
                (try wp_auto)
                wp_for_post
                wp_apply wp_End spn _ $$ []
                · iframe #
                  ipureintro; exact Hspn
                (try wp_auto)
                iapply HΦ
                iunfold updOut
                iright
                iright
                iexists σ'
                ihave Hrd'' := Hrd'
                iunfold rdOk at Hrd''
                icases Hrd'' with ⟨#HQ, %Hwf, -⟩
                rw [update_none c σ' _ hf']
                iframe HQ HW
                isplitr
                · ipureintro; rfl
                simp only [respIs, storageErrIs]
                isplitl []
                · iexists ep
                  iframe Hep
                  ipureintro; rfl
                iexists o0, rv0
                iexact Hout
              | some kv' =>
                icases Hat with ⟨%Herr, %s', Hos', %Hs'⟩
                subst Herr
                (try wp_auto)
                wp_for_post
                iframe
                iexists st', s', σ', kv'
                iframe Hos' HW Hout Hrd'
                iframe
                ipureintro; exact ⟨hf', Hs'⟩
        · -- the encoding failed
          obtain ⟨Heerr, Hee⟩ := Heerr
          cases eerr with
          | nil => exact absurd rfl Heerr
          | ok ee =>
            (try wp_auto)
            ihave #Hes' := go_etcd_io.etcd.cache.v3.errStrOk_elim ee $$ Hes
            iunfold go_etcd_io.etcd.cache.v3.errorStringSpec at Hes'
            wp_apply wp_Int as %kvl -
            wp_apply Hes' as %estr
            wp_apply wp_String as %kve -
            wp_apply wp_slice_literal
            isplitr
            · ipureintro; rfl
            iintro %esl' ⟨Hesl', -⟩
            (try wp_auto)
            wp_apply wp_AddEvent spn _ _ $$ []
            · iframe #
              ipureintro; exact Hspn
            (try wp_auto)
            wp_for_post
            wp_apply wp_End spn _ $$ []
            · iframe #
              ipureintro; exact Hspn
            (try wp_auto)
            iapply HΦ
            iunfold updOut
            ileft
            isplitl []
            · iapply (unkErr_enc c _ (by nofun) Hee)
            iexists o0, rv0
            iexact Hout

end proof

end k8s
end EtcdGrove
end Perennial
