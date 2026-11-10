/-
Lean-first (no Rocq counterpart).

The proof of `(*store).updateOnce`, as `deleteOnce`'s: the transformer's value `v` for the
result's encoding reads as the result, canonically (`dec_toS_encode`); the caller's updates and
token give the client's for the conditional put (`k8sAusRW_kvAu1`, by `updStepOk_item`: by
`stFrom`, every state in the store's history with the key at `origState`'s mod revision has
`origState`'s object there, or, at revision `0`, the zero state with `ignoreNotFound`, no item,
`stItem`); then the client's outcome: an error, success (the result decoded into `destination` at
the new revision, the model's answer by `update_item`), or a conflict (the store's reading of the
key at that state, with `ignoreNotFound`).
-/
module

public import Spec.k8s_io.apiserver.pkg.storage.etcd3.store__updateOnce
public import Spec.k8s_io.apiserver.pkg.storage.etcd3.store__stateFromEtcdResponse
public import Spec.k8s_io.apiserver.pkg.storage.etcd3.txnError
public import Spec.k8s_io.apiserver.pkg.storage.etcd3.metrics.RecordEtcdRequest
public import Spec.k8s_io.apiserver.pkg.storage.NewInternalError
public import Spec.k8s_io.component_base.tracing.Span__AddEvent
public import Spec.go_opentelemetry_io.otel.attribute.String
public import Spec.go_opentelemetry_io.otel.attribute.Int
public import Spec.k8s_io.klog.v2.V
public import Spec.k8s_io.klog.v2.Verbose__Infof
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
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : k8s_io.apiserver.pkg.storage.etcd3.Assumptions]

theorem store.updateOnce.wp_proof
    (wp_stateFrom : store.stateFromEtcdResponse.spec (GF := GF) (hG := hG))
    (wp_txnError : txnError.spec (GF := GF) (hG := hG))
    (wp_RecordEtcdRequest : metrics.RecordEtcdRequest.spec (GF := GF) (hG := hG))
    (wp_NewInternalError : storage.NewInternalError.spec (GF := GF) (hG := hG))
    (wp_AddEvent : tracing.Span.AddEvent.spec (GF := GF) (hG := hG))
    (wp_String : «attribute».String.spec (GF := GF) (hG := hG))
    (wp_Int : «attribute».Int.spec (GF := GF) (hG := hG))
    (wp_V : klog.V.spec (GF := GF) (hG := hG))
    (wp_Infof : klog.Verbose.Infof.spec (GF := GF) (hG := hG))
    (wp_kPut : kubernetes.Client.OptimisticPut.spec (GF := GF) (hG := hG)) :
    store.updateOnce.spec (GF := GF) (hG := hG) := by
  intro _ _ Obj _ E _ sp c ci cd span key dest o0 rv0 st s x dsl v p ign pre f o' W Φu
    hk hkl hpre hok hosz hw
  wp_start as ⟨#Hst, #Hctx, #Hce, %Hspn, Hos, #Hfrom, %Hign, #Hdsl, Hout, %Hv, HW, #Hau⟩
  ihave Hst' := Hst
  iunfold isStore at Hst'
  icases Hst' with ⟨%Hsp, #Fcl, #Fcodec, #Fvi, #Fti, #Fdi, #Fpp, #Frp, #Fgr, #Fmt, #Flt, %Hlt,
    #Hkc, #Hcl, #Hone, #Hregs, #Hcon⟩
  iunfold contractOk at Hcon
  icases Hcon with ⟨-, #Henc, #Hver, #Htr, #Hdec, #Hzero, -⟩
  ihave #Pme : isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.etcd3.metrics $$ []
  · iPkgInit
  ihave #Pti : isPkgInit (PROP := IProp GF) pkg_id.time $$ []
  · iPkgInit
  ihave #Pku : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.kubernetes $$ []
  · iPkgInit
  ihave #Pcl : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 $$ []
  · iPkgInit
  ihave #Pkl : isPkgInit (PROP := IProp GF) pkg_id.k8s_io.klog.v2 $$ []
  · iPkgInit
  ihave #Ptr : isPkgInit (PROP := IProp GF) pkg_id.k8s_io.component_base.tracing $$ []
  · iPkgInit
  ihave #Pat : isPkgInit (PROP := IProp GF) pkg_id.go_opentelemetry_io.otel.«attribute» $$ []
  · iPkgInit
  ihave #Psg : isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage $$ []
  · iPkgInit
  ihave Hkc' := Hkc
  iStructNamed Hkc'
  ihave %Hz := stFrom_zero c key s $$ Hfrom
  have hz : s.rev = W64 0 → ign = true ∧ s.o = c.S.zero := fun h => ⟨Hign h, by rw [Hz h]; rfl⟩
  ihave #HA := (stFrom_stItem c key hk s) $$ Hfrom
  iunfold ownStateX at Hos
  icases Hos with ⟨%m, %sdsl, %Hstn, Hstp, #Hsdsl, Hm⟩
  (try wp_auto)
  iunfold transformerOk at Htr
  icases Htr with ⟨-, #HtrTo⟩
  wp_apply HtrTo $$ [$Hdsl] as %vsl %terr Htres
  icases Htres with (⟨%Hterr, %val, %Hval, #Hvsl⟩ | ⟨%Hterr, #Htes⟩)
  · subst Hterr
    have hdv : c.S.dec val = some (o', true) := c.S.dec_toS_encode o' val Hval
    (try wp_auto)
    wp_apply wp_AddEvent span _ _ $$ []
    · iframe #
      ipureintro; exact Hspn
    (try wp_auto)
    wp_apply wp_AddEvent span _ _ $$ []
    · iframe #
      ipureintro; exact Hspn
    (try wp_auto)
    wp_apply _root_.Perennial.time.wp_Now as %t0 -
    (try wp_auto)
    ihave Hau' := (k8sAusRW_kvAu1 c.ms c (updStep key ign c.S.zero pre f) W Φu
      (.txn (kubernetes.optPutTxn key val s.rev true)) trivial
      (fun σ => (txn.srvRunTxn (W64 ((σ.rev + 1 : Nat) : Int)) σ.kvs
        (kubernetes.optPutTxn key val s.rev true)).1)
      (stepHand c (updStep key ign c.S.zero pre f))
      (fun σ => kvWf c σ → stItem c key s σ)
      (fun σ hw0 hb hA => ⟨(updStepOk_item c key hk s ign c.S.zero hz pre hpre f o' hok hw val hdv σ hw0 hb hA).1,
        fun hf => ⟨(updStepOk_item c key hk s ign c.S.zero hz pre hpre f o' hok hw val hdv σ hw0 hb hA).2 hf,
          fun hh => by simpa [stepHand] using hh⟩⟩)) $$ [HW Hau]
    · iframe HW HA Hau
    rw [method_unfold (t := go.GoType.PointerType go_etcd_io.etcd.client.v3.kubernetes.Client.ty)
      (m := go!"OptimisticPut")]
    wp_call
    (try wp_auto)
    wp_apply (wp_kPut (go_etcd_io.etcd.client.v3.kubernetes.Client.mk c.cl
        (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.v3.kubernetes.Client.ty)
          #c.kc)) c.ms c.V ci cd key vsl val s.rev ⟨true, zero_val _⟩ _ rfl hkl (hosz val Hval)) $$ [Hau']
      as %resp %perr Hput
    · iframe #
      iexact Hau'
    (try wp_auto)
    icases (k8s_io.apiserver.pkg.storage.etcd3.statusErrOk_split perr _ _ _) $$ Hput with ⟨#Hse0, Hput⟩
    wp_apply wp_txnError as %te Hte
    ihave #Hse := Hte $$ Hse0
    (try wp_auto)
    wp_apply wp_RecordEtcdRequest
    · iexact Hse
    (try wp_auto)
    icases Hput with (⟨%Hpe, %σ, ⟨Hres, #Hfs, %HAσ⟩, %Hσ, Hkvo⟩ | ⟨%Hpe, %Hpce, #Hpse, #Hpcl⟩)
    · subst Hpe
      ihave Hfs' := Hfs
      iunfold rdFacts at Hfs'
      icases Hfs' with ⟨%Hw0, #Hseen⟩
      have Hσf : kvWf c σ ∧ σ.rev + 2 < 2 ^ 63 ∧ (kvWf c σ → stItem c key s σ) := ⟨Hw0.1, Hw0.2, HAσ⟩
      obtain ⟨hsucc, hrevσ, hb, hvals⟩ := Hσ
      have hc := put_cases' c σ Hσf.1 Hσf.2.1 key val s.rev (fun _ => by rw [hdv]; rfl)
      (try wp_auto)
      wp_apply wp_AddEvent span _ _ $$ []
      · iframe #
        ipureintro; exact Hspn
      (try wp_auto)
      wp_apply wp_AddEvent span _ _ $$ []
      · iframe #
        ipureintro; exact Hspn
      (try wp_auto)
      cases hsc : resp.Succeeded'
      · -- a conflict: nothing changed
        have hf : (txn.srvRunTxn (W64 ((σ.rev + 1 : Nat) : Int)) σ.kvs
            (kubernetes.optPutTxn key val s.rev true)).1 = false := hsucc.symm.trans hsc
        have hid := hc.1 hf
        isimp only [hf, Bool.false_or] at Hres
        isimp only [hsc, Bool.not_false, Bool.and_self, ↓reduceIte] at Hkvo
        isimp only [single_filter key σ.kvs Hσf.1.1] at Hkvo
        icases Hkvo with #Hkvo
        rw [hid] at hrevσ
        have hdk : ∀ kv, mvcc.findKey key σ.kvs = some kv → ∃ o b, c.S.dec kv.value = some (o, b) :=
          fun kv hkv => c.dec_of_wf σ Hσf.1 key hk kv hkv
        simp only [Bool.not_false]
        (try wp_auto)
        wp_apply wp_slice_literal
        isplitr
        · ipureintro; rfl
        iintro %asl ⟨Hasl, -⟩
        (try wp_auto)
        wp_apply wp_V as %vb -
        (try wp_auto)
        wp_apply wp_Infof
        (try wp_auto)
        wp_apply (wp_stateFrom Obj sp c (GoInterface.ok ci) resp.KV' (mvcc.findKey key σ.kvs)
            resp.Revision' key v p ign hdk) $$ [] as %st' %err' Hsr
        · iframe #
          ipureintro; exact Hv
        cases hfk : mvcc.findKey key σ.kvs with
        | none =>
          cases ign
          rotate_left
          · -- `ignoreNotFound`: the zero state
            isimp only [hfk, ↓reduceIte] at Hsr
            icases Hsr with ⟨%Herr, Hos'⟩
            subst Herr
            (try wp_auto)
            wp_apply wp_AddEvent span _ _ $$ []
            · iframe #
              ipureintro; exact Hspn
            (try wp_auto)
            iapply HΦ
            iright
            iright
            isplitr
            · ipureintro; rfl
            iframe Hout
            iexists σ
            iframe Hfs Hres
            isplitl []
            · ipureintro; exact hvals
            unfold stAt
            rw [hfk]
            simp only [↓reduceIte]
            isplitr
            · ipureintro; first | rfl | trivial
            iexact Hos'
          isimp only [hfk, Bool.false_eq_true, ↓reduceIte] at Hsr
          icases Hsr with ⟨%Hst0, Herr⟩
          iunfold storageErrIs at Herr
          icases Herr with ⟨%ep, %Hep, #Hep⟩
          subst Hep Hst0
          (try wp_auto)
          iapply HΦ
          iright
          iright
          isplitr
          · ipureintro; rfl
          iframe Hout
          iexists σ
          iframe Hfs Hres
          isplitl []
          · ipureintro; exact hvals
          unfold stAt
          rw [hfk, ← hrevσ]
          simp only [Bool.false_eq_true, ↓reduceIte]
          isplitr
          · ipureintro; first | rfl | trivial
          iunfold storageErrIs
          iexists ep
          iframe Hep
          ipureintro; rfl
        | some kv' =>
          isimp only [hfk] at Hsr
          icases Hsr with ⟨%Herr, %s', Hos', %Hs'⟩
          subst Herr
          (try wp_auto)
          wp_apply wp_AddEvent span _ _ $$ []
          · iframe #
            ipureintro; exact Hspn
          (try wp_auto)
          iapply HΦ
          iright
          iright
          isplitr
          · ipureintro; rfl
          iframe Hout
          iexists σ
          iframe Hfs Hres
          isplitl []
          · ipureintro; exact hvals
          unfold stAt
          rw [hfk]
          isplitr
          · ipureintro; rfl
          iexists s'
          iframe Hos'
          ipureintro; exact Hs'
      · -- written
        have ht : (txn.srvRunTxn (W64 ((σ.rev + 1 : Nat) : Int)) σ.kvs
            (kubernetes.optPutTxn key val s.rev true)).1 = true := hsucc.symm.trans hsc
        obtain ⟨hm, -, -, hrev1⟩ := hc.2 ht
        have hcase : (s.rev = W64 0 ∧ (c.abs σ).items key = none ∧ ign = true ∧ s.o = c.S.zero) ∨
            (∃ b, (c.abs σ).items key = some ⟨s.o, uint.nat s.rev, b⟩ ∧
              (b = true → (!s.stale && decide (c.S.encode s.o = s.data)) = true)) := by
          rcases Hσf.2.2 Hσf.1 hm with ⟨h0, hn⟩ | ⟨-, -, b, hb', hc'⟩
          · exact .inl ⟨h0, hn, (hz h0).1, (hz h0).2⟩
          · exact .inr ⟨b, hb', hc'⟩
        have hupd := update_item c (c.abs σ) key s ign c.S.zero pre f o' hcase hpre hok hw
        isimp only [ht, Bool.true_or, ↓reduceIte] at Hres
        simp only [Bool.not_true]
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
        wp_apply wp_AddEvent span _ _ $$ []
        · iframe #
          ipureintro; exact Hspn
        (try wp_auto)
        iapply HΦ
        iright
        ileft
        isplitr
        · ipureintro; exact ⟨rfl, rfl⟩
        iexists σ
        iframe Hres
        have hrv : (c.abs σ).rv = σ.rev := rfl
        rw [hupd, hrv]
        simp only [respIs]
        rw [hrevσ, hrev1]
        iframe Hout
    · -- the client failed
      cases perr with
      | nil => exact absurd rfl Hpe
      | ok ei =>
        (try wp_auto)
        iunfold go_etcd_io.etcd.cache.v3.statusErrOk at Hpse
        ihave ⟨⟨%em, #Hes0⟩, -, -⟩ := Hpse $$ %ei %rfl
        ihave #Hes := go_etcd_io.etcd.cache.v3.errorMsgIs_errorStringSpec _ _ $$ Hes0
        iunfold go_etcd_io.etcd.cache.v3.errorStringSpec at Hes
        wp_apply Hes as %estr
        wp_apply wp_String as %kve -
        wp_apply wp_slice_literal
        isplitr
        · ipureintro; rfl
        iintro %esl ⟨Hesl, -⟩
        (try wp_auto)
        wp_apply wp_AddEvent span _ _ $$ []
        · iframe #
          ipureintro; exact Hspn
        (try wp_auto)
        iapply HΦ
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
      wp_apply wp_AddEvent span _ _ $$ []
      · iframe #
        ipureintro; exact Hspn
      (try wp_auto)
      wp_apply wp_NewInternalError ti' $$ [] as %ie -
      · iframe #
        iunfold go_etcd_io.etcd.cache.v3.errorStringSpec
        iexact Hes
      (try wp_auto)
      iapply HΦ
      ileft
      isplitl []
      · iapply unkErr_internal
      iexists o0, rv0
      iexact Hout

end proof

end k8s
end EtcdGrove
end Perennial
