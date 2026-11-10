/-
Proof of `Spec/k8s_io/apiserver/pkg/storage/etcd3/store__getList.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.k8s_io.apiserver.pkg.storage.etcd3.store__getList
public import Spec.k8s_io.apiserver.pkg.storage.etcd3.store__getResourceSizeEstimator
public import Spec.k8s_io.apiserver.pkg.storage.etcd3.metrics.RecordEtcdRequest
public import Spec.go_etcd_io.etcd.client.v3.kubernetes.Client__List
public import Spec.go_etcd_io.etcd.client.v3.kubernetes.Client__GetAt

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : k8s_io.apiserver.pkg.storage.etcd3.Assumptions]

theorem store.getList.wp_proof
    (wp_kList : kubernetes.Client.List.spec (GF := GF) (hG := hG))
    (wp_kGetAt : kubernetes.Client.GetAt.spec (GF := GF) (hG := hG))
    (wp_RecordEtcdRequest : metrics.RecordEtcdRequest.spec (GF := GF) (hG := hG))
    (wp_rse : store.getResourceSizeEstimator.spec (GF := GF) (hG := hG)) :
    store.getList.spec (GF := GF) (hG := hG) := by
  intro _ _ Obj _ sp c ci cd kp recur lo Q hkp hct hrev hlim hrc hcp
  wp_start as ⟨#Hst, #Hctx, #Hce, Htt, %htb, HQ⟩
  ihave Hst' := Hst
  iunfold isStore at Hst'
  icases Hst' with ⟨%Hsp, #Fcl, #Fcodec, #Fvi, #Fti, #Fdi, #Fpp, #Frp, #Fgr, #Fmt, #Flt, %Hlt,
    #Hkc, #Hcl, #Hone, #Hregs, #Hcon, #Hlst⟩
  iunfold storeListOk at Hlst
  icases Hlst with ⟨%lf, %lγ, -, -, -, %Hutf, -⟩
  ihave #Pme : isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.etcd3.metrics $$ []
  · iPkgInit
  ihave #Pti : isPkgInit (PROP := IProp GF) pkg_id.time $$ []
  · iPkgInit
  ihave #Pku : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.kubernetes $$ []
  · iPkgInit
  ihave #Pcl : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 $$ []
  · iPkgInit
  ihave Hkc' := Hkc
  iStructNamed Hkc'
  (try wp_auto)
  wp_apply _root_.Perennial.time.wp_Now as %t0 -
  (try wp_auto)
  cases recur
  · -- not recursive: `Get` at the revision
    have hc0 : lo.Continue' = [] := hrc rfl
    (try wp_auto)
    rw [method_unfold (t := go.GoType.PointerType go_etcd_io.etcd.client.v3.kubernetes.Client.ty)
      (m := go!"Get")]
    wp_call
    (try wp_auto)
    wp_apply (wp_kGetAt (go_etcd_io.etcd.client.v3.kubernetes.Client.mk c.cl
        (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.v3.kubernetes.Client.ty) #c.kc))
        c.ms c.V ci cd kp (go_etcd_io.etcd.client.v3.kubernetes.GetOptions.mk lo.Revision') Q hkp
        hrev) $$ [HQ]
      as %gresp %gerr Hget
    · iframe #
      iexact HQ
    (try wp_auto)
    icases (k8s_io.apiserver.pkg.storage.etcd3.statusErrOk_split gerr _ _ _) $$ Hget with ⟨#Hse, Hget⟩
    wp_apply (wp_RecordEtcdRequest go!"get" c.gr _ _ (by decide) Hutf.1 Hutf.2) $$ []
    · iexact Hse
    (try wp_auto)
    wp_if_destruct
    all_goals (try wp_auto)
    all_goals
      wp_apply wp_slice_literal
      isplitr
      · ipureintro; rfl
      iintro %asl ⟨Hasl, -⟩
      (try wp_auto)
      wp_apply (wp_rse Obj sp c) $$ [Htt] as Htt
      · iframe #
        iexact Htt
      (try wp_auto)
      (try wp_if_destruct) <;> (try wp_auto) <;> (
        iapply HΦ
        iframe Htt
        icases Hget with (⟨%Hge, %σ, #HQσ, %Hσ, #Hkv⟩ | ⟨%Hge, %Hce', #Hse, #Hcl', #Hrs⟩)
        · ileft
          isplitr
          · ipureintro; exact Hge
          iexists σ
          iframe HQσ
          isplitr
          · ipureintro; exact Hσ.2.1
          simp only [listRespIs, hc0, ↓reduceIte, Bool.false_eq_true, pageKvsL_key]
          generalize mvcc.findKey kp (σ.at (σ.readRev lo.Revision')).kvs = fk
          cases fk with
          | none =>
            iunfold kubernetes.kvOut at Hkv
            icases Hkv with %Hn
            (try (exfalso; contradiction))
            all_goals
              isplitr
              · ipureintro; exact ⟨Hσ.1, rfl⟩
              rw [show List.replicate (go.arrayLiteralSize []).toNat (zero_val Loc) = [] from rfl]
              iexists []
              isplitl [Hasl]
              · iexact Hasl
              simp only [Option.toList]
              iapply BigSepL2.bigSepL2_nil.2
              iempintro
          | some v =>
            iunfold kubernetes.kvOut at Hkv
            icases Hkv with ⟨%Hn, #Hv⟩
            (try (exfalso; contradiction))
            all_goals
              isplitr
              · ipureintro; exact ⟨Hσ.1, rfl⟩
              iexists [gresp.KV']
              isplitl [Hasl]
              · iexact Hasl
              simp only [Option.toList]
              iapply BigSepL2.bigSepL2_cons.2
              iframe Hv
              iapply BigSepL2.bigSepL2_nil.2
              iempintro
        · iright
          isplitr
          · ipureintro; exact Hge
          iunfold readErrIs
          iunfold kClientErr
          iunfold rangeErrSound at Hrs
          iframe #
          ipureintro; exact ⟨Hge, Hce'⟩)
  · -- recursive: `List`
    (try wp_auto)
    rw [method_unfold (t := go.GoType.PointerType go_etcd_io.etcd.client.v3.kubernetes.Client.ty)
      (m := go!"List")]
    wp_call
    (try wp_auto)
    wp_apply (wp_kList (go_etcd_io.etcd.client.v3.kubernetes.Client.mk c.cl
        (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.v3.kubernetes.Client.ty) #c.kc))
        c.ms c.V ci cd kp lo Q hkp hct hrev hlim hcp) $$ [HQ]
      as %resp %lerr Hlist
    · iframe #
      iexact HQ
    (try wp_auto)
    icases (k8s_io.apiserver.pkg.storage.etcd3.statusErrOk_split lerr _ _ _) $$ Hlist with ⟨#Hse, Hlist⟩
    wp_apply (wp_RecordEtcdRequest go!"list" c.gr _ _ (by decide) Hutf.1 Hutf.2) $$ []
    · iexact Hse
    (try wp_auto)
    wp_apply (wp_rse Obj sp c) $$ [Htt] as Htt
    · iframe #
      iexact Htt
    (try wp_auto)
    wp_if_destruct <;> (try wp_auto) <;> (
      iapply HΦ
      iframe Htt
      icases Hlist with (⟨%Hle, %σ, #HQσ, %Hσ, Hresp⟩ | ⟨%Hle, %Hce', #Hse, #Hcl', #Hrs⟩)
      · ileft
        isplitr
        · ipureintro; exact Hle
        iexists σ
        iframe HQσ Hresp
        ipureintro; exact Hσ.1
      · iright
        isplitr
        · ipureintro; exact Hle
        iunfold readErrIs
        iunfold kClientErr
        iunfold rangeErrSound at Hrs
        iframe #
        ipureintro; exact ⟨Hle, Hce'⟩)

end proof

end k8s
end EtcdGrove
end Perennial
