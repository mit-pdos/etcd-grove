/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/k8s/etcd3/newStore.lean`. Lean-first (no
Rocq counterpart). The seed (`seed`), the two feature checks, then `etcd3.New` over the client with
the driver's contract (`driver_contractOk`) and `newObj`; `New`'s watch wand at the driver's watch
contract (`watchContractOk_driver`) and `newObj` (`newItemOk_driver`). `New`'s error is `nil`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.newStore
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.seed
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.noStreaming
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.watchList
public import Spec.k8s_io.apiserver.pkg.storage.etcd3.New
public import Spec.k8s_io.apiserver.pkg.storage.etcd3.NewDefaultLeaseManagerConfig
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.MainDefs
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Contract
public import Proof.github_com.mit_pdos.etcd_grove.PkgInitMemo

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

set_option maxHeartbeats 1600000 in
theorem newStore.wp_proof
    (wp_seed : seed.spec (GF := GF) (hG := hG))
    (wp_noStreaming : noStreaming.spec (GF := GF) (hG := hG))
    (wp_watchList : watchList.spec (GF := GF) (hG := hG))
    (wp_sNew : k8s.New.spec (GF := GF) (hG := hG))
    (wp_lmc : k8s.NewDefaultLeaseManagerConfig.spec (GF := GF) (hG := hG))
    (wp_newObj : newObj.spec (GF := GF) (hG := hG))
    (wp_Encode : runtime.Encode.spec (GF := GF) (hG := hG))
    (wp_cEncode : codec.Encode.spec (GF := GF) (hG := hG))
    (wp_Upd : versioner.UpdateObject.spec (GF := GF) (hG := hG))
    (wp_Prep : versioner.PrepareObjectForStorage.spec (GF := GF) (hG := hG))
    (wp_ORV : versioner.ObjectResourceVersion.spec (GF := GF) (hG := hG))
    (wp_Parse : versioner.ParseResourceVersion.spec (GF := GF) (hG := hG))
    (wp_From : identity.TransformFromStorage.spec (GF := GF) (hG := hG))
    (wp_To : identity.TransformToStorage.spec (GF := GF) (hG := hG))
    (wp_Dec : decoder.Decode.spec (GF := GF) (hG := hG))
    (wp_SetZero : runtime.SetZeroValue.spec (GF := GF) (hG := hG))
    (wp_UID : Obj.GetUID.spec (GF := GF) (hG := hG))
    (wp_RV : Obj.GetResourceVersion.spec (GF := GF) (hG := hG))
    (wp_Decode : runtime.Decode.spec (GF := GF) (hG := hG))
    (wp_cDecode : codec.Decode.spec (GF := GF) (hG := hG))
    (wp_Annotate : storage.AnnotateInitialEventsEndBookmark.spec (GF := GF) (hG := hG))
    (wp_GetAnn : Obj.GetAnnotations.spec (GF := GF) (hG := hG))
    (wp_SetAnn : Obj.SetAnnotations.spec (GF := GF) (hG := hG)) :
    newStore.spec (GF := GF) (hG := hG) := by
  intro _ _ _ kc cl ms V γs γh hAs hmsne Htb
  have hcon := driver_contractOk wp_Encode wp_cEncode wp_Upd wp_Prep wp_ORV wp_Parse wp_From wp_To
    wp_Dec wp_SetZero wp_UID wp_RV (driverSpec_tyOk objTyOk_holds)
  wp_start as ⟨#Hkc, #Hnc, #Hone, #Hregs, #Hsis, Hs⟩
  ihave #Hpd : isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 $$ []
  · iPkgInit
  ihave #Pcli : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 $$ []
  · iPkgInit
  ihave #Hkc' := Hkc
  iStructNamed Hkc'
  (try wp_auto)
  wp_apply (wp_seed cl ms V γs hAs hmsne) $$ [Hs] as %st0 %h0 %ok Hsd
  · iframe #
    iframe Hs
  icases Hsd with (%Hok | ⟨%Hok, Hs, Hst0, Hh0⟩)
  · subst Hok
    wp_auto
    iapply HΦ; ileft; ipureintro; rfl
  subst Hok
  wp_auto
  wp_apply wp_noStreaming as %b Hb
  cases b with
  | false =>
    wp_auto
    iapply HΦ; ileft; ipureintro; rfl
  | true =>
  ihave #Hrs : (k8s.rangeStreamOff : IProp GF) $$ [Hb]
  · iExactEq Hb; rfl
  wp_auto
  wp_apply wp_watchList as %b2 Hwl
  cases b2 with
  | false =>
    wp_auto
    iapply HΦ; ileft; ipureintro; rfl
  | true =>
  wp_auto
  haveI : go.UnderlyingEq k8s_io.apimachinery.pkg.runtime.Codec.ty
      k8s_io.apimachinery.pkg.runtime.Serializer.underlying :=
    ⟨(go.UnderlyingDirectedEq.underlying_unfold (t := k8s_io.apimachinery.pkg.runtime.Codec.ty)).trans
      go.UnderlyingDirectedEq.underlying_unfold⟩
  ihave #Pst : isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.etcd3 $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply wp_lmc as %lmc -
  (try wp_auto)
  ihave #Hctx := client_ctx_field cl (ms.map (·.addr)) V $$ [Hnc]
  · iexact Hnc
  ihave #Hpr : isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apimachinery.pkg.runtime $$ []
  · iPkgInit
  ihave #Hcon := hcon $$ [Hpr Hpd]
  · isplitl; iexact Hpr; iexact Hpd
  have e1 : interface.mkOk github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.codec.ty #(zero_val github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.codec) = codecI := rfl
  have e2 : interface.mkOk github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.identity.ty #(zero_val github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.identity) =
      GoInterface.ok identityI := rfl
  have e3 : interface.mkOk github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.decoder.ty #(zero_val github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.decoder) =
      GoInterface.ok decoderI := rfl
  have e4 : interface.mkOk github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.versioner.ty #(zero_val github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.versioner) =
      GoInterface.ok versionerI := rfl
  rw [e1, e2, e3, e4]
  have hpc : path.PathCleanAbs go!"/registry" := by unfold path.PathCleanAbs; decide
  wp_apply (wp_sNew DObj driverSpec kc cl ms V γh _ codecI _ func.nil func.nil go!"/registry"
      go!"/objs" ⟨[], go!"objs"⟩ versionerI identityI decoderI lmc hpc (by decide) (by decide)
      (by rfl) (by rfl) Htb (by rfl))
    as %sp %err Hnew
  · iframe #
    imodintro
    iintro %Φ' HΦ'
    wp_apply wp_newObj as %o Ho
    iapply HΦ'
    ihave %Hp := objAtD_ptr _ _ _ $$ Ho
    obtain ⟨p, -, rfl⟩ := Hp
    ipureintro
    exact reflectM.notRType_ptr _ _
  icases Hnew with ⟨%Herr, %mt, %lt, #Hstore, #Hw⟩
  subst Herr
  wp_auto
  ihave #Hwc := watchContractOk_driver wp_Decode wp_cDecode wp_Annotate wp_GetAnn wp_SetAnn $$ Hpd
  ihave #Hni := newItemOk_driver wp_newObj
  iapply HΦ
  iright
  isplitr
  · ipureintro; rfl
  isplitl [Hs]
  · iexact Hs
  isplitl [Hst0]
  · iExactEq Hst0; rfl
  isplitl [Hh0]
  · iExactEq Hh0; rfl
  isplitr
  · iexact Hrs
  isplitl [Hwl]
  · iExactEq Hwl; simp
  iexists sp, mt, lt
  isplitr
  · ipureintro; rfl
  unfold storeCfgD
  iframe Hstore
  imodintro
  iintro %γk #Hcw
  iapply Hw $$ Hcw Hwc Hni

end proof

end k8s_etcd3
end EtcdGrove
end Perennial
