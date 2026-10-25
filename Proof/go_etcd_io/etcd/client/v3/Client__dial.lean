/-
Proof of `Spec/go_etcd_io/etcd/client/v3/Client__dial.lean` (item 5, client construction;
updated for PR #21765's `dialWithContext`). Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.Client__dial
public import Spec.go_etcd_io.etcd.client.v3.Client__dialSetupOpts
public import Spec.go_etcd_io.etcd.client.v3.authority
public import Spec.google_golang_org.grpc.NewClient
public import Spec.fmt.SprintfClientPtr

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

omit [FfiInterp ffi] [FfiSemantics ext ffi] hG sem package_sem in
/-- `Sprintf("%s://%p/%s/%s", x, ...)` begins with `x` and `://`. -/
theorem sprintf_scheme_prefix [GoSemanticsFunctions] [go.IntoValInj GoString] (x : GoString)
    (args : List GoInterface) (out : GoString)
    (h : _root_.Perennial.fmt.SprintfOut go!"%s://%p/%s/%s" (interface.mkOk go.string #x :: args)
      out) :
    (x ++ go!"://") <+: out := by
  have hf : go!"%s://%p/%s/%s" = W8 37 :: W8 115 :: go!"://%p/%s/%s" := rfl
  rw [hf] at h
  obtain ⟨o1, rfl, h1⟩ := _root_.Perennial.fmt.SprintfOut.str_inv h
  have hf1 : go!"://%p/%s/%s" = W8 58 :: W8 47 :: W8 47 :: go!"%p/%s/%s" := rfl
  rw [hf1] at h1
  obtain ⟨o2, rfl, h2⟩ := _root_.Perennial.fmt.SprintfOut.byte_inv (by decide) h1
  obtain ⟨o3, rfl, h3⟩ := _root_.Perennial.fmt.SprintfOut.byte_inv (by decide) h2
  obtain ⟨o4, rfl, -⟩ := _root_.Perennial.fmt.SprintfOut.byte_inv (by decide) h3
  exact ⟨o4, by simp⟩

theorem Client.dial.wp_proof
    (wp_dialSetupOpts : Client.dialSetupOpts.spec (GF := GF) (hG := hG))
    (wp_authority : authority.spec (GF := GF) (hG := hG))
    (wp_NewClient : grpc.NewClient.spec (GF := GF) (hG := hG))
    (wp_Sprintf : fmt.SprintfClientPtr.spec (GF := GF) (hG := hG)) :
    Client.dial.spec (GF := GF) (hG := hG) := by
  intro c ctx key targetEndpoint cfg cr sl rb eps
  wp_start as ⟨#Hc, #Hcfg, #Hdo, #Hatb, %Hp1, #Hds, Hrb⟩
  ihave #Hgrpc : isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc $$ []
  · iPkgInit
  ihave #Hfmt : isPkgInit (PROP := IProp GF) pkg_id.fmt $$ []
  · iPkgInit
  wp_auto
  wp_apply wp_dialSetupOpts c cfg cr sl [.resolvers [rb]] $$ [$Hc $Hcfg $Hds]
    as %o1 ⟨%si, %ic, #Ho1, Ho1c, %Hsi, #Hic, #HicW⟩
  iunfold dialOptsAt at Ho1
  icases Ho1 with ⟨%os1, #Hos1, %Hos1⟩
  iStructNamed Hcfg
  wp_auto
  wp_apply wp_slice_append_dfrac (V := GoInterface) o1 os1 DFrac.discard cfg.DialOptions' []
    DFrac.discard $$ [$Hos1 $Ho1c $Hdo] as %o2 ⟨#Ho2, Ho2c, -⟩
  · ipureintro; exact DFrac.valid_discard
  wp_apply wp_authority targetEndpoint as %a -
  · ipureintro; exact Hp1
  wp_apply wp_slice_literal (V := GoInterface)
    [interface.mkOk go.string go_etcd_io.etcd.client.v3.internal.resolver.Schema,
      interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.v3.Client.ty) #c,
      interface.mkOk go.string #key,
      interface.mkOk go.string #a]
  isplitr
  · ipureintro; rfl
  iintro %al ⟨Hal, -⟩
  wp_apply wp_Sprintf _ _ _ (DFrac.own 1) $$ [$Hal] as %tgt ⟨-, %Hout⟩
  · ipureintro
    intro x hx
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · left
      exact _root_.Perennial.fmt.ArgsWf.cons_string go!"etcd-endpoints" []
        _root_.Perennial.fmt.ArgsWf.nil _ (List.mem_singleton_self _)
    · right; rfl
    · left
      exact _root_.Perennial.fmt.ArgsWf.cons_string key [] _root_.Perennial.fmt.ArgsWf.nil _
        (List.mem_singleton_self _)
    · left
      exact _root_.Perennial.fmt.ArgsWf.cons_string a [] _root_.Perennial.fmt.ArgsWf.nil _
        (List.mem_singleton_self _)
  have Hpre := sprintf_scheme_prefix go!"etcd-endpoints" _ tgt Hout
  have Hdok0 : dialOk ([GrpcDialOpt.resolvers [rb]] ++
      [.transportCreds, .streamInterceptor si, .unaryInterceptor ic]) rb := by
    refine ⟨?_, ?_, by simp⟩
    · intro si' h
      simp at h
      rw [h]; exact Hsi
    · intro rbs h
      simp at h
      exact h
  have Hdok : dialOk (kaOpts cfg ++ [GrpcDialOpt.resolvers [rb]] ++
      [.transportCreds, .streamInterceptor si, .unaryInterceptor ic]) rb := by
    rw [List.append_assoc]; exact dialOk_kaOpts cfg _ rb Hdok0
  wp_apply wp_NewClient tgt o2 _ rb etcdScheme eps Hdok $$ [$Hgrpc $Hrb] as %conn %err Hres
  · isplitr
    · iunfold dialOptsAt
      iexists _
      iframe Ho2
      ipureintro
      rw [List.append_nil]; exact Hos1
    · ipureintro; exact Hpre
  iapply HΦ
  icases Hres with (⟨%Herr, #Hconn⟩ | %Herr)
  · ileft
    isplitr
    · ipureintro; exact Herr
    have Hics : unaryIcsOf (kaOpts cfg ++ [GrpcDialOpt.resolvers [rb]] ++
        [.transportCreds, .streamInterceptor si, .unaryInterceptor ic]) = [ic] := by
      rw [List.append_assoc, unaryIcsOf_kaOpts]; rfl
    iunfold isEtcdConn
    iexists ic
    iframe Hic HicW
    rw [← Hics]
    iexact Hconn
  · iright
    ipureintro; exact Herr

end proof

end EtcdGrove
end Perennial
