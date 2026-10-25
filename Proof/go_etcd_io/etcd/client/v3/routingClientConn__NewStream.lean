/-
Proof of `Spec/go_etcd_io/etcd/client/v3/routingClientConn__NewStream.lean` (PR #21765).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.routingClientConn__NewStream

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

theorem routingClientConn.NewStream.wp_proof
    (wp_connForCtx : Client.connectionForContext.spec (GF := GF) (hG := hG))
    (wp_NewStream : grpc.ClientConn.NewStream.spec (GF := GF) (hG := hG)) :
    routingClientConn.NewStream.spec (GF := GF) (hG := hG) := by
  intro rcc cl mu mref dq0 dq1 chs o addrs ics method Req Rep Up Spec ctx cd desc opts vs
  wp_start as ⟨Hrcc, Hmu, Hrw, #Hck, Hrest⟩
  ihave #Hgrpc : isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc $$ []
  · iPkgInit
  wp_auto
  wp_apply wp_connForCtx cl mu mref dq1 chs (GoInterface.ok ctx) o $$ [$Hmu $Hrw $Hck]
    as %conn %err ⟨Hmu, Hrw, Hres⟩
  by_cases hc : poolConnFor chs o = null
  · simp only [hc, ↓reduceIte]
    icases Hres with ⟨%Hconn, %e, %Herr, #HeS⟩
    subst Hconn Herr
    wp_auto
    iapply HΦ
    iframe Hrcc Hmu Hrw
    isplitr
    · ipureintro; trivial
    iexists e
    iframe HeS
    ipureintro; rfl
  · simp only [hc, ↓reduceIte]
    icases Hres with %Hce
    obtain ⟨rfl, rfl⟩ := Hce
    icases Hrest with ⟨#Hconn, #Hstr, #Hctx, #Hdesc, #Hopts, #Hok⟩
    wp_auto
    wp_apply wp_NewStream (poolConnFor chs o) addrs ics method Req Rep Up Spec ctx cd desc opts vs
      $$ [$Hgrpc $Hconn $Hstr $Hctx $Hdesc $Hopts $Hok] as %cs %err' Hout
    iapply HΦ
    iframe Hrcc Hmu Hrw Hout

end proof

end EtcdGrove
end Perennial
