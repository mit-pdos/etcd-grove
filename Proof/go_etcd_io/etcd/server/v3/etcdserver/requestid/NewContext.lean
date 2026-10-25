/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/requestid/NewContext.lean` (PR etcd#21401).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.requestid.NewContext
public import Spec.context.WithValue

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.pkg.v3 go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.requestid.Assumptions]

theorem requestid.NewContext.wp_proof
    (hWV : context.WithValue.spec (GF := GF) (hG := hG)) :
    requestid.NewContext.spec (GF := GF) (hG := hG) := by
  intro ctx id
  wp_start as -
  ihave #Pctx : isPkgInit (PROP := IProp GF) pkg_id.context $$ []
  · iPkgInit
  wp_auto
  wp_apply hWV ctx ⟨requestid.requestIDKey.ty, #(zero_val requestid.requestIDKey)⟩
      (interface.mkOk go.uint64 #id) $$ []
    as %c ⟨%Hcnn, -, -, %c', %vs, %Hc, #Htx, #Hic, -, #Htr, #Hreq, -, #Hval⟩
  · iframe #
    ipureintro; right; right; right; right; right; rfl
  subst Hc
  iapply HΦ
  isplitr
  · ipureintro; exact Hcnn
  iexists c', vs
  isplitr
  · ipureintro; rfl
  iframe Htx Hic
  isplitr
  · imodintro
    iintro %o Htro
    iapply Htr $$ [] Htro
    ipureintro
    trivial
  isplitr
  · iapply Hreq $$ %id
    ipureintro; first | exact ⟨rfl, rfl⟩ | rfl
  imodintro
  iintro %n %x %Φ %Hn Hwp
  iapply Hval $$ [] Hwp
  ipureintro
  delta requestid.requestIDKey.ty
  intro h
  injection h with h1 _
  exact Hn h1.symm

end proof

end EtcdGrove
end Perennial
