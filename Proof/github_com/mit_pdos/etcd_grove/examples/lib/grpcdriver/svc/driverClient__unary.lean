/- Lean-first (no Rocq counterpart).

# `(*driverClient).unary`'s proof

`StaticMethod()` before the options, a fresh reply, one `Invoke` on the connection (`plain_Invoke`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.svc.driverClient__unary
public import Spec.google_golang_org.grpc.StaticMethod
public import Proof.github_com.mit_pdos.etcd_grove.PkgInitMemo

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode EtcdGrove github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver

namespace github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.svc

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.svc.Assumptions]
variable [pkg_wr : google_golang_org.protobuf.types.known.wrapperspb.Assumptions]

theorem driverClient.unary.wp_proof
    (wp_StaticMethod : grpc.StaticMethod.spec (GF := GF) (hG := hG))
    (wp_Invoke : grpc.ClientConn.Invoke.spec (GF := GF) (hG := hG)) :
    driverClient.unary.spec (GF := GF) (hG := hG) := by
  intro dc conn addrs Spec m Φ Ψe ctx cd om inp opts vs method
  wp_start as ⟨#Hcc, #Hconn, #Hrpc, #Hom, Hspec, #Hctx, Hsend, #Hopts, %Hvs⟩
  ihave #Hgrpc : isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc $$ []
  · iPkgInit
  try wp_auto
  wp_apply wp_StaticMethod as %sm ⟨#Hsm, %Hsms⟩
  wp_apply wp_slice_literal (V := GoInterface) [sm]
  isplitr
  · ipureintro; rfl
  iintro %sl_ptr ⟨Hsl, Hcap⟩
  try wp_auto
  wp_apply wp_slice_append $$ [$Hsl $Hcap $Hopts] as %copts ⟨Hco, Hcocap, -⟩
  try wp_auto
  ipersist Hco
  have hvs : ∀ v ∈ [sm] ++ vs, grpcOptOk [] v := by
    intro v hv
    rcases List.mem_append.1 hv with h | h
    · exact Or.inl (Hsms v h)
    · exact Hvs v h
  icases Hsend with ⟨%x, Hx, %Hx⟩
  ihave Hsend : (pbStringValueT (GF := GF)).send inp m $$ [Hx]
  · simp only [pbStringValueT, pbStringValue, stringValueSendB]
    iexists x; iframe; ipureintro; exact Hx
  have hw : (pbStringValueT (GF := GF)).wireLen m < grpcMsgMax := by
    simp only [pbStringValueT, pbStringValue, stringValueWireLen, grpcMsgMax, stringValueReqMax] at Hx ⊢
    omega
  ihave Hown : (pbStringValueRT (GF := GF)).own «$r0_ptr» $$ [«$r0»]
  · simp only [pbStringValueRT, pbStringValueR]
    iexists _; iexact «$r0»
  have hI := plain_Invoke wp_Invoke conn addrs method pbStringValueT pbStringValueRT
    pbStringValueT_reqReg pbStringValueRT_repReg Spec m Φ Ψe ctx cd om inp «$r0_ptr» copts ([sm] ++ vs)
  simp only [pbStringValueT, pbStringValueRT, pbStringValue, pbStringValueR] at hI
  wp_apply hI $$ [Hspec Hsend Hown] as %err ⟨-, Hout⟩
  · iframe #
    iframe
    isplitr
    · ipureintro; exact hw
    ipureintro; exact hvs
  try wp_auto
  wp_if_destruct
  · try wp_auto
    iapply HΦ
    iexists «$r0_ptr»
    iframe
    ipureintro; intro h; exact absurd h Hif
  · try wp_auto
    iapply HΦ
    iexists «$r0_ptr»
    iframe
    ipureintro; intro _; rfl

theorem driverClient.unary.wp_proof_done
    (wp_StaticMethod : grpc.StaticMethod.spec (GF := GF) (hG := hG))
    (wp_Invoke : grpc.ClientConn.Invoke.spec (GF := GF) (hG := hG)) :
    driverClient.unary.spec_done (GF := GF) (hG := hG) := by
  intro dc conn addrs ctx cd inp opts vs method
  wp_start as ⟨#Hcc, #Hconn, #Hom, Hdone, #Hctx, #Hopts, %Hvs⟩
  ihave #Hgrpc : isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc $$ []
  · iPkgInit
  try wp_auto
  wp_apply wp_StaticMethod as %sm ⟨#Hsm, %Hsms⟩
  wp_apply wp_slice_literal (V := GoInterface) [sm]
  isplitr
  · ipureintro; rfl
  iintro %sl_ptr ⟨Hsl, Hcap⟩
  try wp_auto
  wp_apply wp_slice_append $$ [$Hsl $Hcap $Hopts] as %copts ⟨Hco, Hcocap, -⟩
  try wp_auto
  ipersist Hco
  have hvs : ∀ v ∈ [sm] ++ vs, grpcOptOk [] v := by
    intro v hv
    rcases List.mem_append.1 hv with h | h
    · exact Or.inl (Hsms v h)
    · exact Hvs v h
  wp_apply (plain_Invoke_done wp_Invoke conn addrs method ctx cd _ _ copts ([sm] ++ vs)) $$ [Hdone]
    as %err ⟨%Herr, #Hse, #Hcode⟩
  · iframe #
    iframe
    ipureintro; exact hvs
  try wp_auto
  wp_if_destruct
  · try wp_auto
    iapply HΦ
    iframe #
    ipureintro; exact Herr
  · try wp_auto
    iapply HΦ
    iframe #
    ipureintro; exact Herr

end proof

end github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.svc
end Perennial
