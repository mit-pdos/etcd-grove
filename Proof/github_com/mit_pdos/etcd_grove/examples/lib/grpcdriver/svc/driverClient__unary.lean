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
  intro dc conn addrs Spec m Φr Ψe ctx cd om inp opts vs method
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
  icases pbStringValueT_send_wire inp m $$ Hsend with ⟨Hsend, %hw⟩
  ihave Hown : (pbStringValueRT (GF := GF)).own «$r0_ptr» $$ [«$r0»]
  · simp only [pbStringValueRT, pbStringValueR]
    iexists _; iexact «$r0»
  have hI := plain_Invoke wp_Invoke conn addrs method pbStringValueT pbStringValueRT
    pbStringValueT_reqReg pbStringValueRT_repReg Spec m Φr Ψe ctx cd om inp «$r0_ptr» copts ([sm] ++ vs)
    Msg.ty Msg.ty rfl rfl
  wp_apply hI $$ [Hspec Hsend Hown] as %err ⟨-, Hout⟩
  · iframe #
    iframe
    ipureintro; exact ⟨hw, hvs⟩
  cases err with
  | nil =>
    try wp_auto
    iapply HΦ
    iexists «$r0_ptr»
    iframe
    ipureintro; intro _; rfl
  | ok e =>
    try wp_auto
    iapply HΦ
    iexists «$r0_ptr»
    iframe
    ipureintro; intro h; cases h

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
  have hD := plain_Invoke_done wp_Invoke conn addrs method ctx cd
      (interface.mkOk (go.GoType.PointerType google_golang_org.protobuf.types.known.wrapperspb.StringValue.ty) #inp : GoInterface)
      (interface.mkOk (go.GoType.PointerType google_golang_org.protobuf.types.known.wrapperspb.StringValue.ty) #«$r0_ptr» : GoInterface) copts ([sm] ++ vs)
  try simp only [Msg.ty]
  wp_apply hD $$ [Hdone] as %err ⟨%Herr, #Hse, #Hcode⟩
  · iframe #
    iframe
    ipureintro; exact hvs
  cases err with
  | nil => exact absurd rfl Herr.1
  | ok e =>
    try wp_auto
    iapply HΦ
    iframe #
    ipureintro; exact Herr

end proof

end github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.svc
end Perennial
