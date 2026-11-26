/- Lean-first (no Rocq counterpart).

# `canceled`'s proof (the section ctx-canceled)

`WithCancel(Background())`, `cancel()`: the context's `Err()` is `Canceled` (`spec_canceled`, the interim
context axiom), so the call fails at once with a status of code `Canceled` (`spec_done`, over
`grpcInvokerDone`), which `status.Code` returns.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.canceled
public import Spec.context.WithCancelBackground
public import Spec.google_golang_org.grpc.status.Code
public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.freshValue
public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.checkErr
public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.svc.driverClient__Echo
public import Spec.google_golang_org.protobuf.types.known.wrapperspb.String
public import Perennial.Spec.context.Background
public import Proof.context.LibKeysChain
public import Proof.github_com.mit_pdos.etcd_grove.PkgInitMemo

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode EtcdGrove

namespace github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : Assumptions]
variable [pkg_wr : google_golang_org.protobuf.types.known.wrapperspb.Assumptions]

theorem canceled.wp_proof (wp_freshValue : freshValue.spec (GF := GF) (hG := hG))
    (wp_EchoDone : svc.driverClient.Echo.spec_done (GF := GF) (hG := hG))
    (wp_String : google_golang_org.protobuf.types.known.wrapperspb.String.spec (GF := GF) (hG := hG))
    (wp_Background : context.Background.spec (GF := GF) (hG := hG))
    (wp_WithCancel : context.WithCancelBackground.spec_canceled (GF := GF) (hG := hG))
    (wp_Code : status.Code.spec (GF := GF) (hG := hG)) :
    canceled.spec (GF := GF) (hG := hG) := by
  intro γid γb c ids
  wp_start as ⟨#Hcli, Hcred⟩
  iunfold drvCli at Hcli
  icases Hcli with ⟨#Hpkg, #Hf, #Hctr, %conn, #Hstub, #Hconn, #Hecho, #Hfail, #Hmeta⟩
  iunfold drvStubAt at Hstub
  icases Hstub with ⟨%dc, %Hc, #Hcc⟩
  subst Hc
  ihave #Hsvc : isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.svc $$ []
  · iPkgInit
  ihave #Hctxp : isPkgInit (PROP := IProp GF) pkg_id.context $$ []
  · iPkgInit
  ihave #Hst : isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc.status $$ []
  · iPkgInit
  wp_auto
  wp_apply wp_Background
  try wp_auto
  wp_apply wp_WithCancel as %ctx' %γ' %cancel ⟨#Hcs, #Hisc, #Hbg, #Hcc', #Hcanc⟩
  try wp_auto
  try wp_bind (App (Val #cancel) (Val _))
  iapply Hcanc
  inext
  iintro #Herr
  try wp_auto
  wp_apply wp_freshValue γid γb ids $$ [$Hpkg $Hctr $Hcred] as %v ⟨%id, %w, %Hv, -⟩
  obtain ⟨rfl, hw⟩ := Hv
  have hlen := mkVal_length id w hw
  try wp_auto
  wp_apply wp_String stringValueReqMax (mkVal id w) (by unfold stringValueReqMax; omega) as %inp -
  try wp_auto
  let cd : context.ContextDesc (IProp GF) :=
    { Values := ∅, Deadline := none, Done_gn := γ', PDone := iprop(True) }
  iunfold context.bgCancelChild at Hbg
  icases Hbg with ⟨%cc, %Hcceq, #Hfield⟩
  subst Hcceq
  ihave #Hfrom := _root_.Perennial.context.ctxValueFrom_cancel cc _root_.Perennial.context.backgroundCtxVal $$ Hfield
  ihave #Hom := metadata.outMD_bgFrom _ $$ Hfrom
  ihave #Hog := metadata.outgoingCtxOkC_bgFrom _ $$ Hfrom
  ihave #Hok : ctxOk (interface.mk (go.GoType.PointerType _root_.Perennial.context.cancelCtx.ty) #cc) cd $$ []
  · iapply ctxOk_of_isContext
    iframe #
  wp_apply (wp_EchoDone dc conn [drvAddr] _ cd inp slice.nil []) $$ []
    as %resp %err ⟨%Herr', #Hse, #Hcode⟩
  · iframe #
    isplitl []
    · ileft
      unfold ctxCanceledIs
      iunfold EtcdGrove.context.errIsCanceled at Herr
      icases Herr with ⟨%e, #He, #HeWP⟩
      iexists cd, e
      iframe #
    isplitl []
    · iapply (ownSlice_nil (V := GoInterface) DFrac.discard)
    ipureintro; intro v hv; cases hv
  try wp_auto
  wp_apply wp_Code err (W32 1) $$ []
  · iframe #
  try wp_auto
  iunfold drvFacts at Hf
  icases Hf with ⟨%f, #Hfg, #Hfwp⟩
  try wp_auto
  try wp_bind (App (Val #f) (Val _))
  iapply wp_wand $$ (Hfwp $$ %go!"ctx-canceled")
  iintro %u %Hu
  subst Hu
  try wp_auto
  iapply HΦ
  itrivial

end proof

end github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver
end Perennial
