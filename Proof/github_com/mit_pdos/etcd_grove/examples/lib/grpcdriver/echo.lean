/- Lean-first (no Rocq counterpart).

# `echo`'s proof (the section unary-reply)

A fresh value with its id's token, `c.Echo(Background(), String(v))` on the plain connection: on
success the reply is `v ++ "#1"` (`echoSpec`: the handler's run is the value's first), so the check
passes; otherwise the error is a status or `io.EOF` (`checkErr`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.echo
public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.freshValue
public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.checkErr
public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.svc.driverClient__Echo
public import Spec.google_golang_org.protobuf.types.known.wrapperspb.String
public import Perennial.Spec.context.Background
public import Proof.go_etcd_io.etcd.client.v3.InvServerKV
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

theorem echo.wp_proof (wp_freshValue : freshValue.spec (GF := GF) (hG := hG))
    (wp_checkErr : checkErr.spec (GF := GF) (hG := hG))
    (wp_Echo : svc.driverClient.Echo.spec (GF := GF) (hG := hG))
    (wp_String : google_golang_org.protobuf.types.known.wrapperspb.String.spec (GF := GF) (hG := hG))
    (wp_Background : context.Background.spec (GF := GF) (hG := hG)) :
    echo.spec (GF := GF) (hG := hG) := by
  intro γid γb c ids
  wp_start as ⟨#Hcli, Hcred⟩
  iunfold drvCli at Hcli
  icases Hcli with ⟨#Hpkg, #Hf, #Hctr, %conn, #Hstub, #Hconn, #Hecho, #Hfail, #Hmeta⟩
  iunfold drvStubAt at Hstub
  icases Hstub with ⟨%dc, %Hc, #Hcc⟩
  subst Hc
  ihave #Hsvc : isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.svc $$ []
  · iPkgInit
  ihave #Hgrpc : isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc $$ []
  · iPkgInit
  wp_auto
  wp_apply wp_freshValue γid γb ids $$ [$Hpkg $Hctr $Hcred] as %v ⟨%id, %w, %Hv, Htok⟩
  obtain ⟨rfl, hw⟩ := Hv
  have hlen := mkVal_length id w hw
  try wp_auto
  wp_apply wp_Background
  try wp_auto
  wp_apply wp_String stringValueReqMax (mkVal id w) (by unfold stringValueReqMax; omega) as %inp Hinp
  try wp_auto
  let cd : context.ContextDesc (IProp GF) :=
    { Values := ∅, Deadline := none, Done_gn := ⟨γid, γid⟩, PDone := iprop(True) }
  ihave #Hctx : ctxOk context.backgroundCtxVal cd $$ []
  · iapply ctxOk_of_quiet
    isplitl
    · iapply EtcdGrove.client.ctxQuiet_background
    · iapply metadata.outgoingCtxOkC_background
  wp_apply (wp_Echo dc conn [drvAddr] (echoSpec γid) (mkVal id w)
      (fun r => iprop(⌜r = mkVal id w ++ go!"#1"⌝)) (fun _ => iprop(True))
      context.backgroundCtxVal cd none inp slice.nil []) $$ [Htok Hinp]
    as %resp %err ⟨%out, Hout, %Hresp⟩
  · iframe #
    isplitl []
    · iapply metadata.outMD_background
    isplitl [Htok]
    · inext
      iintro %md -
      unfold echoSpec
      iexists id, w
      iframe Htok
      ipureintro; exact ⟨⟨rfl, hw⟩, rfl⟩
    isplitl [Hinp]
    · simp only [pbStringValueT, pbStringValue]
      iexact Hinp
    isplitl []
    · iapply (ownSlice_nil (V := GoInterface) DFrac.discard)
    ipureintro; intro v hv; cases hv
  unfold invokeOut
  icases Hout with (⟨%He, %m', Hrecv, -, %Hm'⟩ | ⟨⟨%Hne, -⟩, #Hse, -, -, -, #Hsh, -⟩)
  · subst He
    have hr := Hresp rfl
    subst hr
    subst Hm'
    simp only [pbStringValueRT, pbStringValueR]
    icases Hrecv with ⟨%Hnn, -, #Hval⟩
    try wp_auto
    iunfold drvFacts at Hf
    icases Hf with ⟨%f, #Hfg, #Hfwp⟩
    try wp_auto
    try wp_bind (App (Val #f) (Val _))
    iapply wp_wand $$ (Hfwp $$ %go!"unary-reply")
    iintro %u %Hu
    subst Hu
    try wp_auto
    iapply HΦ
    itrivial
  · cases err with
    | nil => exact absurd rfl Hne
    | ok ei =>
      try wp_auto
      wp_apply wp_checkErr (GoInterface.ok ei) $$ []
      · iframe #
        iunfold drvFacts at Hf
        iexact Hf
      try wp_auto
      iapply HΦ
      itrivial

end proof

end github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver
end Perennial
