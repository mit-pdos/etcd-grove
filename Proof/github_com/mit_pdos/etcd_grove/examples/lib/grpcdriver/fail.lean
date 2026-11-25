/- Lean-first (no Rocq counterpart).

# `fail`'s proof (the section status-roundtrip)

A fresh value (prefixed with `p` or not), `c.Fail(Background(), String(v))`: the handler never answers
(`failSpec` gives no reply), so the call fails, with a status or `io.EOF` (`checkErr`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.fail
public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.below
public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.freshValue
public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.checkErr
public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.svc.driverClient__Fail
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

theorem fail.wp_proof (wp_freshValue : freshValue.spec (GF := GF) (hG := hG))
    (wp_below : below.spec (GF := GF) (hG := hG))
    (wp_checkErr : checkErr.spec (GF := GF) (hG := hG))
    (wp_Fail : svc.driverClient.Fail.spec (GF := GF) (hG := hG))
    (wp_String : google_golang_org.protobuf.types.known.wrapperspb.String.spec (GF := GF) (hG := hG))
    (wp_Background : context.Background.spec (GF := GF) (hG := hG)) :
    fail.spec (GF := GF) (hG := hG) := by
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
  wp_apply wp_freshValue γid γb ids $$ [$Hpkg $Hctr $Hcred] as %v0 ⟨%id, %w, %Hv, -⟩
  obtain ⟨rfl, hw⟩ := Hv
  have hlen := mkVal_length id w hw
  try wp_auto
  wp_apply wp_below (W64 2) as %b -
  let cd : context.ContextDesc (IProp GF) :=
    { Values := ∅, Deadline := none, Done_gn := ⟨γid, γid⟩, PDone := iprop(True) }
  ihave #Hctx : ctxOk context.backgroundCtxVal cd $$ []
  · iapply ctxOk_of_quiet
    isplitl
    · iapply drv_ctxQuiet_background
    · iapply metadata.outgoingCtxOkC_background
  wp_if_destruct
  · try wp_auto
    try wp_auto
    wp_apply wp_Background
    try wp_auto
    wp_apply wp_String stringValueReqMax (go!"p" ++ mkVal id w) (by unfold stringValueReqMax; simp only [List.length_append, List.length_cons, List.length_nil]; omega) as %inp Hinp
    try wp_auto
    wp_apply (wp_Fail dc conn [drvAddr] failSpec (go!"p" ++ mkVal id w)
        (fun _ => iprop(False)) (fun _ => iprop(True))
        context.backgroundCtxVal cd none inp slice.nil []) $$ [Hinp]
      as %resp %err ⟨%out, Hout, %Hresp⟩
    · iframe #
      isplitl []
      · iapply metadata.outMD_background
      isplitl []
      · inext
        iintro %md -
        unfold failSpec
        itrivial
      isplitl [Hinp]
      · simp only [pbStringValueT, pbStringValue]
        iexact Hinp
      isplitl []
      · iapply (ownSlice_nil (V := GoInterface) DFrac.discard)
      ipureintro; intro v hv; cases hv
    unfold invokeOut
    icases Hout with (⟨-, %m', -, -, %Hfalse⟩ | ⟨⟨%Hne, -⟩, #Hse, -, -, -, #Hsh, -⟩)
    · exact Hfalse.elim
    · cases err with
    | nil => exact absurd rfl Hne
    | ok ei =>
      try wp_auto
      wp_apply wp_checkErr (GoInterface.ok ei) $$ []
      · iframe #
      iunfold drvFacts at Hf
      icases Hf with ⟨%f, #Hfg, #Hfwp⟩
      try wp_auto
      try wp_bind (App (Val #f) (Val _))
      iapply wp_wand $$ (Hfwp $$ %go!"status-roundtrip")
      iintro %u %Hu
      subst Hu
      try wp_auto
      iapply HΦ
      itrivial
  · try wp_auto
    wp_apply wp_Background
    try wp_auto
    wp_apply wp_String stringValueReqMax (mkVal id w) (by unfold stringValueReqMax; omega) as %inp Hinp
    try wp_auto
    wp_apply (wp_Fail dc conn [drvAddr] failSpec (mkVal id w)
        (fun _ => iprop(False)) (fun _ => iprop(True))
        context.backgroundCtxVal cd none inp slice.nil []) $$ [Hinp]
      as %resp %err ⟨%out, Hout, %Hresp⟩
    · iframe #
      isplitl []
      · iapply metadata.outMD_background
      isplitl []
      · inext
        iintro %md -
        unfold failSpec
        itrivial
      isplitl [Hinp]
      · simp only [pbStringValueT, pbStringValue]
        iexact Hinp
      isplitl []
      · iapply (ownSlice_nil (V := GoInterface) DFrac.discard)
      ipureintro; intro v hv; cases hv
    unfold invokeOut
    icases Hout with (⟨-, %m', -, -, %Hfalse⟩ | ⟨⟨%Hne, -⟩, #Hse, -, -, -, #Hsh, -⟩)
    · exact Hfalse.elim
    · cases err with
    | nil => exact absurd rfl Hne
    | ok ei =>
      try wp_auto
      wp_apply wp_checkErr (GoInterface.ok ei) $$ []
      · iframe #
      iunfold drvFacts at Hf
      icases Hf with ⟨%f, #Hfg, #Hfwp⟩
      try wp_auto
      try wp_bind (App (Val #f) (Val _))
      iapply wp_wand $$ (Hfwp $$ %go!"status-roundtrip")
      iintro %u %Hu
      subst Hu
      try wp_auto
      iapply HΦ
      itrivial

end proof

end github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver
end Perennial
