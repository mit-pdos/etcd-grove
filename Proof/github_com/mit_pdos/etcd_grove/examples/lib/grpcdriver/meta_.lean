/- Lean-first (no Rocq counterpart).

# `meta`'s proof (the section metadata)

`n < 4` random words appended to a `WithCancel(Background())` context's outgoing metadata at `mdKeyS`
(`AppendToOutgoingContext`: `mdAdd`), then `c.Meta`: the handler sees an attempt's metadata, which
with no per-RPC credentials (`connCredsOk conn []`) is at `mdKeyS` the caller's (`grpcAttemptMd`; the
key is not reserved), so the reply is the words joined by `","` (`metaSpec`), which the check
compares with `strings.Join` of the same words; otherwise the error is a status or `io.EOF`
(`checkErr`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.meta_
public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.below
public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.randomWord
public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.checkErr
public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.svc.driverClient__Meta
public import Spec.google_golang_org.protobuf.types.known.wrapperspb.String
public import Spec.google_golang_org.grpc.metadata.AppendToOutgoingContext
public import Spec.context.WithCancelBackground
public import Perennial.Spec.context.Background
public import Perennial.Proof.strings.JoinBounded
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

theorem mdKeyS_notReserved : ¬ grpcReservedKey mdKeyS := by
  unfold grpcReservedKey mdKeyS; decide

theorem «meta».wp_proof (wp_below : below.spec (GF := GF) (hG := hG))
    (wp_randomWord : randomWord.spec (GF := GF) (hG := hG))
    (wp_checkErr : checkErr.spec (GF := GF) (hG := hG))
    (wp_Meta : svc.driverClient.Meta.spec (GF := GF) (hG := hG))
    (wp_String : google_golang_org.protobuf.types.known.wrapperspb.String.spec (GF := GF) (hG := hG))
    (wp_Background : context.Background.spec (GF := GF) (hG := hG))
    (wp_WithCancel : context.WithCancelBackground.spec_canceled (GF := GF) (hG := hG))
    (wp_Append : metadata.AppendToOutgoingContext.spec (GF := GF) (hG := hG))
    (wp_Join : _root_.Perennial.strings.Join.spec (GF := GF) (hG := hG)) :
    «meta».spec (GF := GF) (hG := hG) := by
  intro γid γb c ids
  wp_start as #Hcli
  iunfold drvCli at Hcli
  icases Hcli with ⟨#Hpkg, #Hf, #Hctr, %conn, #Hstub, #Hconn, #Hecho, #Hfail, #Hmeta, #Hstrm,
    #Hcreds⟩
  iunfold drvStubAt at Hstub
  icases Hstub with ⟨%dc, %Hc, #Hcc⟩
  subst Hc
  ihave #Hsvc : isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.svc $$ []
  · iPkgInit
  ihave #Hctxp : isPkgInit (PROP := IProp GF) pkg_id.context $$ []
  · iPkgInit
  ihave #Hmdp : isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc.metadata $$ []
  · iPkgInit
  ihave #Hstrs : isPkgInit (PROP := IProp GF) pkg_id.strings $$ []
  · iPkgInit
  wp_auto
  wp_apply wp_below (W64 4) as %n %Hn
  have hn : uint.Z n < 4 := Hn.2 (by decide)
  try wp_auto
  wp_apply wp_Background
  try wp_auto
  wp_apply wp_WithCancel as %ctx' %γ' %cancel ⟨#Hcs, #Hisc, #Hbg, #Hcc', #Hcanc⟩
  try wp_auto
  iunfold context.bgCancelChild at Hbg
  icases Hbg with ⟨%cc, %Hcceq, #Hfield⟩
  subst Hcceq
  ihave #Hfrom := _root_.Perennial.context.ctxValueFrom_cancel cc _root_.Perennial.context.backgroundCtxVal $$ Hfield
  ihave #Hom0 := metadata.outMD_bgFrom _ $$ Hfrom
  ihave #HogC0 := metadata.outgoingCtxOkC_bgFrom _ $$ Hfrom
  ihave #Hlib0 := context.libCtxOk_bgFrom _ $$ [$Hctxp $Hfrom]
  ihave #Hog0 := context.outgoingCtxOk_of_libCtxOk _ $$ Hlib0
  ihave Hnil : (slice.nil : GoSlice) ↦* ([] : List GoString) $$ []
  · iapply ownSlice_nil
  ihave Hnilc : ownSliceCap GoString slice.nil (DFrac.own 1) $$ []
  · iapply ownSliceCap_nil
  ihave IH : (∃ (k : w64) (s : GoSlice) (ci : GoInterfaceOk) (cdv : context.ContextDesc (IProp GF))
      (om : GrpcMd) (vals : List GoString),
      "i" ∷ i_ptr ↦ k ∗ "vals" ∷ vals_ptr ↦ s ∗ "Hsl" ∷ s ↦* vals ∗
      "Hcap" ∷ ownSliceCap GoString s (DFrac.own 1) ∗
      "ctx" ∷ ctx_ptr ↦ (GoInterface.ok ci) ∗
      "#Hisc" ∷ context.isContext ci cdv ∗ "#Hog" ∷ metadata.outgoingCtxOk ci ∗
      "#HogC" ∷ metadata.outgoingCtxOkC ci ∗ "#Hom" ∷ metadata.outMD ci om ∗
      "%Hk" ∷ ⌜metadata.mdVals om mdKeyS = vals ∧ (∀ w ∈ vals, wordOk w) ∧
        vals.length = uint.nat k ∧ uint.Z k ≤ uint.Z n⌝ : IProp GF)
      $$ [i vals ctx Hnil Hnilc]
  · iexists W64 0, slice.nil, _, _, none, []
    iframe
    iframe #
    ipureintro
    refine ⟨by simp [metadata.mdVals], by simp, by simp, by word⟩
  wp_for IH
  wp_if_destruct
  · wp_apply wp_randomWord as %w %hw
    try wp_auto
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %osl ⟨Hosl, -⟩
    try wp_auto
    wp_apply wp_slice_append $$ [$Hsl $Hcap $Hosl] as %s1 ⟨Hsl, Hcap, -⟩
    try wp_auto
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %ksl ⟨Hksl, -⟩
    try wp_auto
    wp_apply wp_Append ci cdv _ (DFrac.own 1) mdKeyS w om (by unfold metadata.lowerKey; decide)
      $$ [Hksl] as %c' ⟨%ci', %vs', %Hc', #Hisc', #Hog', #HogC', #Hom', -⟩
    · iframe; iframe #
    subst Hc'
    try wp_auto
    wp_for_post
    iframe
    iexists k + W64 1, s1, ci', { cdv with Values := vs' }, metadata.mdAdd om mdKeyS w, vals ++ [w]
    iframe
    iframe #
    ipureintro
    obtain ⟨h1, h2, h3, h4⟩ := Hk
    have hk : uint.Z k < uint.Z n := by first | word | simpa using Hif | (simp at Hif; word)
    refine ⟨by rw [metadata.mdVals_mdAdd, h1], ?_, ?_, by word⟩
    · intro x hx
      rcases List.mem_append.1 hx with hx | hx
      · exact h2 x hx
      · simp at hx; subst hx; exact hw
    · simp only [List.length_append, List.length_singleton, h3]; word
  · try wp_auto
    obtain ⟨h1, h2, h3, h4⟩ := Hk
    have hlen3 : vals.length ≤ 3 := by rw [h3]; word
    have hB : ∀ x ∈ vals, x.length ≤ 16 := fun x hx => (h2 x hx).1
    have hJ := strings.length_intercalate_le go!"," vals 16 hB
    have hmul : vals.length * (16 + (go!",").length) ≤ 3 * 17 := by
      have : (go!",").length = 1 := rfl
      rw [this]; exact Nat.mul_le_mul_right _ hlen3
    have hJlen : (go!",".intercalate vals).length < stringValueMax := by
      unfold stringValueMax; omega
    wp_apply wp_String stringValueReqMax go!"" (by unfold stringValueReqMax; decide) as %inp Hinp
    try wp_auto
    ihave #Hok : ctxOk ci cdv $$ []
    · iapply ctxOk_of_isContext
      iframe #
    wp_apply (wp_Meta dc conn [drvAddr] metaSpec go!""
        (fun r => iprop(⌜r = go!",".intercalate vals⌝)) (fun _ => iprop(True))
        ci cdv om inp slice.nil []) $$ [Hinp]
      as %resp %err ⟨%out, Hout, %Hresp⟩
    · iframe #
      isplitl []
      · inext
        iintro %md #Hatt
        unfold metaSpec grpcAttemptMd
        icases Hatt with ⟨%cm, #Hcy, %Hmd⟩
        unfold connCredsOk
        ihave %Hcm := Hcreds $$ %cm Hcy
        subst Hcm
        have hv : metadata.mdVals md mdKeyS = vals := by
          rw [Hmd.1 mdKeyS mdKeyS_notReserved, h1]; simp [metadata.mdVals]
        rw [hv]
        isplitr
        · ipureintro; exact hJlen
        ipureintro; rfl
      isplitl [Hinp]
      · simp only [pbStringValueT, pbStringValue]
        iexact Hinp
      isplitl []
      · iapply (ownSlice_nil (V := GoInterface) DFrac.discard)
      ipureintro; intro v hv; cases hv
    try wp_auto
    try wp_bind (App (Val #cancel) (Val _))
    iapply Hcanc
    inext
    iintro -
    try wp_auto
    unfold invokeOut
    icases Hout with (⟨%He, %m', Hrecv, -, %Hm'⟩ | ⟨⟨%Hne, -⟩, #Hse, -, -, -, #Hsh, -⟩)
    · subst He
      have hr := Hresp rfl
      subst hr
      subst Hm'
      simp only [pbStringValueRT, pbStringValueR]
      icases Hrecv with ⟨%Hnn, -, #Hval⟩
      try wp_auto
      wp_apply (strings.Join_bounded_of wp_Join s vals (DFrac.own 1) go!"," 16 hB
        (by unfold strings.joinMax; omega)) $$ [Hsl] as Hsl
      · iframe #; iframe
      try wp_auto
      iunfold drvFacts at Hf
      icases Hf with ⟨%f, #Hfg, #Hfwp⟩
      try simp only [decide_true]
      try wp_auto
      try wp_bind (App (Val #f) (Val _))
      iapply wp_wand $$ (Hfwp $$ %go!"metadata")
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
        try wp_auto
        iapply HΦ
        itrivial

end proof

end github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver
end Perennial
