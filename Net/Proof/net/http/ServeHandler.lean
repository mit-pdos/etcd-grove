/-
The proof of `http.Serve` with a handler (`Net/Spec/net/http/ServeHandler.lean`): the new server
`&Server{Handler: h}` split into its fields (its mutex made, over `srvMuInv`'s two `nil` maps), the
read-only ones kept (`srvConst`, `srvDflt`, `srvServe`, `srvServeRest`), the server's handler on each
address's connections from `h`'s (`srvHandler_intro`), then `Server.Serve`.
-/
module

public import Net.Spec.net.http.ServeHandler
public import Net.Spec.net.http.Server__Serve
public import Net.Proof.net.http.ServeLoopLemmas

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace net.http

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [package_sem' : net.http.Assumptions]
variable [π : NetProtoGS]

attribute [local instance] GooseGlobalGS.gooseInvGS

theorem Serve.wp_proofHandler (wp_Serve : Server.Serve.spec (GF := GF) (hG := hG)) :
    Serve.specHandler (GF := GF) (hG := hG) := by
  intro h lis l la P Q path hpath hlen
  wp_start as ⟨#Henv, #Hre, #Hse, #Hctxi, #Hlogi, #Htime, #Hsync, #Hatomic, #Hkeys, #Hwp, #Hrp,
    #Htm, #Haddrs, #Hlis, #Hon, #Hli⟩
  try wp_auto
  icases typedPointsto_split _ _ _ $$ «$r0» with S
  simp only [TypedPointsto.typedPointstoDef, named]
  icases S with ⟨-, Hh, Hdg, Htls, Hrt, Hrht, Hwt, -, Hmhb, Hmhvc, Htnp, Hcs, Hel, Hbc, Hcc, -, Hpr,
    -, Hsd, -, Hnpo, Hnpe, Hmu, Hls, Hac, -, -, -, -, -, Hlg, -⟩
  ipersist Hh
  ipersist Hdg
  ipersist Htls
  ipersist Hrt
  ipersist Hrht
  ipersist Hwt
  ipersist Hmhb
  ipersist Hmhvc
  ipersist Htnp
  ipersist Hcs
  ipersist Hel
  ipersist Hbc
  ipersist Hcc
  ipersist Hpr
  ipersist Hsd
  imod sync.init_Mutex (srvMuInv (GF := GF) «$r0_ptr») ⊤
    (structFieldRef net.http.Server go!"mu" «$r0_ptr») $$ Hmu [Hls Hac] with #Hmux
  · inext
    iunfold srvMuInv
    iunfold mapField
    isplitl [Hac]
    · iexists _; iframe Hac; ileft; ipureintro; rfl
    · iexists _; iframe Hls; ileft; ipureintro; rfl
  ihave #Hsc : srvConst (GF := GF) «$r0_ptr» $$ []
  · iunfold srvConst; iframe #
  ihave #Hsdf : srvDflt (GF := GF) «$r0_ptr» $$ []
  · iunfold srvDflt
    simp only [show (W64 0 : w64) = 0 from rfl]
    iframe #
  ihave #Hss : srvServe (GF := GF) «$r0_ptr» $$ []
  · iunfold srvServe
    simp only [show (W64 0 : w64) = 0 from rfl, map.nil]
    iframe #
    rw [sync.atomic.ownBool_unseal]; unfold sync.atomic.ownBoolDef
    have hz : (_root_.Perennial.zero_val sync.atomic.Bool') =
        { «_#0'» := _root_.Perennial.zero_val _, v' := sync.atomic.b32w false : sync.atomic.Bool' } :=
      rfl
    rw [← hz]
    iexact Hsd
  ihave #Hsa : □ (∀ a, ⌜addrOk a = true ∧ lisAccepts la a⌝ →
      srvAddr (GF := GF) «$r0_ptr» a (P a) (Q a) path) $$ []
  · imodintro
    iintro %a %ha
    ihave Ha := Haddrs $$ %a %ha
    iunfold srvAddrH at Ha
    icases Ha with ⟨%hQ, #Hp, #Hz, #Hb, #Hhc⟩
    iunfold srvAddr
    iframe Hp Hz Hb
    isplitr
    · ipureintro; exact hQ
    imodintro
    iintro %cn
    iapply srvHandler_intro «$r0_ptr» h cn a (P a) (Q a) path hpath
    iframe Hse Hh Hdg
    iapply Hhc
  wp_apply wp_Serve «$r0_ptr» lis l la P Q path hpath hlen
    $$ [$Henv $Hre $Hse $Hctxi $Hlogi $Hsc $Hsdf $Hss $Hkeys $Hwp $Hrp $Htm $Hsa $Hlis $Hon $Hli
      Hnpo Hnpe Hlg] as %err -
  · iunfold srvServeRest
    isplitr; · iexact Htls
    isplitr; · iexact Hbc
    isplitr; · iexact Hcc
    isplitr; · iexact Hel
    isplitl [Hnpo]; · iexact Hnpo
    isplitl [Hnpe]; · iexact Hnpe
    iexact Hlg
  try wp_auto
  iapply HΦ; itrivial

end proof

end net.http
end Perennial
