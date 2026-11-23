/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/net/rpc/LocalRegister.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
Local variants of the harness's `Server.Register` and `Register` (Harness/Proof/net/rpc/ServerDefs.lean)
whose name premise is `nameOkFor fn rcvr`: the kit's `Name` function meets `RpcNames` at the
registered receiver only, instead of `kitNameOk` (at every receiver, which the generated
`rpcName` does not meet: it panics on a receiver not in kit.toml; HUB-REQUEST 1 of the codec
group, a finding against the kit's fixed `nameOk`). The proofs are the harness's, with
`Hname` used at `rcvr`.
-/
module


-- PORT: lab imports dropped: Harness.Proof.net.rpc.ServerDefs

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace net.rpc

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [RpcNames]

/-- The name function `fn` meets `RpcNames` at `rcvr` (persistent). -/
def nameOkFor (fn : GoFunc) (rcvr : GoInterface) : IProp GF :=
  iprop(□ ∀ Φ : val → IProp GF, ▷ Φ #(RpcNames.name rcvr) -∗ WP (App (Val #fn) (Val #rcvr)) {{ Φ }})

instance nameOkFor_persistent (fn : GoFunc) (rcvr : GoInterface) :
    Persistent (nameOkFor (GF := GF) fn rcvr) := by
  unfold nameOkFor; infer_instance

end defs

section register
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netConnExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [net.Assumptions] [net.model.Assumptions] [net.rpc.Assumptions] [RpcKit] [RpcCodec GF]
variable [RpcNames]

/-- `kitNameOk` gives `nameOkFor` at every receiver. -/
theorem kitNameOk_for (rcvr : GoInterface) :
    kitNameOk (GF := GF) ⊢ nameOkFor (kitFn go!"rpcName") rcvr := by
  unfold kitNameOk nameOk nameOkFor
  iintro #H !> %Φ HΦ
  iapply H
  iexact HΦ

/-- `s.Register(rcvr)`, with the name premise at `rcvr` only. -/
abbrev Server.Register.spec' : Prop :=
  ∀ (s : Loc) (rcvr : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.net.rpc ∗ isServer s ∗ codecSet (GF := GF) ∗
      kitCodecOk (GF := GF) ∗ nameOkFor (GF := GF) (kitFn go!"rpcName") rcvr ∗
      RpcCodec.methods rcvr }}
    (App (Val (s @!! go.GoType.PointerType Server.ty @!! go!"Register")) (Val #rcvr))
  {{ (err : GoInterface), RET #err;
      (⌜err = interface.nil⌝ ∗ svcReg s (RpcNames.name rcvr) rcvr) ∨ ⌜err ≠ interface.nil⌝ }}

/-- `Register(rcvr)` (on the `DefaultServer`), with the name premise at `rcvr` only. -/
abbrev Register.spec' : Prop :=
  ∀ (rcvr : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.net.rpc ∗ codecSet (GF := GF) ∗
      kitCodecOk (GF := GF) ∗ nameOkFor (GF := GF) (kitFn go!"rpcName") rcvr ∗
      RpcCodec.methods rcvr }}
    (App (Val (@! net.rpc.Register)) (Val #rcvr))
  {{ (err : GoInterface), RET #err;
      (⌜err = interface.nil⌝ ∗ defaultSvcReg (RpcNames.name rcvr) rcvr) ∨
        ⌜err ≠ interface.nil⌝ }}

set_option goose.wp.extras true

theorem Server.Register.wp_proof' : Server.Register.spec' (GF := GF) (hG := hG) := by
  intro s rcvr
  wp_start as ⟨#Hsrv, #Hset, #Hok, #Hname, Hm⟩
  ihave ⟨-, -, -, #Herrors⟩ := deps_of_pkg $$ Hpkg
  wp_auto
  wp_apply getCodec.wp_proof $$ [$Hpkg $Hset] as %c #Hfns
  unfold codecFns
  icases Hfns with ⟨-, -, -, -, #HfN⟩
  wp_auto
  unfold nameOkFor
  wp_apply Hname
  wp_if_destruct
  · wp_apply errors.wp_New_errorString as %x #-
    iapply HΦ; iright; ipureintro; simp [interface.mkOk]
  rcases hn : RpcNames.name rcvr with _ | ⟨b0, rest⟩
  · exact absurd hn Hif
  simp only [List.getElem?_cons_zero]
  wp_auto
  wp_if_destruct
  · wp_apply errors.wp_New_errorString as %x #-
    iapply HΦ; iright; ipureintro; simp [interface.mkOk]
  wp_if_destruct
  · wp_apply errors.wp_New_errorString as %x #-
    iapply HΦ; iright; ipureintro; simp [interface.mkOk]
  wp_apply Server.RegisterName.wp_proof $$ [$Hpkg $Hsrv $Hset $Hok $Hm] as %err Hr
  iapply HΦ
  iexact Hr

theorem Register.wp_proof' : Register.spec' (GF := GF) (hG := hG) := by
  intro rcvr
  wp_start as ⟨#Hset, #Hok, #Hname, Hm⟩
  ihave #Hi := isInit_access $$ Hpkg
  iNamed Hi
  icases HDefaultServer with ⟨%s, #Hs, #Hsrv⟩
  wp_auto
  wp_apply Server.Register.wp_proof' $$ [$Hpkg $Hsrv $Hset $Hok $Hname $Hm] as %err Hr
  iapply HΦ
  icases Hr with (⟨%He, #Hr⟩ | %He)
  · ileft; isplitr
    · ipureintro; exact He
    unfold defaultSvcReg; iexists s; iframe Hs Hr
  · iright; ipureintro; exact He

end register

end net.rpc

end Perennial
