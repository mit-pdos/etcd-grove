/-
transport/netrpc: `(*Client).Connect` (`rpc.DialHTTP`) as promoted to `*NodeClient` and
`*CoordinatorClient`.
-/
module

public import Dsverify.Proof.github_com.despreston.go_craq.Craq.Netrpc.Defs

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net

namespace github_com.despreston.go_craq

attribute [local instance] GooseGlobalGS.gooseInvGS

namespace netrpcP

section proofs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [examples.craqnet.Assumptions] [store.Assumptions] [transport.Assumptions] [transport.netrpc.Assumptions]
variable [net.rpc.Assumptions] [net.FieldAssumptions] [π : NetProtoGS]


/-- `cl.Connect(a)` on an unconnected `*Client`: connected to `a`, or an error. -/
theorem wp_Client_Connect (HDial : DialHTTP.spec (GF := GF)) (cfg : Cfg GF) (cl : Loc) (a : GoString) (ha : a ∈ cfg.cAddr :: cfg.chain) :
    env cfg ∗ cl ↦ transport.netrpc.Client.mk null ⊢
    ∀ Φ : val → IProp GF,
      ▷ (∀ err : GoInterface, ((⌜err = interface.nil⌝ ∗ connected cfg cl a) ∨
          models_lab.errAny err) -∗ Φ #err) -∗
      WP (App (Val #(methods (go.GoType.PointerType transport.netrpc.Client.ty) go!"Connect" #cl))
        (Val #a)) {{ Φ }} := by
  iintro ⟨#Henv, Hcl⟩ %Φ HΦ
  iStructNamed Hcl
  unfold env rpcReady craqCtx
  icases Henv with ⟨#Hpkg, ⟨#Hrpkg, #Hcs⟩, #Hcraq, %Hss, #Haddrs⟩
  ihave #Ha := BigSepL.bigSepL_mem ha $$ Haddrs
  wp_method_call
  wp_call
  wp_auto
  wp_apply HDial cfg.W a $$ [Hrpkg Ha] as %r %err Hpost
  · iexact Ha
  icases Hpost with (⟨%He, #Hr⟩ | ⟨%He, #Hany⟩)
  · subst He
    iapply wp_fupd
    wp_auto
    ipersist rpc
    imodintro
    iapply HΦ
    ileft
    isplitr
    · ipureintro; rfl
    unfold connected
    iexists r
    isplitr
    · iexact rpc
    · iexact Hr
  · rcases err with e | _
    · wp_auto
      iapply HΦ
      iright; iexact Hany
    · exact absurd rfl He

end proofs
end netrpcP
end github_com.despreston.go_craq
end Perennial
