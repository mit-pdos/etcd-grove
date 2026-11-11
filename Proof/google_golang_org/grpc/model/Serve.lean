/-
Proof of `Spec/google_golang_org/grpc/model/Serve.lean`: the trusted `Serve` model
(`TrustedCode/google_golang_org/grpcServeModel.lean`) meets its spec over its leaves' axioms
(per-type stage B, B1a, 2026-11-11; Scope r5 §2.2). A Löb loop over `acceptRun`; each accepted call
is forked (`wp_fork_tok_upd`: the forker gets the fork's thread token and a later credit, both
passed into the run); the run identifies the client's deposited registration with Go's handler
(`grpcSrvCfg_agree`, the joint `Nodup`), applies its run contract with the token and the credit,
answers through `respond` (unary) or `finishStream` (stream), and exits with the token the contract
returns. `serveRest` is the same loop over `acceptRunConns`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.google_golang_org.grpc.model.Serve
public import Spec.google_golang_org.grpc.model.acceptRun
public import Spec.google_golang_org.grpc.model.acceptRunConns
public import Spec.google_golang_org.grpc.model.respond
public import Spec.google_golang_org.grpc.model.finishStream

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode google_golang_org.grpc

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- An accepted call's run value is not a panic. -/
theorem grpcAccepted_notPanic (γ : GName) (c : GrpcSrvCfg GF) (r : val) :
    grpcAccepted γ c r ⊢ ⌜r.isPanic = false⌝ := by
  iintro Hacc
  iunfold grpcAccepted at Hacc
  icases Hacc with (⟨%_, %_, %_, %_, %_, %_, %_, %_, %_, %_, %_, %_, %_, %Hr, -⟩ |
    ⟨%_, %_, %_, %_, %_, %_, %_, %_, %_, %_, %_, %_, %_, %_, %Hr, -⟩) <;>
    (subst Hr; ipureintro; rfl)

/-- **A run of an accepted call** (the model's `runCall`), given the fork's token and credit. -/
theorem grpc.model.runCall_wp
    (hR : grpc.model.respond.spec (GF := GF) (hG := hG))
    (hF : grpc.model.finishStream.spec (GF := GF) (hG := hG))
    (gs : Loc) (γ : GName) (c : GrpcSrvCfg GF) (r : val) (Hnd : grpcSrvNodup c)
    (Hfit : grpcRepliesFit) :
    threadTok ∗ £ 1 ∗ grpcSrvCfg γ c ∗ grpcAccepted γ c r ⊢
      WP (App (App (Val model.runCall) (Val #gs)) (Val r))
        {{ v, ⌜v.isPanic = false⌝ ∗ threadTok }} := by
  iintro ⟨HT, Hlc, #Hc, Hacc⟩
  iunfold grpcAccepted at Hacc
  icases Hacc with (⟨%name, %mh, %srv, %ci, %cd, %dec, %ui, %Req, %Rep, %Spec, %m, %Φ, %Ψe, %Hr,
      %Hin, Hat, Hctx, Hrc, Hd, Hch, HSpec, Hrep⟩ |
    ⟨%name, %mh, %srv, %ci, %cd, %st, %info, %si, %Req, %Rep, %Up, %Spec, %γs, %Dn, %Hr, %Hin,
      %Hmh, Hat, Hsch, #HSpec, Hraw, HRt, HSt, HAt, Hinfo⟩)
  · -- unary
    iunfold isGrpcRpcAt at Hat
    icases Hat with ⟨%c', %mh', %srv', #Hc', %Hin', #Hrun⟩
    ihave %Heq := grpcSrvCfg_agree γ c c' $$ [Hc Hc']
    · iframe #
    subst Heq
    obtain ⟨rfl, rfl⟩ := grpc_regs_unique c.regs c.sregs name mh mh' srv srv' Hnd Hin Hin'
    subst Hr
    unfold model.runCall model.runUnary
    wp_auto
    wp_pures
    iunfold grpcRunOkMd at Hrun
    wp_apply Hrun $$ %m %Φ %Ψe %ci %cd %dec %ui [HT Hlc Hctx Hrc Hd Hch HSpec] as
      %resp %err ⟨HT, Hok, Herr, #Hse⟩
    · iframe
    wp_pures
    wp_apply hR $$ %gs %_ %resp %err %Rep %Φ %Ψe [Hrep Hok Herr]
    · iframe
      iframe #
      ipureintro; exact Hfit
    iframe
    ipureintro; exact isPanic_intoVal ()
  · -- stream
    iunfold isGrpcStreamAt at Hat
    icases Hat with ⟨%c', %mh', %srv', #Hc', %Hin', Hrun⟩
    ihave %Heq := grpcSrvCfg_agree γ c c' $$ [Hc Hc']
    · iframe #
    subst Heq
    obtain ⟨rfl, rfl⟩ := grpc_sregs_unique c.regs c.sregs name mh mh' srv srv' Hnd Hin Hin'
    subst Hr
    iunfold grpcStreamRunOk at Hrun
    icases Hrun with ⟨-, #Hrun⟩
    ihave Hw := Hrun $$ %γs %Dn %ci %cd %st %info HSpec HT Hlc Hraw HRt HSt HAt Hinfo
    unfold model.runCall model.runStream
    wp_auto
    rcases hs : c.sics with _ | ⟨ic, ics'⟩
    · iunfold grpcSrvStreamChain at Hsch
      icases Hsch with %Hsi
      subst Hsi
      simp only [srvStreamChainWP]
      wp_pures
      wp_bind (App (App (Val mh) _) _)
      iapply wp_wand_r
      isplitl [Hw]
      · iexact Hw
      iintro %v ⟨%err, %Hv, #Hse, HT⟩
      subst Hv
      wp_pures
      wp_apply hF $$ %gs %_ %err [Hse]
      · iexact Hse
      iframe
      ipureintro; exact isPanic_intoVal ()
    · iunfold grpcSrvStreamChain at Hsch
      icases Hsch with ⟨%Hsi, #Hch⟩
      rw [decide_eq_false Hsi]
      wp_pures
      wp_bind (App (App (App (App (Val #si) _) _) _) _)
      iapply wp_wand_r
      isplitl [Hw]
      · iapply Hch $$ %#srv %#st %#info %mh %_ Hw
      iintro %v ⟨%err, %Hv, #Hse, HT⟩
      subst Hv
      wp_pures
      wp_apply hF $$ %gs %_ %err [Hse]
      · iexact Hse
      iframe
      ipureintro; exact isPanic_intoVal ()

/-- **`serveRest`'s loop**: each call accepted on an open connection is forked. -/
theorem grpc.model.serveRest_wp
    (hC : grpc.model.acceptRunConns.spec (GF := GF) (hG := hG))
    (hR : grpc.model.respond.spec (GF := GF) (hG := hG))
    (hF : grpc.model.finishStream.spec (GF := GF) (hG := hG))
    (gs : Loc) (γ : GName) (c : GrpcSrvCfg GF) (Hnd : grpcSrvNodup c) (Hfit : grpcRepliesFit) :
    threadTok ∗ grpcConnsLink gs γ ∗ grpcSrvCfg γ c ⊢
      WP (App (Val model.serveRest) (Val #gs)) {{ v, ⌜v.isPanic = false⌝ ∗ threadTok }} := by
  iloeb as IH
  iintro ⟨HT, Hl, #Hc⟩
  unfold model.serveRest
  wp_pures
  wp_apply hC $$ %gs %γ %c [Hl] as %r %ok Hr
  · iframe; iframe #; ipureintro; exact Hfit
  icases Hr with (⟨%Hok, Hl, Hacc⟩ | %Hok) <;> subst Hok
  · ihave %Hrp := grpcAccepted_notPanic γ c r $$ Hacc
    wp_pures
    wp_bind (Fork _)
    iapply wp_fork_tok_upd
    inext
    iintro HT' Hlc
    imodintro
    isplitl [HT' Hlc Hacc]
    · wp_pure
      iapply grpc.model.runCall_wp hR hF gs γ c r Hnd Hfit
      iframe; iframe #
    wp_pure
    wp_pure
    iapply IH
    iframe; iframe #
  · wp_pures
    iframe

/-- **`Serve`'s loop**: each accepted call is forked; after a listener failure, `serveRest` keeps
accepting on the open connections, on a goroutine of its own. -/
theorem grpc.model.serveLoop_wp
    (hA : grpc.model.acceptRun.spec (GF := GF) (hG := hG))
    (hC : grpc.model.acceptRunConns.spec (GF := GF) (hG := hG))
    (hR : grpc.model.respond.spec (GF := GF) (hG := hG))
    (hF : grpc.model.finishStream.spec (GF := GF) (hG := hG))
    (gs : Loc) (lis : GoInterface) (γ : GName) (c : GrpcSrvCfg GF) (Hnd : grpcSrvNodup c)
    (Hfit : grpcRepliesFit) (Φ : val → IProp GF) :
    grpcSrvLink gs lis γ ∗ grpcSrvCfg γ c ∗ (∀ err : GoInterface, Φ #err) ⊢
      WP (App (App (Val model.serveLoop) (Val #gs)) (Val #lis)) {{ Φ }} := by
  iloeb as IH
  iintro ⟨Hl, #Hc, HΦ⟩
  unfold model.serveLoop
  wp_pures
  wp_apply hA $$ %gs %lis %γ %c [Hl] as %r %st Hr
  · iframe; iframe #; ipureintro; exact Hfit
  icases Hr with (⟨%Hst, Hl, Hacc⟩ | %Hst | ⟨%Hst, ⟨%err, %Herr⟩, Hcl⟩)
  · subst Hst
    ihave %Hrp := grpcAccepted_notPanic γ c r $$ Hacc
    wp_pures
    wp_bind (Fork _)
    iapply wp_fork_tok_upd
    inext
    iintro HT' Hlc
    imodintro
    isplitl [HT' Hlc Hacc]
    · iapply grpc.model.runCall_wp hR hF gs γ c r Hnd Hfit
      iframe; iframe #
    wp_pure
    wp_pure
    iapply IH
    iframe; iframe #
  · obtain ⟨rfl, rfl⟩ := Hst
    wp_pures
    iapply HΦ
  · subst Hst Herr
    wp_pures
    wp_bind (Fork _)
    iapply wp_fork_tok_upd
    inext
    iintro HT' Hlc
    imodintro
    isplitl [HT' Hcl]
    · iapply grpc.model.serveRest_wp hC hR hF gs γ c Hnd Hfit
      iframe; iframe #
    wp_pures
    iapply HΦ

/-- **`Serve`'s model meets its spec** (see the file header). -/
theorem grpc.model.Serve.wp_proof
    (hA : grpc.model.acceptRun.spec (GF := GF) (hG := hG))
    (hC : grpc.model.acceptRunConns.spec (GF := GF) (hG := hG))
    (hR : grpc.model.respond.spec (GF := GF) (hG := hG))
    (hF : grpc.model.finishStream.spec (GF := GF) (hG := hG)) :
    grpc.model.Serve.spec (GF := GF) (hG := hG) := by
  intro gs lis γ
  iintro %Φ Htok HΦ
  iunfold grpcServeTokR at Htok
  icases Htok with ⟨Hl, ⟨%c, #Hc, %Hnd⟩, %Hfit⟩
  unfold model.Serve
  wp_pure
  wp_pure
  wp_pure
  iapply grpc.model.serveLoop_wp hA hC hR hF gs lis γ c Hnd Hfit
  iframe; iframe #
  iintro %err
  iapply HΦ
  itrivial

end proof

end EtcdGrove
end Perennial
