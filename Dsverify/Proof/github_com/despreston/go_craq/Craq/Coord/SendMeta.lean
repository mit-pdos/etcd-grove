/-
`cdr.sendMeta(n, meta)` (lock held): a disconnected node gets nothing; a connected one gets the
Update (its role half and the Update's deposit); a failed Update disconnects it.
-/
module

public import Dsverify.Proof.github_com.despreston.go_craq.Craq.Coord.Lemmas

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net

namespace github_com.despreston.go_craq

attribute [local instance] GooseGlobalGS.gooseInvGS

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [log.Assumptions] [LogHyp GF] [examples.craqnet.Assumptions] [store.Assumptions] [store.kv.Assumptions] [transport.Assumptions] [transport.netrpc.Assumptions] [node.Assumptions] [coordinator.Assumptions]
variable [net.rpc.Assumptions] [π : NetProtoGS]

/-- What `sendMeta` needs of node `a` when `connected` is `b`. -/
def sendPre (cfg : Cfg GF) (a : GoString) (b : Bool) (r : Role) (m : MetaV) : IProp GF :=
  if b then iprop(roleHalf cfg.γ a r ∗ updDep cfg.γ r m) else iprop(True)

/-- What `sendMeta` gives back. -/
def sendPost (cfg : Cfg GF) (a : GoString) (b : Bool) (r : Role) (m : MetaV) (b' : Bool)
    (err : GoInterface) : IProp GF :=
  iprop((⌜err = interface.nil ∧ b = true ∧ b' = true⌝ ∗ updPost cfg.γ a r m) ∨
    (⌜b' = false⌝ ∗ models_lab.errAny err))

theorem wp_sendMeta (cfg : Cfg GF) (c n ptr : Loc) (a : GoString) (b : Bool) (dq : DFrac)
    (m : MetaV) (r : Role) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.despreston.go_craq.coordinator ∗
        nodeFacts cfg n a ∗ structFieldRef coordinator.node go!"connected" n ↦ b ∗
        metaPtr ptr dq m ∗ ⌜metaAddrsOk cfg.chain m⌝ ∗ sendPre cfg a b r m }}
      (App (App (Val (c @!! go.GoType.PointerType coordinator.Coordinator.ty @!! go!"sendMeta"))
        (Val #n)) (Val #ptr))
    {{ (err : GoInterface), RET #err;
        ∃ b' : Bool, structFieldRef coordinator.node go!"connected" n ↦ b' ∗
          sendPost cfg a b r m b' err }} := by
  wp_start as ⟨#Hnf, Hconn, Hm, %Hok, Hpre⟩
  ihave ⟨-, -, #Herr, -⟩ := coord_pkg_errs $$ Hpkg
  ihave ⟨%errD, #HerrD, #HerrMsg⟩ := newVar_errMsg _ _ $$ Herr
  unfold nodeFacts
  icases Hnf with ⟨#Haddr, %cl, #Hrpc, #Hcl⟩
  wp_auto
  cases b
  · wp_auto
    iapply HΦ
    iexists false
    iframe Hconn
    unfold sendPost
    iright
    isplitr
    · ipureintro; rfl
    iapply errMsg_errAny $$ HerrMsg
  wp_auto
  unfold sendPre
  simp only [↓reduceIte]
  icases Hpre with ⟨Hrole, Hdep⟩
  unfold isNodeClient
  icases Hcl with ⟨%e, ⟨%He, %Ha⟩, #Hcl⟩
  subst He
  icases Hcl with ⟨-, -, -, -, -, #HUpd, -⟩
  wp_auto
  wp_apply HUpd $$ %ptr %dq %m %r %_ %Hok Hm Hrole Hdep as %err Hres
  icases Hres with (⟨%Hnil, -, Hpost⟩ | #Hany)
  · subst Hnil
    wp_auto
    iapply HΦ
    iexists true
    iframe Hconn
    unfold sendPost
    ileft
    iframe Hpost
    ipureintro; exact ⟨rfl, rfl, rfl⟩
  · ihave %Hne := models_lab.errAny_ne_nil $$ Hany
    obtain ⟨i, rfl⟩ : ∃ i, err = GoInterface.ok i := by
      cases err with
      | nil => exact absurd rfl Hne
      | ok i => exact ⟨i, rfl⟩
    wp_auto
    iapply HΦ
    iexists false
    iframe Hconn
    unfold sendPost
    iright
    iframe Hany
    ipureintro; rfl

end proof

end github_com.despreston.go_craq

end Perennial
