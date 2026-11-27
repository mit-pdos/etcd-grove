/- Lean-first (no Rocq counterpart).

# `check`'s proof

By the outcome (`callOutcome`): a success (the reply is the method's answer to this request: its id,
its payload, `Runs` 1; and `fail` empty); a `ServerError` whose message is `fail` or one of net/rpc's
own (not marked as the method's: `srvErrMsg_not_marked`); another error (not a `ServerError`: the
type assertion fails). Each `reached` call returns (`drvFacts`).
-/
module

public import Net.Spec.github_com.mit_pdos.etcd_grove.examples.net.rpcdriver.check
public import Net.Spec.github_com.mit_pdos.etcd_grove.examples.net.rpcdriver.isFailMsg

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace github_com.mit_pdos.etcd_grove.examples.net.rpcdriver

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : Assumptions]
variable [π : NetProtoGS]

theorem check.wp_proof (wp_isFailMsg : isFailMsg.spec (GF := GF) (hG := hG)) :
    check.spec (GF := GF) (hG := hG) := by
  intro pa pr id dsl data fail err
  wp_start as ⟨#Hf, #Hstr, Hout⟩
  iunfold drvFacts at Hf
  icases Hf with ⟨-, %f, #Hrg, #Hrf⟩
  iunfold callOutcome at Hout
  icases Hout with (⟨%He, Ha, Hd, %dsl', Hr, Hd'⟩ | ⟨%msg, %He, Ha⟩ | %He)
  · -- a success: the method's reply to this request
    obtain ⟨rfl, rfl⟩ := He
    wp_auto
    wp_apply (wp_bytes_to_string dsl' data (DFrac.own 1)) $$ Hd' as Hd'
    dsimp only
    wp_apply (wp_bytes_to_string dsl data (DFrac.own 1)) $$ Hd as Hd
    repeat (first | wp_if_destruct | wp_auto)
    try wp_bind (App (Val #f) (Val _))
    iapply wp_wand $$ (Hrf $$ %go!"call-success")
    iintro %v %Hv
    subst Hv
    wp_auto
    iapply HΦ
    itrivial
  · -- a `ServerError`
    obtain ⟨rfl, hmsg⟩ := He
    wp_auto
    try simp only [net.rpc.serverErr, interface.mkOk]
    repeat (first | wp_if_destruct | wp_auto)
    wp_apply wp_isFailMsg $$ Hstr
    by_cases hm : driverMark <+: msg
    · have hmf : msg = fail := by
        rcases hmsg with h | h
        · exact h
        · exact absurd hm (srvErrMsg_not_marked msg h)
      subst hmf
      simp only [hm, decide_true]
      wp_auto
      try wp_bind (App (Val #f) (Val _))
      iapply wp_wand $$ (Hrf $$ %go!"server-error")
      iintro %v %Hv
      subst Hv
      wp_auto
      iapply HΦ
      itrivial
    · simp only [hm, decide_false]
      repeat (first | wp_if_destruct | wp_auto)
      all_goals first
        | (wp_bind (App (Val #f) (Val _))
           iapply wp_wand $$ (Hrf $$ %go!"server-error")
           iintro %v %Hv
           subst Hv
           repeat wp_auto
           iapply HΦ
           itrivial)
        | (iapply HΦ; itrivial)
  · -- another error
    obtain ⟨hne, hns⟩ := He
    have hta : ∀ v : val, True := fun _ => trivial
    cases err with
    | nil => exact absurd rfl hne
    | ok e =>
      have hty : e.ty ≠ net.rpc.ServerError.ty := hns e rfl
      wp_auto
      simp only [hty, ↓reduceIte, decide_false]
      wp_auto
      try wp_bind (App (Val #f) (Val _))
      iapply wp_wand $$ (Hrf $$ %go!"other-error")
      iintro %v %Hv
      subst Hv
      wp_auto
      iapply HΦ
      itrivial

end proof

end github_com.mit_pdos.etcd_grove.examples.net.rpcdriver
end Perennial
