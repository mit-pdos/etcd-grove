module

public import Dsverify.Proof.github_com.despreston.go_craq.Craq.Specs
public import Dsverify.Proof.github_com.despreston.go_craq.Craq.LogHyp

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net

namespace github_com.despreston.go_craq

attribute [local instance] GooseGlobalGS.gooseInvGS

namespace NodeP

section common
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [examples.craqnet.Assumptions] [store.Assumptions] [store.kv.Assumptions] [transport.Assumptions] [transport.netrpc.Assumptions] [node.Assumptions] [coordinator.Assumptions]
variable [net.rpc.Assumptions] [net.FieldAssumptions] [π : NetProtoGS]
variable [ra : RpcHttpAddr GF]

/-- The node package's error variables. -/
theorem node_vars :
    isPkgInit (PROP := IProp GF) pkg_id.github_com.despreston.go_craq.node ⊢
      errors.newVar node.errNoSuccessor go!"no successor" ∗
      errors.newVar node.errNoTail go!"no connection to the tail" ∗
      errors.newVar node.errNotTail go!"not the tail" ∗
      errors.newVar node.errTailVersion go!"failed to get the latest version from the tail" := by
  with_unfolding_all exact isPkgInit_access (PROP := IProp GF) pkg_id.github_com.despreston.go_craq.node

/-- An error with a non-empty message. -/
theorem errNE_of_errMsg (err : GoInterface) (msg : GoString) (h : msg ≠ []) :
    net.rpc.errMsg (GF := GF) err msg ⊢ errNE err := by
  iintro #H
  unfold errNE
  iexists msg
  iframe H
  ipureintro; exact h

theorem errNotFound_errMsg (err : GoInterface) :
    errNotFound (hG := hG) err ⊢ net.rpc.errMsg err go!"that key does not exist" := by
  unfold errNotFound net.rpc.errMsg
  iintro ⟨%x, %Hx, -, -, #H⟩
  iexists ⟨go.GoType.PointerType errors.errorString.ty, #x⟩
  isplitr
  · ipureintro; exact Hx
  isplitr
  · ipureintro; go_type_set
  iexact H

theorem errMsg_ok (err : GoInterface) (msg : GoString) :
    net.rpc.errMsg (GF := GF) err msg ⊢ ⌜∃ ei, err = GoInterface.ok ei⌝ := by
  unfold net.rpc.errMsg
  iintro ⟨%ei, %h, -⟩
  ipureintro; exact ⟨ei, h⟩

theorem errAny_ok (err : GoInterface) :
    models_lab.errAny (GF := GF) err ⊢ ⌜∃ ei, err = GoInterface.ok ei⌝ := by
  unfold models_lab.errAny
  iintro ⟨%ei, %h, -⟩
  ipureintro; exact ⟨ei, h⟩

instance errNotFound_persistent (err : GoInterface) :
    Persistent (errNotFound (hG := hG) err) := by
  unfold errNotFound; infer_instance

/-- The protocol laws the node's proofs use (other packages' results, as hypotheses). -/
structure Laws : Prop where
  commit : commit.spec (GF := GF)
  read : read.spec (GF := GF)
  tailTok_cvLb : tailTok_cvLb.spec (GF := GF)
  tailTok_lb : tailTok_lb.spec (GF := GF)
  cvLb_zero : cvLb_zero.spec (GF := GF)
  cvLb_mono : cvLb_mono.spec (GF := GF)
  valsElem_agree : valsElem_agree.spec (GF := GF)
  covers_nil : covers_nil.spec (GF := GF)
  roleHalf_agree : roleHalf_agree.spec (GF := GF)
  roleHalf_update : roleHalf_update.spec (GF := GF)
  nlog_covers : nlog_covers.spec (GF := GF)
  nlog_covers_le : nlog_covers_le.spec (GF := GF)
  nlog_append : nlog_append.spec (GF := GF)
  covers_mono : covers_mono.spec (GF := GF)
  cvOf_append : cvOf_append.spec
  cvOf_commit : cvOf_commit.spec

end common

end NodeP

end github_com.despreston.go_craq

end Perennial
