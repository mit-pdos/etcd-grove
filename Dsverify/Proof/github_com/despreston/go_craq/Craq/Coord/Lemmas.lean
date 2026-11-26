/-
The coordinator package's shared lemmas: its package variables' errors, the errors' facts.
-/
module

public import Dsverify.Proof.github_com.despreston.go_craq.Craq.Specs
public import Net.Proof.net.rpc.Errs

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net

namespace github_com.despreston.go_craq

attribute [local instance] GooseGlobalGS.gooseInvGS

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [log.Assumptions] [examples.craqnet.Assumptions] [store.Assumptions] [store.kv.Assumptions] [transport.Assumptions] [transport.netrpc.Assumptions] [node.Assumptions] [coordinator.Assumptions] [LogSpecs GF]
variable [net.rpc.Assumptions] [π : NetProtoGS]

/-- The coordinator package's error variables. -/
theorem coord_pkg_errs :
    isPkgInit (PROP := IProp GF) pkg_id.github_com.despreston.go_craq.coordinator ⊢
      errors.newVar coordinator.ErrEmptyChain go!"no nodes in the chain" ∗
      errors.newVar coordinator.errLastNode go!"cannot remove the last node of the chain" ∗
      errors.newVar coordinator.errDisconnected go!"no metadata can be sent to the node" ∗
      errors.newVar coordinator.ErrVersions go!"no version left" := by
  iintro #H
  ihave #Hi := isPkgInit_access _ $$ H
  iexact Hi

/-- The coordinator package's initialization gives `time`'s (`time.Now`'s precondition at
Perennial 3afd77e35). -/
theorem coord_time_init :
    isPkgInit (PROP := IProp GF) pkg_id.github_com.despreston.go_craq.coordinator ⊢
      isPkgInit (PROP := IProp GF) pkg_id.time := by
  refine (isPkgInit_unfold_deps (PROP := IProp GF) pkg_id.github_com.despreston.go_craq.coordinator).trans ?_
  show iprop(isPkgInit pkg_id.errors ∗ isPkgInit pkg_id.log ∗ isPkgInit pkg_id.sync ∗
    isPkgInit pkg_id.time ∗ isPkgInit pkg_id.github_com.despreston.go_craq.transport ∗ True) ⊢ _
  iintro ⟨-, -, -, #H, -⟩
  iexact H

/-- An `errPlain` error is not nil. -/
theorem errPlain_ne_nil (e : GoInterface) : models_lab.errPlain (GF := GF) e ⊢ ⌜e ≠ interface.nil⌝ := by
  iintro #H
  iapply models_lab.errAny_ne_nil
  iapply models_lab.errPlain_errAny $$ H

/-- A package variable made by `errors.New(msg)` holds an error with message `msg`. -/
theorem newVar_errMsg (X msg : GoString) :
    errors.newVar (GF := GF) X msg ⊢
      ∃ err : GoInterface, globalAddr X ↦□ err ∗ net.rpc.errMsg err msg := by
  unfold errors.newVar net.rpc.errMsg
  iintro ⟨%x, #Hx, -, #He⟩
  iexists _
  iframe Hx
  iexists ⟨go.GoType.PointerType errors.errorString.ty, #x⟩
  isplitr
  · ipureintro; rfl
  isplitr
  · ipureintro; exact errorString_isError
  iexact He

/-- `errMsg` with a non-empty message is `errNE`. -/
theorem errMsg_errNE (err : GoInterface) (msg : GoString) (h : msg ≠ []) :
    net.rpc.errMsg (GF := GF) err msg ⊢ errNE err := by
  iintro #H
  unfold errNE
  iexists msg
  iframe H
  ipureintro; exact h

/-- The lock invariant from its parts. -/
theorem coordLock_pack (cfg : Cfg GF) (c : Loc) (sl : GoSlice) (rs : List Rep) (ver : w64)
    (hd tl : Loc) (hwf : repsWf cfg rs) :
    structFieldRef coordinator.Coordinator go!"replicas" c ↦ sl ∗
      sl ↦* rs.map Rep.loc ∗ ownSliceCap Loc sl (DFrac.own 1) ∗
      structFieldRef coordinator.Coordinator go!"version" c ↦ ver ∗ nextHalf cfg.γ ver ∗
      structFieldRef coordinator.Coordinator go!"head" c ↦ hd ∗
      structFieldRef coordinator.Coordinator go!"tail" c ↦ tl ∗
      □ ([∗list] r ∈ rs, nodeFacts cfg r.loc r.addr) ∗
      ([∗list] i ↦ r ∈ rs, connRole cfg rs i r) ∗
      ([∗list] a ∈ cfg.chain, joinRes cfg rs a) ∗
      (if rs = [] then tailTok cfg.γ [] else iprop(True)) ⊢
    coordLock (hG := hG) cfg c := by
  iintro ⟨H1, H2, H3, H4, H5, H6, H7, #H8, H9, H10, H11⟩
  unfold coordLock
  iexists sl, rs, ver, hd, tl
  unfold named
  iframe
  isplitr
  · ipureintro; exact hwf
  iexact H8

end lemmas

end github_com.despreston.go_craq

end Perennial
