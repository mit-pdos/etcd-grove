/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/SnapBase.lean (241f27e).
-/
/-
(stage 3, snap) Shared lemmas of the snapshot paths: `errors.Is` on raft's error values (leaf
`*errorString`s).
-/
module
public import Dsverify.Proof.github_com.hashicorp.raft.core.Laws
public import Dsverify.Proof.github_com.hashicorp.raft.SnapFut
public import Perennial.Proof.errors.Results
@[expose] public section
noncomputable section
namespace Perennial
open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.Assumptions]
open github_com.hashicorp.raft

namespace github_com.hashicorp.raft.snapProof

omit [GooseSemantics] in
/-- An `errors.New` error (`*errorString`) is a leaf without an `Is` method. -/

theorem errorString_leaf (x : Loc) :
    errors.isLeafError (⟨go.GoType.PointerType errors.errorString.ty, #x⟩ : GoInterfaceOk) ∧
    methodSet (go.GoType.PointerType errors.errorString.ty) !! go!"Is" ≠
      some (go.Signature [go.error] false [go.bool]) := by
  unfold errors.isLeafError
  have h1 := (go.MethodSetIs.method_set_is (t := go.GoType.PointerType errors.errorString.ty) go!"As")
  have h2 := (go.MethodSetIs.method_set_is (t := go.GoType.PointerType errors.errorString.ty) go!"Unwrap")
  have h3 := (go.MethodSetIs.method_set_is (t := go.GoType.PointerType errors.errorString.ty) go!"Is")
  simp only [go.methodSetLookup, gooseReduceIteDecide] at h1 h2 h3
  simp [h1, h2, h3]

/-- `errors.Is(err, target)` on two raft error values: no panic, some answer. -/
theorem wp_Is_raftErr (c d : RaftErr) (err tgt : GoInterface) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗ isRaftErr c err ∗ isRaftErr d tgt }}
      (App (App (Val (@! errors.Is)) (Val #err)) (Val #tgt))
    {{ (b : Bool), RET #b; True }} := by
  iintro %Φ ⟨#Hpkg, #He, #Ht⟩ HΦ
  unfold isRaftErr
  icases He with ⟨%f, #Hf, %hf⟩
  icases Ht with ⟨%g, #Hg, %hg⟩
  icases errVals_elem f c $$ Hf with ⟨#P, #Hn⟩
  icases errVals_elem g d $$ Hg with ⟨#Q, #Hm⟩
  unfold errors.newVar
  icases Hn with ⟨%x, #Px, -⟩
  icases Hm with ⟨%y, #Py, -⟩
  icombine P Px gives %h1
  icombine Q Py gives %h2
  subst hf hg
  rw [h1, h2]
  obtain ⟨hl, hi⟩ := errorString_leaf (GF := GF) (hG := hG) (package_sem := package_sem) x
  have h := errors.wp_Is_leaf (GF := GF) (hG := hG) (package_sem := inferInstance)
    ⟨go.GoType.PointerType errors.errorString.ty, #x⟩
    (interface.mkOk (go.GoType.PointerType errors.errorString.ty) #y) hl hi
    (fun tii ht => by cases ht; exact errors.newVar_isPointerError y)
    (errors.treeTyped_pointer _ _ (errors.newVar_isPointerError x))
  iapply h
  · iPkgInit
  inext; iintro -
  iapply HΦ; itrivial
/-- (stage 4) `errors.Is(err, target)` on an `errors.New` error (a `*errorString`, e.g. `takeSnapshot`'s
`fmt.Errorf` of the configuration index, `fmt.wp_Errorf_snapCfgErr`) and a raft error value: no panic,
some answer. -/
theorem wp_Is_errorString (d : RaftErr) (x : Loc) (tgt : GoInterface) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗ isRaftErr d tgt }}
      (App (App (Val (@! errors.Is))
        (Val #(interface.mkOk (go.GoType.PointerType errors.errorString.ty) #x))) (Val #tgt))
    {{ (b : Bool), RET #b; True }} := by
  iintro %Φ ⟨#Hpkg, #Ht⟩ HΦ
  unfold isRaftErr
  icases Ht with ⟨%g, #Hg, %hg⟩
  icases errVals_elem g d $$ Hg with ⟨#Q, #Hm⟩
  unfold errors.newVar
  icases Hm with ⟨%y, #Py, -⟩
  icombine Q Py gives %h2
  subst hg
  rw [h2]
  obtain ⟨hl, hi⟩ := errorString_leaf (GF := GF) (hG := hG) (package_sem := package_sem) x
  have h := errors.wp_Is_leaf (GF := GF) (hG := hG) (package_sem := inferInstance)
    ⟨go.GoType.PointerType errors.errorString.ty, #x⟩
    (interface.mkOk (go.GoType.PointerType errors.errorString.ty) #y) hl hi
    (fun tii ht => by cases ht; exact errors.newVar_isPointerError y)
    (errors.treeTyped_pointer _ _ (errors.newVar_isPointerError x))
  iapply h
  · iPkgInit
  inext; iintro -
  iapply HΦ; itrivial

/-- A raft error value is an `errors.New` error (a `*errorString`). -/
theorem raftErr_shape (c : RaftErr) (e : GoInterface) :
    isRaftErr (GF := GF) c e ⊢ ∃ x : Loc, ⌜e = interface.mkOk (go.GoType.PointerType errors.errorString.ty) #x⌝ := by
  unfold isRaftErr
  iintro ⟨%f, #Hf, %hf⟩
  icases errVals_elem f c $$ Hf with ⟨#P, #Hn⟩
  unfold errors.newVar
  icases Hn with ⟨%x, #Px, -⟩
  icombine P Px gives %h1
  iexists x
  ipureintro; rw [← hf, h1]

end github_com.hashicorp.raft.snapProof

end proof

end Perennial
