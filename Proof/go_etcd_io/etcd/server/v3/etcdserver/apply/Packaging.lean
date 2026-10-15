/-
The apply package's packaging lemmas (`server/v3/etcdserver/apply`): a wrapper layer's
thread-owned resources (`chainRes`) are its inner applier's (and, for the auth layer, its
`authInfo`). Lean-first (no Rocq counterpart); shared by the constructors' proofs
(`newQuotaApplierV3.lean`, ...) and the layers' methods.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.Chain

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace apply

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.apply

section lemmas
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions]

theorem mkOk_ptr_inj (t : go.GoType) (p q : Loc)
    (h : interface.mkOk t #p = interface.mkOk t #q) : p = q := by
  simp only [interface.mkOk, GoInterface.ok.injEq, GoInterfaceOk.mk.injEq, true_and] at h
  exact GoGlobalContext.intoVal_inj_loc h

/-! ## The quota layer -/

theorem chainRes_quota_out (c : Chain) (p : Loc) (inner : GoInterface) :
    structFieldRef quotaApplierV3 go!"applierV3" p ↦□ inner ⊢
      chainRes (GF := GF) (.quota c) (interface.mkOk (go.GoType.PointerType quotaApplierV3.ty) #p) -∗
        chainRes c inner := by
  iintro #Hf Hr
  simp only [chainRes]
  icases Hr with ⟨%p', %inner', %Ha, #Hf', Hr⟩
  have := mkOk_ptr_inj _ _ _ Ha
  subst this
  icombine Hf Hf' gives %Heq
  subst Heq
  iexact Hr

theorem chainRes_quota_in (c : Chain) (p : Loc) (inner : GoInterface) :
    structFieldRef quotaApplierV3 go!"applierV3" p ↦□ inner ⊢
      chainRes (GF := GF) c inner -∗
        chainRes (.quota c) (interface.mkOk (go.GoType.PointerType quotaApplierV3.ty) #p) := by
  iintro #Hf Hr
  simp only [chainRes]
  iexists p, inner
  iframe Hf Hr
  ipureintro; rfl

/-! ## The capped layer -/

theorem chainRes_capped_out (c : Chain) (p : Loc) (inner : GoInterface) :
    structFieldRef applierV3Capped go!"applierV3" p ↦□ inner ⊢
      chainRes (GF := GF) (.capped c) (interface.mkOk (go.GoType.PointerType applierV3Capped.ty) #p) -∗
        chainRes c inner := by
  iintro #Hf Hr
  simp only [chainRes]
  icases Hr with ⟨%p', %inner', %Ha, #Hf', Hr⟩
  have := mkOk_ptr_inj _ _ _ Ha
  subst this
  icombine Hf Hf' gives %Heq
  subst Heq
  iexact Hr

theorem chainRes_capped_in (c : Chain) (p : Loc) (inner : GoInterface) :
    structFieldRef applierV3Capped go!"applierV3" p ↦□ inner ⊢
      chainRes (GF := GF) c inner -∗
        chainRes (.capped c) (interface.mkOk (go.GoType.PointerType applierV3Capped.ty) #p) := by
  iintro #Hf Hr
  simp only [chainRes]
  iexists p, inner
  iframe Hf Hr
  ipureintro; rfl

/-! ## The corrupt layer -/

theorem chainRes_corrupt_out (c : Chain) (p : Loc) (inner : GoInterface) :
    structFieldRef applierV3Corrupt go!"applierV3" p ↦□ inner ⊢
      chainRes (GF := GF) (.corrupt c)
        (interface.mkOk (go.GoType.PointerType applierV3Corrupt.ty) #p) -∗
        chainRes c inner := by
  iintro #Hf Hr
  simp only [chainRes]
  icases Hr with ⟨%p', %inner', %Ha, #Hf', Hr⟩
  have := mkOk_ptr_inj _ _ _ Ha
  subst this
  icombine Hf Hf' gives %Heq
  subst Heq
  iexact Hr

theorem chainRes_corrupt_in (c : Chain) (p : Loc) (inner : GoInterface) :
    structFieldRef applierV3Corrupt go!"applierV3" p ↦□ inner ⊢
      chainRes (GF := GF) c inner -∗
        chainRes (.corrupt c) (interface.mkOk (go.GoType.PointerType applierV3Corrupt.ty) #p) := by
  iintro #Hf Hr
  simp only [chainRes]
  iexists p, inner
  iframe Hf Hr
  ipureintro; rfl

/-! ## The auth layer: its `authInfo` beside the inner's -/

theorem chainRes_auth_out (c : Chain) (p : Loc) (inner : GoInterface) :
    structFieldRef authApplierV3 go!"applierV3" p ↦□ inner ⊢
      chainRes (GF := GF) (.auth c) (interface.mkOk (go.GoType.PointerType authApplierV3.ty) #p) -∗
        authInfoOwn p ∗ chainRes c inner := by
  iintro #Hf Hr
  simp only [chainRes]
  icases Hr with ⟨%p', %inner', %Ha, #Hf', Hi, Hr⟩
  have := mkOk_ptr_inj _ _ _ Ha
  subst this
  icombine Hf Hf' gives %Heq
  subst Heq
  iframe Hr
  iunfold authInfoOwn
  iexact Hi

theorem chainRes_auth_in (c : Chain) (p : Loc) (inner : GoInterface) :
    structFieldRef authApplierV3 go!"applierV3" p ↦□ inner ⊢
      authInfoOwn (GF := GF) p -∗ chainRes c inner -∗
        chainRes (.auth c) (interface.mkOk (go.GoType.PointerType authApplierV3.ty) #p) := by
  iintro #Hf Hi Hr
  simp only [chainRes]
  iexists p, inner
  iframe Hf Hr
  iunfold authInfoOwn at Hi
  iframe Hi
  ipureintro; rfl

end lemmas

end apply
end EtcdGrove
end Perennial
