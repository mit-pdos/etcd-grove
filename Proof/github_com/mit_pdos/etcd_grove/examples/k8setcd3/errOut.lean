/- Lean-first (no Rocq counterpart).

The proof of `errOut(err)`: by the error's kind (`errIs`). A `*StorageError` passes the type
assertion and its code picks the output; a sentinel is a `*errorString` (the package's fact), so
the assertion fails, and it equals its variable; any other error fails the assertion and equals
neither (interfaces of different dynamic types are unequal; of the same pointer type, compared by
pointer).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8setcd3.errOut

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8setcd3

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.k8setcd3 (Input Output Obj item mstore mcfg state)

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8setcd3.Assumptions]

theorem errOut.wp_proof : errOut.spec (GF := GF) (hG := hG) := by
  intro _ _ err y
  wp_start as Hy
  ihave #Hi : (github_com.mit_pdos.etcd_grove.examples.k8setcd3.drvInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hi with ⟨-, -, -, -, ⟨%lD, #HD, -⟩, ⟨%lU, #HU, -⟩⟩
  iunfold errIs at Hy
  icases Hy with (⟨%k, %rv, Hse, %Hy⟩ | ⟨%k, %rv, Hse, %Hy⟩ | ⟨Hs, %Hy⟩ | ⟨%Hy, %eD, %eU, #HD', #HU', %Hne⟩)
  · -- not found
    iunfold k8s.storageErrIs at Hse
    icases Hse with ⟨%p, %He, #Hp⟩
    subst He Hy
    iStructNamed Hp
    wp_auto
    iapply HΦ
    itrivial
  · -- key exists
    iunfold k8s.storageErrIs at Hse
    icases Hse with ⟨%p, %He, #Hp⟩
    subst He Hy
    iStructNamed Hp
    wp_auto
    iapply HΦ
    itrivial
  · -- a sentinel
    subst Hy
    icases Hs with (#Hs | #Hs)
    · icombine HD Hs gives %Heq
      subst Heq
      wp_auto
      simp only [rejectedL]
      iapply HΦ
      itrivial
    · icombine HU Hs gives %Heq
      subst Heq
      wp_auto
      cases decide (lU = lD) <;> wp_auto <;> simp only [rejectedL] <;> iapply HΦ <;> itrivial
  · -- any other error
    subst Hy
    icombine HD HD' gives %HeD
    icombine HU HU' gives %HeU
    subst HeD HeU
    obtain ⟨hD, hU, ii, rfl, hty, hptr⟩ := Hne
    wp_auto
    rw [if_neg hty, decide_eq_false hty]
    wp_auto
    by_cases hT : ii.ty = go.GoType.PointerType _root_.Perennial.errors.errorString.ty
    · obtain ⟨l, hl⟩ := hptr hT
      obtain ⟨ty, v⟩ := ii
      simp only at hT hl
      subst hT hl
      have hlD : l ≠ lD := fun e => hD (by rw [e])
      have hlU : l ≠ lU := fun e => hU (by rw [e])
      wp_auto
      simp only [hlD, decide_false]
      wp_auto
      simp only [hlU, decide_false]
      wp_auto
      simp only [errOutL]
      iapply HΦ
      itrivial
    · simp only [hT, ↓reduceIte]
      wp_auto
      simp only [hT, ↓reduceIte]
      wp_auto
      simp only [errOutL]
      iapply HΦ
      itrivial

end proof

end k8setcd3
end EtcdGrove
end Perennial
