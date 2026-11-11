/- Lean-first (no Rocq counterpart).

The proof of `errOut(err)`: by the error's kind (`errIs`). A `*StorageError` passes the type
assertion and its code picks the output; a sentinel is a `*errorString` (the package's fact), so
the assertion fails, and it equals its variable; any other error fails the assertion and equals
neither (interfaces of different dynamic types are unequal; of the same pointer type, compared by
pointer).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.errOut
public import Spec.k8s_io.apiserver.pkg.storage.IsTooLargeResourceVersion

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSimpArgs false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Input Output Obj item mstore mcfg state)

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

/-- The too-large error's view is one `IsTooLargeResourceVersion` recognizes. -/
theorem tooLargeV_of (st : k8s_io.apimachinery.pkg.apis.«meta».v1.Status)
    (cs : List k8s_io.apimachinery.pkg.apis.«meta».v1.StatusCause)
    (h : st.Reason' = go!"Timeout" ∧ go!"ResourceVersionTooLarge" ∈ cs.map (·.Type')) :
    apierrors.tooLargeV (.status st cs) = true := by
  unfold apierrors.tooLargeV apierrors.timeoutV apierrors.causeIn
  simp [h.1, h.2]

theorem errOut.wp_proof
    (wp_IsTooLarge : storage.IsTooLargeResourceVersion.spec (GF := GF) (hG := hG)) :
    errOut.spec (GF := GF) (hG := hG) := by
  intro _ _ err y
  wp_start as Hy
  ihave #Hi : (github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.drvInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  ihave ⟨%lD, %lU, #HD, #HU, -, -⟩ := drvInit_sents $$ Hi
  iunfold errIs at Hy
  icases Hy with (⟨%k, %rv, Hse, %Hy⟩ | ⟨%k, %rv, Hse, %Hy⟩ | ⟨%k, Hse, %Hy⟩ | ⟨#Ht, %Hy⟩ |
    ⟨Hs, %Hy⟩ | ⟨%Hy, #Hn, %eD, %eU, #HD', #HU', %Hne⟩)
  · -- not found
    iunfold k8s.storageErrIs at Hse
    icases Hse with ⟨%p, %He, #Hp⟩
    subst He Hy
    iStructNamed Hp
    wp_auto
    simp only [errOutL, tooLargeL, otherL, rejectedL]
    iapply HΦ
    itrivial
  · -- key exists
    iunfold k8s.storageErrIs at Hse
    icases Hse with ⟨%p, %He, #Hp⟩
    subst He Hy
    iStructNamed Hp
    wp_auto
    simp only [errOutL, tooLargeL, otherL, rejectedL]
    iapply HΦ
    itrivial
  · -- an invalid object (a failed precondition; stage 7b)
    iunfold k8s.invalidErrIs at Hse
    icases Hse with ⟨%p, %e, %He, #Hp⟩
    subst He Hy
    iStructNamed Hp
    wp_auto
    simp only [errOutL, tooLargeL, otherL, rejectedL]
    iapply HΦ
    itrivial
  · -- too large (stage 7e-4): a `*StatusError`, recognized
    subst Hy
    iunfold apierrors.tooLargeErrIs at Ht
    icases Ht with ⟨%st, %cs, #Hv, %Hst⟩
    ihave %Hp := apierrors.tooLargeErrIs_ptr err $$ [Hv]
    · iunfold apierrors.tooLargeErrIs; iexists st, cs; iframe Hv; ipureintro; exact Hst
    obtain ⟨l, rfl⟩ := Hp
    wp_auto
    wp_apply wp_IsTooLarge _ (.status st cs) $$ [Hv]
    · iframe Hv
    rw [tooLargeV_of st cs Hst]
    wp_auto
    simp only [errOutL, tooLargeL, otherL, rejectedL]
    iapply HΦ
    itrivial
  · -- a sentinel: plain, then compared
    subst Hy
    icases Hs with (#Hs | #Hs)
    · icombine HD Hs gives %Heq
      subst Heq
      wp_auto
      wp_apply wp_IsTooLarge _ .plain $$ []
      · iapply sentV_plain
      simp only [apierrors.tooLargeV]
      wp_auto
      skip
      simp only [errOutL, tooLargeL, otherL, rejectedL]
      iapply HΦ
      itrivial
    · icombine HU Hs gives %Heq
      subst Heq
      wp_auto
      wp_apply wp_IsTooLarge _ .plain $$ []
      · iapply sentV_plain
      simp only [apierrors.tooLargeV]
      wp_auto
      cases decide (lU = lD) <;> wp_auto <;> simp only [rejectedL, errOutL] <;> iapply HΦ <;> itrivial
  · -- any other error: not recognized, neither sentinel
    subst Hy
    icombine HD HD' gives %HeD
    icombine HU HU' gives %HeU
    subst HeD HeU
    iunfold notTooLarge at Hn
    icases Hn with ⟨%w, #Hw, %Hwf⟩
    obtain ⟨hD, hU, ii, rfl, hty, hptr⟩ := Hne
    wp_auto
    rw [if_neg hty, decide_eq_false hty]
    wp_auto
    wp_apply wp_IsTooLarge _ w $$ [Hw]
    · iframe Hw
    rw [Hwf]
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
      skip
      simp only [errOutL, tooLargeL, otherL, rejectedL]
      iapply HΦ
      itrivial
    · simp only [hT, ↓reduceIte]
      wp_auto
      simp only [hT, ↓reduceIte]
      wp_auto
      skip
      simp only [errOutL, tooLargeL, otherL, rejectedL]
      iapply HΦ
      itrivial

end proof

end k8s_etcd3
end EtcdGrove
end Perennial
