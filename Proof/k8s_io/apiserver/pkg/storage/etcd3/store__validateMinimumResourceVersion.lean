/-
Lean-first (no Rocq counterpart).

The proof of `(*store).validateMinimumResourceVersion`: `""` returns at once (it parses to `0`);
another minimum is parsed by the versioner (`versionerOk`) and compared with the revision.
-/
module

public import Spec.k8s_io.apiserver.pkg.storage.etcd3.store__validateMinimumResourceVersion
public import Spec.k8s_io.apiserver.pkg.storage.NewTooLargeResourceVersionError

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : k8s_io.apiserver.pkg.storage.etcd3.Assumptions]

theorem store.validateMinimumResourceVersion.wp_proof
    (wp_TooLarge : storage.NewTooLargeResourceVersionError.spec (GF := GF) (hG := hG)) :
    store.validateMinimumResourceVersion.spec (GF := GF) (hG := hG) := by
  intro _ _ Obj _ sp c m n rev
  wp_start as ⟨#Hs, %hp⟩
  by_cases hm : m = []
  · subst hm
    have hn : n = W64 0 := Option.some.inj (hp.symm.trans c.S.parse_empty)
    subst hn
    wp_auto
    iapply HΦ
    ipureintro
    have : ¬ uint.nat rev < uint.nat (W64 0) := by simp
    simp only [this, ↓reduceIte]
  · wp_auto
    rw [decide_eq_false hm]
    iunfold isStore at Hs
    icases Hs with ⟨%Hsp, #Fcl, #Fcodec, #Fvi, #Fti, #Fdi, #Fpp, #Frp, #Fgr, #Fmt, #Flt, %Hlt, #Hkc,
      #Hcl, #Hone, #Hregs, #Hcon⟩
    iunfold contractOk at Hcon
    icases Hcon with ⟨%Hty, #Henc, #Hver, #Htr, #Hdec, #Hzero, #Hmeta⟩
    iunfold versionerOk at Hver
    icases Hver with ⟨#HORV, #HPrep, #HUpd, #HParse⟩
    wp_auto
    wp_bind
    iapply HParse
    inext
    iintro %n' %err %hn'
    rw [hp] at hn'
    obtain ⟨rfl, rfl⟩ := hn'
    wp_auto
    by_cases hlt : uint.nat rev < uint.nat n'
    · rw [decide_eq_true (by word)]
      wp_auto
      wp_apply wp_TooLarge as %err %herr
      iapply HΦ
      ipureintro
      simp only [hlt, ↓reduceIte]
      exact herr
    · rw [decide_eq_false (by word)]
      wp_auto
      iapply HΦ
      ipureintro
      simp only [hlt, ↓reduceIte]

end proof

end k8s
end EtcdGrove
end Perennial
