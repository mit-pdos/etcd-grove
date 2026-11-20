/- Lean-first (no Rocq counterpart).

The proof of `listOut(l)`: the list's fields read (`listAtItems`: the items slice, made read-only
for `encodeItems`; the metadata), then the remaining count's pointer tested and, if not `nil`, read.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.listOut
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.encodeItems

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode k8s
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Input Output Obj)

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

theorem listOut.wp_proof (wp_encodeItems : encodeItems.spec (GF := GF) (hG := hG)) :
    listOut.spec (GF := GF) (hG := hG) := by
  intro pl s os rv cont rem
  unfold driverListSpec itemsAtD metaAtD
  wp_start as ⟨%Hpn, Hs, Hit, Hm⟩
  icases Hit with ⟨%vs, Hsl, -, %Hf⟩
  icases Hm with ⟨Hrv, Hc, %r, Hr, Hrem⟩
  imod ownSlice_persist $$ Hsl with #Hsl
  ipersist Hs
  ipersist Hrv
  ipersist Hc
  ipersist Hr
  wp_auto
  wp_apply wp_encodeItems $$ [Hsl]
  · iframe #
  iintro -
  wp_auto
  cases rem with
  | none =>
    iunfold remIs at Hrem
    icases Hrem with %hr
    subst hr
    wp_auto
    iapply HΦ
    iexists vs
    isplitr
    · ipureintro
      exact ⟨Hf, rfl⟩
    unfold k8sDeep.deepRep k8sDeep.itemsRep k8sDeep.remRep
    iexists pl, s, null
    isplitr
    · ipureintro; rfl
    isplitr
    · iapply typedPointsto_combine pl _ _ Hpn.1
      simp only [TypedPointsto.typedPointstoDef]
      iframe #
    dsimp only
    isplitr
    · isplitr
      · ipureintro; exact Hpn.2
      iexact Hsl
    ipureintro; rfl
  | some n =>
    iunfold remIs at Hrem
    icases (typedPointsto_not_null_dup _ _ _) $$ Hrem with ⟨Hrem, %Hn⟩
    ipersist Hrem
    rw [decide_eq_false Hn]
    wp_auto
    iapply HΦ
    iexists vs
    isplitr
    · ipureintro
      exact ⟨Hf, rfl⟩
    unfold k8sDeep.deepRep k8sDeep.itemsRep k8sDeep.remRep
    iexists pl, s, r
    isplitr
    · ipureintro; rfl
    isplitr
    · iapply typedPointsto_combine pl _ _ Hpn.1
      simp only [TypedPointsto.typedPointstoDef]
      iframe #
    dsimp only
    isplitr
    · isplitr
      · ipureintro; exact Hpn.2
      iexact Hsl
    iexact Hrem

end proof

end k8s_etcd3
end EtcdGrove
end Perennial
