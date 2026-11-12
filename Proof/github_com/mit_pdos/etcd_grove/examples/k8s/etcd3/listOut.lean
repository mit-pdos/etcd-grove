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
  intro pl os rv cont rem
  unfold ListSpec.listAtItems driverListSpec itemsAtD metaAtD
  wp_start as ⟨%Hpl, %s, Hs, Hit, Hm⟩
  icases Hit with ⟨%vs, Hsl, -, %Hf⟩
  icases Hm with ⟨Hrv, Hc, %r, Hr, Hrem⟩
  imod ownSlice_persist $$ Hsl with #Hsl
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
    ipureintro
    exact ⟨vs, Hf, rfl⟩
  | some n =>
    iunfold remIs at Hrem
    icases (typedPointsto_not_null_dup _ _ _) $$ Hrem with ⟨Hrem, %Hn⟩
    rw [decide_eq_false Hn]
    wp_auto
    iapply HΦ
    ipureintro
    exact ⟨vs, Hf, rfl⟩

end proof

end k8s_etcd3
end EtcdGrove
end Perennial
