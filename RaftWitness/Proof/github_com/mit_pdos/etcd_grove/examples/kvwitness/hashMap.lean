/-
Lean-first (no Rocq counterpart).

The proof of `hashMap`: a loop over the map, calling `hashString`; nothing is claimed of the
result.
-/
module

public import RaftWitness.Spec.github_com.mit_pdos.etcd_grove.examples.kvwitness.hashMap
public import RaftWitness.Spec.github_com.mit_pdos.etcd_grove.examples.kvwitness.hashString

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvwitness

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode go_etcd_io.raft.v3
open github_com.anishathalye.porcupine

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvwitness.Assumptions]

theorem hashMap.wp_proof (wp_hashString : hashString.spec (GF := GF) (hG := hG)) :
    hashMap.spec (GF := GF) (hG := hG) := by
  intro l m dq
  wp_start as Hm
  wp_auto
  wp_func_lits
  wp_bind (App (App (Val (map.forRange _ _)) _) _)
  iapply wp_map_for_range (fun (_ : List GoString) (_ : Int) => iprop(∃ (x y : GoString)
      (hv : w64),
      "k" ∷ k_ptr ↦ x ∗
      "v" ∷ v_ptr ↦ y ∗
      "h" ∷ h_ptr ↦ hv)) $$ Hm
  iintro %keys _
  isplitl [k v h]
  · iexists _, _, _
    iframe
  isplitr
  · imodintro
    iintro %i %key %vv _ HP
    iNamed HP
    wp_auto
    wp_if_destruct
    · unfold forMapPostcondition
      iright; ileft
      isplitr
      · ipureintro; rfl
      iexists _, _, _
      iframe
    · wp_apply wp_hashString as %h1 _
      wp_apply wp_hashString as %h2 _
      unfold forMapPostcondition
      iright; ileft
      isplitr
      · ipureintro; rfl
      iexists _, _, _
      iframe
  iintro HP Hm
  iNamed HP
  wp_auto
  iapply HΦ
  iframe

end proof

end kvwitness
end EtcdGrove
end Perennial
