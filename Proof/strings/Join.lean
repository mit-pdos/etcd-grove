/-
Port of `election_proof/proof_strings_Join.v` (stage R4 of the raft v3.7 retarget).
-/
module

public import Spec.strings.Join

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- From Perennial's `strings.Join_owned_bounded_of` over the real `Join`'s spec. -/
theorem strings.Join.wp_proof
    (wp_Join : _root_.Perennial.strings.Join.spec (GF := GF) (hG := hG)) :
    strings.Join.spec (GF := GF) (hG := hG) := by
  intro elems xs sep B hB hm
  iintro %Φ ⟨#Hpkg, Hs⟩ HΦ
  wp_apply _root_.Perennial.strings.Join_owned_bounded_of wp_Join elems xs sep B hB hm
    $$ [$Hs] as Hs
  iapply HΦ $$ Hs


end proof

end EtcdGrove
end Perennial
