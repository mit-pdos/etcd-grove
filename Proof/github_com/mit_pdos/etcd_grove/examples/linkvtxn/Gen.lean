/-
Lean-first (no Rocq counterpart).

The proof of `Gen`: `RandomUint64`, then `genFrom`'s input, boxed.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.linkvtxn.Gen
public import Spec.github_com.mit_pdos.etcd_grove.examples.linkvtxn.genFrom
public import Perennial.Proof.github_com.goose_lang.primitive.Link

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace linkvtxn

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.linkvtxn

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.linkvtxn.Assumptions]

theorem Gen.wp_proof (wp_genFrom : genFrom.spec (GF := GF) (hG := hG)) :
    Gen.spec (GF := GF) (hG := hG) := by
  unfold Gen.spec lintest.genSpec
  iintro %id
  wp_start as _
  wp_auto
  wp_apply github_com.goose_lang.primitive.wp_RandomUint64 as %n _
  wp_apply wp_genFrom n as %x %Hx
  iapply HΦ
  imodintro
  ipureintro
  exact ⟨x, rfl, Hx⟩

end proof

end linkvtxn
end EtcdGrove
end Perennial
