/-
The proof of counter's `Gen` (`Net/Spec/.../lib/remote/counter/Gen.lean`): `RandomUint64`, then
the comparison of its parity, boxed.
-/
module

public import Net.Spec.github_com.mit_pdos.etcd_grove.examples.lib.remote.counter.Gen
public import Perennial.Spec.github_com.goose_lang.primitive.RandomUint64

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace github_com.mit_pdos.etcd_grove.examples.lib.remote.counter

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.lib.remote.counter.Assumptions]

theorem Gen.wp_proof
    (wp_RandomUint64 : github_com.goose_lang.primitive.RandomUint64.spec (GF := GF) (hG := hG)) :
    Gen.spec (GF := GF) (hG := hG) := by
  unfold Gen.spec EtcdGrove.lintest.genSpec
  iintro %id
  wp_start as _
  wp_auto
  wp_apply wp_RandomUint64 as %n _
  iapply HΦ
  imodintro
  ipureintro
  exact ⟨_, rfl⟩

end proof

end github_com.mit_pdos.etcd_grove.examples.lib.remote.counter
end Perennial
