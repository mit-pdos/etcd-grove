/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Spec/github_com/hashicorp/raft/sortUint64s.lean (241f27e).
-/
/-
`raft.sortUint64s`'s spec: in-place sort of a `[]uint64` in increasing (unsigned) order.
After the call the slice holds a permutation of its input that is sorted by `uint.Z`; the
code never panics and never indexes out of bounds.
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.Assumptions]

/-- `raft.sortUint64s(s)` sorts `s` in place by `uint.Z`: it ends holding a permutation of
its input, sorted (pairwise `uint.Z · ≤ uint.Z ·`). -/
abbrev github_com.hashicorp.raft.sortUint64s.spec : Prop :=
  ∀ (s : GoSlice) (xs : List w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗
      "Hs" ∷ s ↦* xs ∗
      "%Hbound" ∷ ⌜xs.length ≤ 2 ^ 62⌝ }}
    (App (Val (@! github_com.hashicorp.raft.sortUint64s)) (Val #s))
  {{ (xs' : List w64), RET #();
      "Hs" ∷ s ↦* xs' ∗
      "%Hperm" ∷ ⌜xs ≡ₚ xs'⌝ ∗
      "%Hsorted" ∷ ⌜List.Pairwise (fun x y => uint.Z x ≤ uint.Z y) xs'⌝ }}

end spec

end Perennial
