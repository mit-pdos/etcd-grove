/-
`client.Rotate(xs, i)`: a new slice of `xs` from its `i`-th (mod length) element on (`rotateL`). Its
index arithmetic `(i+j)%len(xs)` needs, for a non-empty `xs`, `0 ≤ i` and `i + len(xs) ≤ 2^63` (otherwise Go panics: a negative
index); its callers pass a client machine's index (`nonissues/grove-dist-rotate-doc.md`).
Lean-first (no Rocq counterpart); N7-kv, M1 (`notes/etcd-dist-n7kv.md`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.KvDefs
@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_dist

open Iris Iris.BI
open github_com.mit_pdos.etcd_grove.examples.etcd.dist

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : client.Assumptions]

/-- `Rotate(xs, i)` returns a new slice `rotateL xsL i`. -/
abbrev Rotate.spec : Prop :=
  ∀ {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] {T : go.GoType} [IntoValTyped (GF := GF) V T]
    [Inhabited V] (xs : GoSlice) (dq : DFrac) (xsL : List V) (i : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client ∗
      xs ↦*{dq} xsL ∗ ⌜xsL ≠ [] → 0 ≤ sint.Z i ∧ sint.Z i + xsL.length ≤ 2 ^ 63⌝ }}
    (App (App (Val #(functions client.Rotate [T])) (Val #xs)) (Val #i))
  {{ (out : GoSlice), RET #out; xs ↦*{dq} xsL ∗ out ↦* rotateL xsL (sint.nat i) }}

end spec

end etcd_dist
end EtcdGrove
end Perennial
