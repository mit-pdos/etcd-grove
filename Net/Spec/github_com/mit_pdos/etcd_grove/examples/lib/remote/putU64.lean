/-
`putU64(b, x)`: writes `x`'s 8 little-endian bytes at the start of `b` (at least 8 long).
Proved in `Net/Proof/.../lib/remote/putU64.lean`.
-/
module

public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.lib.remote.Wire

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Net

namespace github_com.mit_pdos.etcd_grove.examples.lib.remote

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem' : github_com.mit_pdos.etcd_grove.examples.lib.remote.Assumptions] [field_sem : net.FieldAssumptions]
variable [π : NetProtoGS]

/-- See the file header. -/
abbrev putU64.spec : Prop :=
  ∀ (b : GoSlice) (vs : List w8) (x : w64), 8 ≤ vs.length →
  {{ (b ↦* vs : IProp GF) }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.lib.remote.putU64)) (Val #b)) (Val #x))
  {{ RET #(); b ↦* (u64Le x ++ vs.drop 8) }}

end spec

end github_com.mit_pdos.etcd_grove.examples.lib.remote
end Perennial
