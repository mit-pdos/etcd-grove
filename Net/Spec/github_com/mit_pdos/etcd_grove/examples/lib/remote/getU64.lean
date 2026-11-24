/-
`getU64(b)`: the little-endian `uint64` of `b`'s first 8 bytes.
Proved in `Net/Proof/.../lib/remote/getU64.lean`.
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
abbrev getU64.spec : Prop :=
  ∀ (b : GoSlice) (dq : DFrac) (bs rem : List w8), bs.length = 8 →
  {{ (b ↦*{dq} (bs ++ rem) : IProp GF) }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.lib.remote.getU64)) (Val #b))
  {{ RET #(leToU64 bs); b ↦*{dq} (bs ++ rem) }}

end spec

end github_com.mit_pdos.etcd_grove.examples.lib.remote
end Perennial
