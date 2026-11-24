/-
`Codec()`: the counter's codec, a `remote.Codec` of seven function literals, which computes the
encodings and decodings of the far side's store `cR γ` (`codecOk`, `remote/Defs.lean`), for every
`γ` (the codec does not look at the store's state): an input `boxB b` is one byte (`1`: increment),
an output `Out{u, n}` the byte of `u` and `n`'s 8 little-endian bytes (`encOutB`); `IsRead` is
`!b`, `Unknown` is `Out{true, 0}`, `IsUnknown` the field `Unknown`.
Proved in `Net/Proof/.../lib/remote/counter/Codec.lean`.
-/
module

public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.lib.remote.counter.Defs

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Net

namespace github_com.mit_pdos.etcd_grove.examples.lib.remote.counter

open github_com.mit_pdos.etcd_grove.examples.lib.remote

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.lib.remote.counter.Assumptions]

/-- See the file header. -/
abbrev Codec.spec : Prop :=
  ∀ γ : GName,
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.remote.counter }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.lib.remote.counter.Codec)) (Val #()))
  {{ (cd : remote.Codec), RET #cd; codecOk (cR (GF := GF) γ) cd }}

end spec

end github_com.mit_pdos.etcd_grove.examples.lib.remote.counter
end Perennial
