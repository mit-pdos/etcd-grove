/-
`idutil.lowbit(x, n)` (`id.go`): the `n` low bits of `x`. Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.pkg.v3.idutil.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.pkg.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- `lowbit(x, n)` for `n ≤ 64` is `x & (2 ^ n - 1)` (`math.MaxUint64 >> (64 - n)`; Perennial's
shifts do not truncate the count, so `n > 64`, whose `64 - n` wraps, would give `0`: excluded,
the code calls it with `40` and `48`). -/
abbrev idutil.lowbit.spec : Prop :=
  ∀ (x n : w64), uint.Z n ≤ 64 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.idutil }}
    (App (App (Val (@! idutil.lowbit)) (Val #x)) (Val #n))
  {{ RET #(x &&& W64 (2 ^ uint.nat n - 1)); True }}

end spec

end EtcdGrove
end Perennial
