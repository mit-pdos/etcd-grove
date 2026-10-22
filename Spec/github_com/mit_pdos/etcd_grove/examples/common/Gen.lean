/- Lean-first (no Rocq counterpart). `Gen(keys)` (`examples/common/watch.go`; watchkv's `Gen()`
until 2026-10-22, D33, at its keys): a key of `keys` (not empty) and a value of `genVals`, whatever
`primitive.RandomUint64` returns. -/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.common.WatchBase

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace common

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode github_com.mit_pdos.etcd_grove.examples.common

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.common.Assumptions]

/-- See the file header. -/
abbrev Gen.spec : Prop :=
  ∀ (ksl : GoSlice) (ks : List GoString), 0 < ks.length → ks.length < 2 ^ 63 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.common ∗
      ksl ↦*□ ks }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.common.Gen)) (Val #ksl))
  {{ (p : wkv), RET #p; ⌜GenKv ks p⌝ }}

end spec

end common
end EtcdGrove
end Perennial
