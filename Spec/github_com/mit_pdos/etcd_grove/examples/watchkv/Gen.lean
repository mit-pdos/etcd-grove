/- Lean-first (no Rocq counterpart). `Gen()` (watchkv.go): a key of `genKeys` and a value of
`genVals`, whatever `primitive.RandomUint64` returns. -/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.watchkv.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace watchkv

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode github_com.mit_pdos.etcd_grove.examples.watchkv

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.watchkv.Assumptions]

/-- See the file header. -/
abbrev Gen.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.watchkv }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.watchkv.Gen)) (Val #()))
  {{ (p : wkv), RET #p; ⌜GenKv p⌝ }}

end spec

end watchkv
end EtcdGrove
end Perennial
