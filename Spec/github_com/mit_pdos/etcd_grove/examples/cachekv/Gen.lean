/- Lean-first (no Rocq counterpart). `Gen()` (cachekv.go): a key of `genKeys` and a value of
`genVals`, whatever `primitive.RandomUint64` returns. -/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.cachekv.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace cachekv

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode github_com.mit_pdos.etcd_grove.examples.cachekv

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.cachekv.Assumptions]

/-- See the file header. -/
abbrev Gen.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.cachekv }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.cachekv.Gen)) (Val #()))
  {{ (p : ckv), RET #p; ⌜GenKv p⌝ }}

end spec

end cachekv
end EtcdGrove
end Perennial
