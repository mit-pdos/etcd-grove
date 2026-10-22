/- Lean-first (no Rocq counterpart). `genPut()` (linkv3p.go): a key of `genKeys` and a value of
`genVals`, whatever `primitive.RandomUint64` returns (W4d of `notes/watch-cut-plan.md`: watchkv's `Gen`,
for linkv3p's copy). -/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.linkv3p.WatchBase

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace linkv3p

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode github_com.mit_pdos.etcd_grove.examples.linkv3p

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.linkv3p.Assumptions]

/-- See the file header. -/
abbrev genPut.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.linkv3p }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.linkv3p.genPut)) (Val #()))
  {{ (p : wkv), RET #p; ⌜GenKv p⌝ }}

end spec

end linkv3p
end EtcdGrove
end Perennial
