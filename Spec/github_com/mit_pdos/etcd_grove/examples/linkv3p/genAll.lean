/- Lean-first (no Rocq counterpart). `genAll(n)` (linkv3p.go): `n` puts of `genPut`, in a fresh
slice. -/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.linkv3p.genPut

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
abbrev genAll.spec : Prop :=
  ∀ (n : w64), 0 ≤ sint.Z n →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.linkv3p }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.linkv3p.genAll)) (Val #n))
  {{ (sl : GoSlice), RET #sl; ∃ ps : List wkv, sl ↦* ps ∗
      ⌜ps.length = sint.nat n ∧ ∀ p ∈ ps, GenKv p⌝ }}

end spec

end linkv3p
end EtcdGrove
end Perennial
