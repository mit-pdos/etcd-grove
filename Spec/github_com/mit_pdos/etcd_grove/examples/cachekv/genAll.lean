/- Lean-first (no Rocq counterpart). `genAll(n)` (cachekv.go): `n` Puts of `Gen`, in a fresh
slice. -/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.cachekv.Gen

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
abbrev genAll.spec : Prop :=
  ∀ (n : w64), 0 ≤ sint.Z n →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.cachekv }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.cachekv.genAll)) (Val #n))
  {{ (sl : GoSlice), RET #sl; ∃ ps : List ckv, sl ↦* ps ∗
      ⌜ps.length = sint.nat n ∧ ∀ p ∈ ps, GenKv p⌝ }}

end spec

end cachekv
end EtcdGrove
end Perennial
