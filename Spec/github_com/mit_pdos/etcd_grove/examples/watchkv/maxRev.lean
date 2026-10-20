/- Lean-first (no Rocq counterpart). `maxRev(oks)` (watchkv.go): at least every revision of
`oks`, and not negative. -/
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
abbrev maxRev.spec : Prop :=
  ∀ (sl : GoSlice) (oks : List wrec) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.watchkv ∗
      sl ↦*{dq} oks }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.watchkv.maxRev)) (Val #sl))
  {{ (m : w64), RET #m; sl ↦*{dq} oks ∗
      ⌜0 ≤ sint.Z m ∧ ∀ p ∈ oks, sint.Z p.rev' ≤ sint.Z m⌝ }}

end spec

end watchkv
end EtcdGrove
end Perennial
