/- Lean-first (no Rocq counterpart). `m.validate()` (`examples/bboltfs/page.go`): whether `*m` is valid (`metaValid`: the magic, the version, and a checksum equal to `metaSum`), read through any fraction of `*m` (a mapped meta page). -/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.bboltfs.Meta

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bboltfs

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode github_com.mit_pdos.etcd_grove.examples.bboltfs

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.bboltfs.Assumptions]

/-- See the file header. -/
abbrev Meta.validate.spec : Prop :=
  ∀ (m : Loc) (v : Meta) (dq : DFrac),
    {{ (m ↦{dq} v ∗ ⌜0 < m.addr⌝ : IProp GF) }}
      (App (Val (m @!! go.GoType.PointerType Meta.ty @!! go!"validate")) (Val #()))
    {{ RET #(decide (metaValid v)); m ↦{dq} v }}

end spec

end bboltfs
end EtcdGrove
end Perennial
