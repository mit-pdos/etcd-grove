/- Lean-first (no Rocq counterpart). `pickMeta(meta0, meta1)` (`examples/bboltfs/page.go`): the valid meta with the higher txid (`meta0` on a tie), else the other if it is valid, else nil (`pickMetaRes`), read through any fractions of the metas (mapped meta pages). -/
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
abbrev pickMeta.spec : Prop :=
  ∀ (m0 m1 : Loc) (v0 v1 : Meta) (dq0 dq1 : DFrac),
    {{ (m0 ↦{dq0} v0 ∗ m1 ↦{dq1} v1 ∗ ⌜0 < m0.addr ∧ 0 < m1.addr⌝ : IProp GF) }}
      (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.bboltfs.pickMeta)) (Val #m0)) (Val #m1))
    {{ RET #(pickMetaRes m0 v0 m1 v1); m0 ↦{dq0} v0 ∗ m1 ↦{dq1} v1 }}

end spec

end bboltfs
end EtcdGrove
end Perennial
