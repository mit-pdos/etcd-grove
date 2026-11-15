/- Lean-first (no Rocq counterpart). `p.meta()` (`examples/osfs/bboltfs/page.go`): the address 16 bytes past `p`, after the page header, where the page's meta is viewed (`Pages.lean`, `pageMeta_view`). -/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs.Meta

@[expose] public section

noncomputable section

namespace Perennial

open Fs
namespace EtcdGrove
namespace osfs_bboltfs

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs.Assumptions]

/-- See the file header. -/
abbrev Page.«meta».spec : Prop :=
  ∀ (p : Loc),
    {{ (⌜0 < p.addr ∧ p.addr + 16 ≤ maxAddr⌝ : IProp GF) }}
      (App (Val (p @!! go.GoType.PointerType Page.ty @!! go!"meta")) (Val #()))
    {{ RET #(p +ₗ 16); True }}

end spec

end osfs_bboltfs
end EtcdGrove
end Perennial
