/- Lean-first (no Rocq counterpart).

`(*member).hs()` (`examples/etcd/wal/wal.go`): the member's hard state (its fields `term`, `vote`,
`commit`).
-/
module

public import WalTester.Proof.github_com.mit_pdos.etcd_grove.examples.etcd.wal.Rep

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_wal

open Iris Iris.BI github_com.mit_pdos.etcd_grove.examples.etcd.wal

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.wal.Assumptions]

/-- See the file header. -/
abbrev member.hs.spec : Prop :=
  ∀ (m : Loc) (t vo cm : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.wal ∗
      m.[member, go!"term"] ↦ t ∗ m.[member, go!"vote"] ↦ vo ∗ m.[member, go!"commit"] ↦ cm }}
    (App (Val (m @!! go.GoType.PointerType member.ty @!! go!"hs")) (Val #()))
  {{ RET #(hardState.mk t vo cm); m.[member, go!"term"] ↦ t ∗ m.[member, go!"vote"] ↦ vo ∗
      m.[member, go!"commit"] ↦ cm }}

end spec

end etcd_wal
end EtcdGrove
end Perennial
