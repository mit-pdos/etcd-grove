/- Lean-first (no Rocq counterpart).

`(*member).size()` (`examples/etcd/wal/wal.go`): an entry size, 16 to 139999 bytes (so the entries
`tEntWf` asks of the tester's: at least the salt's 8 bytes, at most 140000).
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
abbrev member.size.spec : Prop :=
  ∀ (m r : Loc) (v : rnd),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.wal ∗
      m.[member, go!"r"] ↦ r ∗ r ↦ v }}
    (App (Val (m @!! go.GoType.PointerType member.ty @!! go!"size")) (Val #()))
  {{ (sz : w64), RET #sz; m.[member, go!"r"] ↦ r ∗ (∃ v' : rnd, r ↦ v') ∗
      ⌜16 ≤ uint.nat sz ∧ uint.nat sz < 140000⌝ }}

end spec

end etcd_wal
end EtcdGrove
end Perennial
