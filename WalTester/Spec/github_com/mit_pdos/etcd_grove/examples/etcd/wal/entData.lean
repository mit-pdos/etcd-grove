/- Lean-first (no Rocq counterpart).

`entData(e)` (`examples/etcd/wal/wal.go`): a fresh slice holding `tEntData e` (`e.size` bytes: the
salt's, then the pattern). `e.size` below `2^63` (`make([]byte, 0, e.size)` takes an `int`).
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
abbrev entData.spec : Prop :=
  ∀ (e : TEnt), uint.nat e.size' < 2 ^ 63 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.wal }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.wal.entData)) (Val #e))
  {{ (b : GoSlice), RET #b; b ↦* tEntData e ∗ ownSliceCap w8 b (DFrac.own 1) }}

end spec

end etcd_wal
end EtcdGrove
end Perennial
