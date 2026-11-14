/- Lean-first (no Rocq counterpart).

`putHS(b, h)` (`examples/etcd/wal/oracle.go`): appends the hard state's 24 bytes (`tHsBytes`).
-/
module

public import LinuxFs.Proof.github_com.mit_pdos.etcd_grove.examples.etcd.wal.Rep

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
abbrev putHS.spec : Prop :=
  ∀ (b : GoSlice) (bs : List w8) (h : THs),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.wal ∗
      b ↦* bs ∗ ownSliceCap w8 b (DFrac.own 1) }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.wal.putHS)) (Val #b)) (Val #h))
  {{ (b' : GoSlice), RET #b'; b' ↦* (bs ++ tHsBytes h) ∗ ownSliceCap w8 b' (DFrac.own 1) }}

end spec

end etcd_wal
end EtcdGrove
end Perennial
