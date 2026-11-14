/- Lean-first (no Rocq counterpart).

`putOps(b, h)` (`examples/etcd/wal/oracle.go`): appends the history's bytes (`tOpsBytes`): its length,
then each operation's fields and entries.
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
abbrev putOps.spec : Prop :=
  ∀ (b : GoSlice) (bs : List w8) (s : GoSlice) (h : List TOp),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.wal ∗
      b ↦* bs ∗ ownSliceCap w8 b (DFrac.own 1) ∗ opsRep s h }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.wal.putOps)) (Val #b)) (Val #s))
  {{ (b' : GoSlice), RET #b'; b' ↦* (bs ++ tOpsBytes h) ∗ ownSliceCap w8 b' (DFrac.own 1) }}

end spec

end etcd_wal
end EtcdGrove
end Perennial
