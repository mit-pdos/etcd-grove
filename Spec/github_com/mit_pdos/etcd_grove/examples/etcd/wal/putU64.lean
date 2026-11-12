/- Lean-first (no Rocq counterpart).

`putU64(b, x)` (`examples/etcd/wal/oracle.go`): appends `x`'s 8 bytes, little-endian (`tU64`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.wal.Rep

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
abbrev putU64.spec : Prop :=
  ∀ (b : GoSlice) (bs : List w8) (x : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.wal ∗
      b ↦* bs ∗ ownSliceCap w8 b (DFrac.own 1) }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.wal.putU64)) (Val #b)) (Val #x))
  {{ (b' : GoSlice), RET #b'; b' ↦* (bs ++ tU64 x) ∗ ownSliceCap w8 b' (DFrac.own 1) }}

end spec

end etcd_wal
end EtcdGrove
end Perennial
