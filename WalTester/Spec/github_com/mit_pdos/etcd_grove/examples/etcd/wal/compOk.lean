/- Lean-first (no Rocq counterpart).

`compOk(n, dots)` (`examples/etcd/wal/wal.go`): whether a path component of `n` bytes, all `.` if
`dots`, is nonempty, neither `.` nor `..`, and at most 255 bytes (`tCompOk`).
-/
module

public import WalTester.Proof.github_com.mit_pdos.etcd_grove.examples.etcd.wal.DirOk

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
abbrev compOk.spec : Prop :=
  ∀ (n : w64) (dots : Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.wal }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.wal.compOk)) (Val #n)) (Val #dots))
  {{ RET #(tCompOk (uint.nat n) dots); True }}

end spec

end etcd_wal
end EtcdGrove
end Perennial
