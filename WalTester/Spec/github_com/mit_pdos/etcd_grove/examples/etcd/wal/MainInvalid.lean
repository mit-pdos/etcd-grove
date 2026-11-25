/- Lean-first (no Rocq counterpart).

`Main(area, orDir)` (wal.go) on directories the tester's facts do not hold of (`¬ tArgsOk e`): `dirOk`
refuses one of them, and `Main` returns without a file system call.
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
abbrev Main.specInvalid : Prop :=
  ∀ (e : TEnv), ¬ tArgsOk e →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.wal }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.wal.Main)) (Val #e.area)) (Val #e.orDir))
  {{ RET #(); True }}

end spec

end etcd_wal
end EtcdGrove
end Perennial
