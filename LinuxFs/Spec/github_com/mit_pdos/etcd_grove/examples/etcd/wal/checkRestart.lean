/- Lean-first (no Rocq counterpart).

`checkRestart(o, c)` (`examples/etcd/wal/wal.go`): the restart's check. It does not panic when some
candidate's image at its mark reads `c` from a purged prefix within its purge bound (`tCheckNext o c ≠
[]`, from `tCheckNext_ne_nil`), and returns the oracle `tCheckRestart o c` (the images that read `c`,
with their bounds); the argument oracle is untouched.
-/
module

public import LinuxFs.Proof.github_com.mit_pdos.etcd_grove.examples.etcd.wal.Rep
public import LinuxFs.Proof.github_com.mit_pdos.etcd_grove.examples.etcd.wal.Check

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
abbrev checkRestart.spec : Prop :=
  ∀ (vo : oracle) (vc : contents) (o : TOracle) (c : TContents),
  tCheckWf o → tCheckNext o c ≠ [] →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.wal ∗
      oracleRep vo o ∗ contentsRep vc c }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.wal.checkRestart)) (Val #vo))
      (Val #vc))
  {{ (v : oracle), RET #v; oracleRep vo o ∗ oracleRep v (tCheckRestart o c) }}

end spec

end etcd_wal
end EtcdGrove
end Perennial
