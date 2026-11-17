/-
`encodeOracle(o)` (oracle.go): the oracle's encoding (`tEncodeOracle`, `Defs.lean`), the oracle kept.
To be proved (with `putHS`, `putOps`; `putU64` is). Lean-first (no Rocq counterpart).
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
abbrev encodeOracle.spec : Prop :=
  ∀ (v : oracle) (o : TOracle),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.wal ∗
      oracleRep v o }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.wal.encodeOracle)) (Val #v))
  {{ RET #(tEncodeOracle o); oracleRep v o }}

end spec

end etcd_wal
end EtcdGrove
end Perennial
