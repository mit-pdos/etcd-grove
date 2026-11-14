/-
`decodeOracle(s)` (oracle.go) on an oracle's encoding of at most 1 GiB (`tOrSmall`, which the oracle
file's invariant keeps): the oracle and `true`. To be proved (with `decoder.u64`/`hs`/`ops`; the
handoff's step 1). `freshOracle()`: the fresh oracle. Lean-first (no Rocq counterpart).
-/
module

public import LinuxFs.Proof.github_com.mit_pdos.etcd_grove.examples.etcd.wal.Inv
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
abbrev decodeOracle.spec : Prop :=
  ∀ (o : TOracle), tOrSmall o →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.wal }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.wal.decodeOracle)) (Val #(tEncodeOracle o)))
  {{ (v : oracle), RET (PairV #v #true); oracleRep v o }}

end spec

end etcd_wal
end EtcdGrove
end Perennial
