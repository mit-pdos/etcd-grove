/-
`fits(o, room)` (oracle.go, 2026-11-15): whether the oracle's encoding with `room` more bytes stays within
`maxOracle` (`2^30`, `durable.Write`'s bound): `true` exactly when `tOrRoom o room`. The room is at most
`2^62`, so the sum does not wrap (the encoding is shorter than `2^63`, `len`'s bound). Lean-first (no Rocq
counterpart).
-/
module

public import LinuxFs.Proof.github_com.mit_pdos.etcd_grove.examples.etcd.wal.OrLen
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
abbrev fits.spec : Prop :=
  ∀ (v : oracle) (o : TOracle) (room : w64), uint.nat room ≤ 2 ^ 62 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.wal ∗
      oracleRep v o }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.wal.fits)) (Val #v)) (Val #room))
  {{ (b : Bool), RET #b; oracleRep v o ∗ ⌜b = true ↔ tOrRoom o (uint.nat room)⌝ }}

end spec

end etcd_wal
end EtcdGrove
end Perennial
