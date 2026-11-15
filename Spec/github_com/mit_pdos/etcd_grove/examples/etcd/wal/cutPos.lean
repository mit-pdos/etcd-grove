/- Lean-first (no Rocq counterpart).

`cutPos(h, b)` (`examples/etcd/wal/ref.go`): whether a WAL file can start at position `b ≤ |h|`
(`tCutPos`).
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
abbrev cutPos.spec : Prop :=
  ∀ (s : GoSlice) (h : List TOp) (b : w64),
  0 ≤ sint.Z b → sint.nat b ≤ h.length →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.wal ∗ opsRep s h }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.wal.cutPos)) (Val #s)) (Val #b))
  {{ RET #(tCutPos h (sint.nat b)); True }}

end spec

end etcd_wal
end EtcdGrove
end Perennial
