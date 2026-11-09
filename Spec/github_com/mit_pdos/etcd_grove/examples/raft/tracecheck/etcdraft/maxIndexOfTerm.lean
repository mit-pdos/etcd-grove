/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): `maxIndexOfTerm(xlog, t)`:
`MaxOrZero({n \in DOMAIN xlog : xlog[n].term = t})` (`maxIndexOfTerm`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Rep

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Etcdraft

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Assumptions]

/-- `maxIndexOfTerm(xlog, t)`: the last (1-based) index of an entry of term `t`, 0 if none. The
log shorter than `2^63 - 1` (the Go's counter runs to `len(xlog) + 1` in `int`). -/
abbrev maxIndexOfTerm.spec : Prop :=
  ∀ (sl : GoSlice) (l : List Entry) (t : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft ∗
      logRO sl l ∗ ⌜(l.length : Int) < 2 ^ 63 - 1⌝ }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.maxIndexOfTerm))
      (Val #sl)) (Val #t))
  {{ (r : w64), RET #r; ⌜sint.Z r = maxIndexOfTerm l (sint.Z t)⌝ }}

end spec

end Etcdraft
end EtcdGrove
end Perennial
