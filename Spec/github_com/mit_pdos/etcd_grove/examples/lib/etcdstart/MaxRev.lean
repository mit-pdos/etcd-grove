/- Lean-first (no Rocq counterpart). `MaxRev(oks)` (`examples/lib/etcdstart/watch.go`; watchkv's until 2026-10-22, D33): at least every revision of
`oks`, and not negative. -/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.WatchBase

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcdstart

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode github_com.mit_pdos.etcd_grove.examples.lib.etcdstart

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Assumptions]

/-- See the file header. -/
abbrev MaxRev.spec : Prop :=
  ∀ (sl : GoSlice) (oks : List wrec) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart ∗
      sl ↦*{dq} oks }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.MaxRev)) (Val #sl))
  {{ (m : w64), RET #m; sl ↦*{dq} oks ∗
      ⌜0 ≤ sint.Z m ∧ ∀ p ∈ oks, sint.Z p.Rev' ≤ sint.Z m⌝ }}

end spec

end etcdstart
end EtcdGrove
end Perennial
