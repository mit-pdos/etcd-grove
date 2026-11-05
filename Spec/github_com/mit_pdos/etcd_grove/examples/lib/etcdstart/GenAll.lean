/- Lean-first (no Rocq counterpart). `GenAll(n, keys)` (`examples/lib/etcdstart/watch.go`; watchkv's until 2026-10-22, D33): `n` Puts of `Gen(keys)`, in a fresh
slice. -/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Gen

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
abbrev GenAll.spec : Prop :=
  ∀ (n : w64) (ksl : GoSlice) (ks : List GoString), 0 ≤ sint.Z n → 0 < ks.length →
  ks.length < 2 ^ 63 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart ∗
      ksl ↦*□ ks }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.GenAll)) (Val #n))
      (Val #ksl))
  {{ (sl : GoSlice), RET #sl; ∃ ps : List wkv, sl ↦* ps ∗
      ⌜ps.length = sint.nat n ∧ ∀ p ∈ ps, GenKv ks p⌝ }}

end spec

end etcdstart
end EtcdGrove
end Perennial
