/- Lean-first (no Rocq counterpart).

`etcdstart.GenAll(n, keys)` (`examples/lib/etcdstart/watch.go`) **with its steps counted** (#50 N10a,
`notes/etcd-dist-plan.md` §24.7): `GenAll.spec` (`Spec/.../lib/etcdstart/GenAll.lean`, verbatim: `n` Puts
of `Gen(keys)` in a fresh slice), its post also `n < receiptBound GF`. The loop runs `n` iterations;
each resolves a function (`Gen`, `append`), a counted step, whose time receipt (`⧗ 1`, Perennial's `GooseLang/Receipts.lean`)
the proof keeps, so the loop ends holding `⧗ n`, and `n` exclusive receipts are fewer than the receipts'
bound (`receipt_lt`). So the count of the Puts is bounded by the execution's length (the adequacy
theorem's `receiptBound`, at most `etcdSteps`), not by a premise. Used by `RunWatch` for the writers'
Puts (`len(nodes) * nops`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Gen

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_dist_client

open Iris Iris.BI etcdstart

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Assumptions]

/-- See the file header. -/
abbrev GenAll_receipts.spec : Prop :=
  ∀ (n : w64) (ksl : GoSlice) (ks : List GoString), 0 ≤ sint.Z n → 0 < ks.length →
  ks.length < 2 ^ 63 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart ∗
      ksl ↦*□ ks }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.GenAll)) (Val #n))
      (Val #ksl))
  {{ (sl : GoSlice), RET #sl; ∃ ps : List wkv, sl ↦* ps ∗
      ⌜ps.length = sint.nat n ∧ (∀ p ∈ ps, GenKv ks p) ∧ sint.nat n < receiptBound GF⌝ }}

end spec

end etcd_dist_client
end EtcdGrove
end Perennial
