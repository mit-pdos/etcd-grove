/- Lean-first (no Rocq counterpart).

`appendEnts(b, old, es)` (`examples/etcd/wal/ref.go`): never panics, and returns entries of `old` and
`es` only (what `opResend` re-sends must be entries the history saved).
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
abbrev appendEnts.spec : Prop :=
  ∀ (b : w64) (old es : GoSlice) (olds ess : List TEnt),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.wal ∗
      old ↦*□ olds ∗ es ↦*□ ess }}
    (App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.wal.appendEnts)) (Val #b))
      (Val #old)) (Val #es))
  {{ (r : GoSlice), RET #r; ∃ rs : List TEnt, r ↦*□ rs ∗ ⌜∀ e ∈ rs, e ∈ olds ∨ e ∈ ess⌝ }}

end spec

end etcd_wal
end EtcdGrove
end Perennial
