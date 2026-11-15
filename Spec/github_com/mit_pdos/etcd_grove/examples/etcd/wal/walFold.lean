/- Lean-first (no Rocq counterpart).

`walFold(h)` (`examples/etcd/wal/ref.go`): never panics, and the entries of what it returns are
entries some `Save` of `h` saved (what `opResend` re-sends: well formed when `h` is).
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
abbrev walFold.spec : Prop :=
  ∀ (s : GoSlice) (h : List TOp),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.wal ∗ opsRep s h }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.wal.walFold)) (Val #s))
  {{ (v : contents), RET #v; ∃ c : TContents, contentsRep v c ∗
      ⌜∀ e ∈ c.ents, ∃ o ∈ h, o.snap = false ∧ e ∈ o.ents⌝ }}

end spec

end etcd_wal
end EtcdGrove
end Perennial
