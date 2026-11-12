/- Lean-first (no Rocq counterpart).

`copyEnts(es)` (`examples/etcd/wal/ref.go`): a fresh copy of the entry slice.
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
abbrev copyEnts.spec : Prop :=
  ∀ (s : GoSlice) (es : List TEnt) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.wal ∗ s ↦*{dq} es }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.wal.copyEnts)) (Val #s))
  {{ (s' : GoSlice), RET #s'; s' ↦* es ∗ ownSliceCap TEnt s' (DFrac.own 1) ∗ s ↦*{dq} es }}

end spec

end etcd_wal
end EtcdGrove
end Perennial
