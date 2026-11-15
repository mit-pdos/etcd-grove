/- Lean-first (no Rocq counterpart).

`walSaveSnap(s, idx, term)` (`examples/etcd/wal/ref.go`): the read state after a snapshot record
(`tSaveSnap`).
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
abbrev walSaveSnap.spec : Prop :=
  ∀ (v : contents) (c : TContents) (idx term : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.wal ∗ contentsRep v c }}
    (App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.wal.walSaveSnap)) (Val #v))
      (Val #idx)) (Val #term))
  {{ (v' : contents), RET #v'; contentsRep v' (tSaveSnap c idx term) }}

end spec

end etcd_wal
end EtcdGrove
end Perennial
