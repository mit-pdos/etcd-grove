/- Lean-first (no Rocq counterpart).

`walFoldChk(h)` (`examples/etcd/wal/ref.go`): the fold of the history through `readEnt` from the
zero contents (`tFoldChk`), `false` once an entry step fails; for a well-formed history (its
indices below `2^63`, `readEnt`'s premise).
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
abbrev walFoldChk.spec : Prop :=
  ∀ (s : GoSlice) (h : List TOp),
  tHistWf h →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.wal ∗ opsRep s h }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.wal.walFoldChk)) (Val #s))
  {{ (v : contents) (ok : Bool), RET (PairV #v #ok); readRes (tFoldChk h) v ok }}

end spec

end etcd_wal
end EtcdGrove
end Perennial
