/- Lean-first (no Rocq counterpart).

`walRead(h)` (`examples/etcd/wal/ref.go`): what a restart reads from the files of a WAL whose
history is `h` (`tRead`), for a well-formed history.
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
abbrev walRead.spec : Prop :=
  ∀ (s : GoSlice) (h : List TOp),
  tHistWf h →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.wal ∗ opsRep s h }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.wal.walRead)) (Val #s))
  {{ (v : contents) (ok : Bool), RET (PairV #v #ok); readRes (tRead h) v ok }}

end spec

end etcd_wal
end EtcdGrove
end Perennial
