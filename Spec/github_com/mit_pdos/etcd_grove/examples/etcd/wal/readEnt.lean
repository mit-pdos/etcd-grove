/- Lean-first (no Rocq counterpart).

`readEnt(b, ents, e)` (`examples/etcd/wal/ref.go`): `ReadAll`'s step on the entry `e` above the
base `b` (`tReadEnt`), for an entry whose index is below `2^63` (the tester's: so the slice it
makes has a valid capacity).
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
abbrev readEnt.spec : Prop :=
  ∀ (b : w64) (s : GoSlice) (es : List TEnt) (e : TEnt),
  uint.nat e.index' < 2 ^ 63 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.wal ∗ s ↦*□ es }}
    (App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.wal.readEnt)) (Val #b)) (Val #s))
      (Val #e))
  {{ (r : GoSlice) (ok : Bool), RET (PairV #r #ok); entsRes (tReadEnt b es e) r ok }}

end spec

end etcd_wal
end EtcdGrove
end Perennial
