/-
`ClientStep(brs, holed, kind, a)` (`examples/lib/cluster3/cluster3.go`, until 2026-11-05 package `partition`'s; `notes/client-cut-plan.md` K0):
blackholes (once: `holed[a]` says whether it is), unblackholes, or drops the connections of member
`a`'s bridge; an index out of range does nothing. Lean-first (no Rocq counterpart).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.cluster3.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace cluster3

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.lib.cluster3.Assumptions]

/-- **`ClientStep(brs, holed, kind, a)`**, over the read-only slice of bridges `bs`, each owned
with its flag "blackholed" (`ownBridge`), the flags the slice `holed` holds: it returns, with the
flags as `holed` holds them then. -/
abbrev ClientStep.spec : Prop :=
  ∀ (brs holed : GoSlice) (bs : List GoInterface) (hs : List Bool) (kind a : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.cluster3 ∗
      brs ↦*□ bs ∗ holed ↦* hs ∗
      ([∗list] br; h ∈ bs; hs, ∃ addr : GoString, bridge.ownBridge br addr h) }}
    (App (App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.lib.cluster3.ClientStep))
      (Val #brs)) (Val #holed)) (Val #kind)) (Val #a))
  {{ RET #(); ∃ hs' : List Bool, holed ↦* hs' ∗
      ([∗list] br; h ∈ bs; hs', ∃ addr : GoString, bridge.ownBridge br addr h) }}

end spec

end cluster3
end EtcdGrove
end Perennial
