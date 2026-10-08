/-
Port of election_proof/spec_tracker_NewInflights.v (feb5c73d4).

Lean notes:
* Rocq's `own_Inflights` (the public, record-indexed predicate) is `ownInflights`;
  `inflights_new` is `inflightsNew` (`Defs.lean`). The chained `0 ≤ x < 2^62` is a
  conjunction.
-/
import EtcdGrove.Raft.InvRaftPhys

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `NewInflights` allocates one.

The premise bounds the ring size. It is what `ownInflights`'s ring-buffer invariant
(`InflightsOk`, `InvTracker.lean`) asks of a fresh `Inflights`: a negative `size` would
make `0 ≤ len(buffer) ≤ size` false, and a `size` at or above `2^62` would let
`Inflights.grow`'s `len(buffer) * 2` overflow. The one caller on this path is `reset`'s
`Visit` closure, passing `r.trk.MaxInflight`, which `ownTracker`'s `HmaxInfl` bounds.
Added 2026-09-20 with the invariant. The window is empty: `inflightsNew size maxBytes`
(`Defs.lean`). -/
abbrev tracker.NewInflights.spec : Prop :=
  ∀ (size maxBytes : w64),
  0 ≤ sint.Z size ∧ sint.Z size < 2 ^ 62 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.tracker }}
    (App (App (Val #(functions tracker.NewInflights [])) (Val #size)) (Val #maxBytes))
  {{ (l : Loc), RET #l; ownInflights l (inflightsNew size maxBytes) }}

end spec

end EtcdGrove
end Perennial
