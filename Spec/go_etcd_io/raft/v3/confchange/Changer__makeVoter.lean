/-
`Changer.makeVoter` adds or promotes an id to a voter of the incoming config.
Lean-first (no Rocq counterpart); see `InvConfchange.lean`.
-/
module

public import Proof.go_etcd_io.raft.v3.InvConfchange

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `makeVoter(cfg, trk, id)`: `makeVoterM`. (Generalized 2026-10-12 from the voters-only
config `Restore` builds.) -/
abbrev confchange.Changer.makeVoter.spec : Prop :=
  ∀ (p cfgp trk : Loc) (chg : confchange.Changer) (base : GMap w64 tracker.Progress)
    (s : CCState) (id : w64) (dq : DFrac),
  (0 ≤ sint.Z chg.Tracker'.MaxInflight' ∧ sint.Z chg.Tracker'.MaxInflight' < 2 ^ 62) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.confchange ∗ p ↦{dq} chg ∗ ownWork chg base cfgp trk s }}
    (App (App (App (Val (p @!! go.GoType.PointerType confchange.Changer.ty @!! go!"makeVoter")) (Val #cfgp)) (Val #trk)) (Val #id))
  {{ RET #(); p ↦{dq} chg ∗ ownWork chg base cfgp trk (makeVoterM id s) }}

end spec

end EtcdGrove
end Perennial
