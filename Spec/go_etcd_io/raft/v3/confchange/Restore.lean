/-
Port of `election_proof/spec_confchange_Restore.v` (feb5c73d4).

Lean notes:
* Rocq's `(#cfgv, #prsm, #interface.nil)` is the left-nested
  `PairV (PairV #cfgv #prsm) #interface.nil`.
* Rocq's `let tv := chg.(Tracker')` is inlined: `tv` is written `chg.Tracker'`.
-/
module

public import Proof.go_etcd_io.raft.v3.InvRaftPhys

@[expose] public section

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

/-- `confchange.Restore chg cs` replays a `ConfState` onto the empty configuration
`chg.Tracker` and returns the resulting `Config` and `ProgressMap`.

**Not translated** (`new/code/go_etcd_io/raft/v3/confchange.v.toml` translates only
the `Changer` type), so this triple is an `Axiom` -- and, unlike `slices.Sort`, one
about **core raft** code. It is stated for the one case this development needs: a
voters-only `ConfState` applied to the empty tracker `MakeProgressTracker` builds. Read
against the Go (`confchange/restore.go`, `confchange/confchange.go`) it says:

- `toConfChangeSingle` turns `cs` into no outgoing changes and one `AddNode id` per
  `id ∈ cs.Voters`, since `VotersOutgoing`, `Learners` and `LearnersNext` are empty;
- `chain` runs one `Changer.Simple(AddNode id)` per voter. Each `Simple` starts with
  `checkAndCopy`, which `Clone`s the config (a fresh `Voters[0]` map; `Voters[1]`,
  `Learners`, `LearnersNext` stay `nil`; `AutoLeave` is not copied, so `false`) and
  copies the progress map into a fresh one, each `Progress` shallow-copied into a fresh
  allocation. `makeVoter` on a new id calls `initProgress`, which adds `id` to
  `Voters[0]` and allocates a `Progress` with `State = StateProbe`, `IsLearner = false`
  and a fresh `NewInflights(MaxInflight, MaxInflightBytes)`; on a repeated id it only
  re-marks it a voter. `apply` **skips `NodeID = 0`**, hence the premise
  `0 ∉ voters`. No error is reachable: the config is never joint, one voter changes per
  step (`symdiff ≤ 1`), and `checkInvariants` holds throughout;
- so the result is a fresh voter map and a fresh progress map, both with domain
  `set voters`, each `Progress` owned exactly once (the intermediate copies are
  garbage, and so are the tracker's original maps, which are only read).

**`voters ≠ []` is load-bearing for soundness, not just for the caller.** With no
voters there are no ops, and `chain` returns `chg.Tracker.Config` and
`chg.Tracker.Progress` *themselves* -- the maps the premise already owns. A
postcondition handing out fresh points-tos for them would then duplicate ownership,
i.e. prove `False`.

`NoDup voters` is *not* needed here (`Restore` de-duplicates); it is needed by
`assertConfStatesEquivalent`, whose `Equivalent` check fails on a `ConfState` with a
repeated voter.

`MaxInflight`'s bound is what `ownProgress` (via `InflightsOk`) asks of the fresh
`Inflights`; see `spec_tracker_NewInflights.v`. -/
abbrev confchange.Restore.spec : Prop :=
  ∀ (chg : confchange.Changer) (cs : raftpb.ConfState)
    (voters : List w64) (dq : DFrac) (v0 : Loc),
  voters ≠ [] →
  W64 0 ∉ voters →
  cs.VotersOutgoing'.len = W64 0 →
  cs.Learners'.len = W64 0 →
  cs.LearnersNext'.len = W64 0 →
  (0 ≤ sint.Z chg.Tracker'.MaxInflight' ∧ sint.Z chg.Tracker'.MaxInflight' < 2 ^ 62) →
  -- the empty configuration
  chg.Tracker'.Config'.Voters'.arr = [v0, map.nil] →
  chg.Tracker'.Config'.Learners' = map.nil →
  chg.Tracker'.Config'.LearnersNext' = map.nil →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.confchange ∗
      cs.Voters' ↦*{dq} voters ∗
      v0 ↦$ (∅ : GMap w64 Unit) ∗
      chg.Tracker'.Progress' ↦$□ (∅ : GMap w64 Loc) }}
    (App (App (Val #(functions confchange.Restore [])) (Val #chg)) (Val #cs))
  {{ (cfgv : tracker.Config) (prsm : Loc) (prs : GMap w64 Loc)
      (vref : Loc) (vm : GMap w64 Unit),
      RET (PairV (PairV #cfgv #prsm) #interface.nil);
      cs.Voters' ↦*{dq} voters ∗
      v0 ↦$ (∅ : GMap w64 Unit) ∗
      chg.Tracker'.Progress' ↦$□ (∅ : GMap w64 Loc) ∗
      ⌜cfgv.Voters'.arr = [vref, map.nil] ∧
        cfgv.Learners' = map.nil ∧
        cfgv.LearnersNext' = map.nil ∧
        cfgv.AutoLeave' = false⌝ ∗
      vref ↦$ vm ∗ ⌜domSet vm = GMap.listToSet voters⌝ ∗
      prsm ↦$ prs ∗ ⌜domSet prs = GMap.listToSet voters⌝ ∗
      ([∗map] _k ↦ pr ∈ prs, ∃ p, ownProgress pr p) }}

end spec

end EtcdGrove
end Perennial
