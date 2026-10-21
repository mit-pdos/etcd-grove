/-
`(*raft).getWitnessVoteRequestReadiness` (raft#168, `raft.go`; 2026-10-19, witness support).
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

/-- `r.getWitnessVoteRequestReadiness(votesToWin)` (2026-10-20, at any configuration; until then
witness-free only): the configuration's witnesses are `[c.wit, 0]` (`ownTrackerC`), so

    if v1 > 1 && v2 > 1 { return nil }
    if w1 == 0 && w2 == 0 { return nil }
    w := map[uint64]bool{}; ...; if w1 > 0 { w[w1] = v1 == 1 }; return w

is `nil` without a witness or with both halves more than one vote short, else the map
`{c.wit ↦ (v1 = 1)}`: the witness is to be asked when the incoming half is one vote short.
`stepCandidate`'s `VotePending` arm ranges over it. -/
abbrev raft.getWitnessVoteRequestReadiness.spec : Prop :=
  ∀ (c : CfgM) (V : GSet w64) (r : Loc) (id : w64) (s : NState) (d : GoArray w64 2)
    (v1 v2 : w64),
  d.arr = [v1, v2] →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ ownRaftPhysCV c V r id s }}
    (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"getWitnessVoteRequestReadiness"))
      (Val #d))
  {{ (m : Loc), RET #m; ownRaftPhysCV c V r id s ∗
      (⌜m = map.nil ∧ (c.wit = W64 0 ∨ (1 < sint.Z v1 ∧ 1 < sint.Z v2))⌝ ∨
       ∃ ready : Bool, m ↦$ (<[c.wit := ready]> ∅ : GMap w64 Bool) ∗
         ⌜c.wit ≠ W64 0 ∧ (ready = true ↔ v1 = W64 1)⌝) }}

end spec

end EtcdGrove
end Perennial
