/-
Port of election_proof/proof_raft__becomeFollower.v.
-/
module

public import Spec.go_etcd_io.raft.v3.raft__becomeFollower
public import Spec.go_etcd_io.raft.v3.raft__reset
public import Spec.go_etcd_io.raft.v3.traceBecomeFollower

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `raft.wp_store_stateC` at the value the Go code stores, the generated constant
`go_etcd_io.raft.v3.StateFollower` (`#(W64 0)`), which `wp_apply` does not unify with
`#(stateW64 .follower)` by itself. -/
private theorem wp_store_state_follower (c : CfgM) (r : Loc) (id : w64) (s : NState) :
    {{ ownRaftPhysCV (GF := GF) c c.voters r id s }}
      (App (Val (GoInstruction (GoStore StateType.ty)))
        (Val (PairV #(r.[raft, go!"state"]) go_etcd_io.raft.v3.StateFollower)))
    {{ RET #(); ownRaftPhysCV c c.voters r id { s with role := .follower } }} :=
  raft.wp_store_stateC (c := c) r id s .follower (fun h => absurd rfl h)

theorem raft.becomeFollower.wp_proof
    (wp_raft_reset : raft.reset.spec (GF := GF) (hG := hG))
    (wp_traceBecomeFollower : traceBecomeFollower.spec (GF := GF) (hG := hG)) :
    raft.becomeFollower.spec (GF := GF) (hG := hG) := by
  intro c r id s term lead Hle
  wp_start as Hphys
  wp_auto
  -- `r.step := stepFollower`
  wp_apply raft.wp_store_stepC $$ Hphys as Hphys
  -- `reset`'s state is left to the frame
  wp_apply wp_raft_reset c r id { s with stepfn := functions stepFollower [] } term Hle
    $$ [$Hphys] as %pvs ⟨Hphys, -⟩
  -- `Match` is irrelevant for a non-leader (`toPState`)
  -- `r.tick`, `r.lead := lead`, `r.state := StateFollower`
  wp_apply raft.wp_store_tickC (Hf := .inl rfl) $$ Hphys as Hphys
  wp_apply raft.wp_store_leadC $$ Hphys as Hphys
  wp_apply wp_store_state_follower $$ Hphys as Hphys
  wp_apply raft.wp_load_idC $$ Hphys as Hphys
  wp_apply raft.wp_load_TermC $$ Hphys as Hphys
  wp_raft_logC
  wp_apply wp_traceBecomeFollower
  iapply HΦ
  -- the stores above, in the order the Go code makes them, give `becomeFollower` up to
  -- the order of the record updates
  iapply ownRaftPhysC_eq (c := c) r id _ _ ?_ $$ Hphys
  rfl

end proof

end EtcdGrove
end Perennial
