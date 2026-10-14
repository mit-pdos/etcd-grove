/-
The ghost refinement for `StepR` at a static configuration (2026-10-14, reconfiguration stage
B3).

`ownRaftGhost_stepR`: a `StepR` derivation whose configurations keep the ghost state's voters
(`StaticAdm γ.reCfg`), from a state at them whose non-follower is a voter (`RoleVoter`, which
the code has as `ownRaftPhys`'s `Hvoter`), updates the ghost state as `StepC` does: by
`stepR_static` it is a `StepC (CfgM.simple γ.reCfg ∅)` derivation of the protocol states, which
`ownRaftGhost_stepC` takes. The new rules are stuttering steps for the ghost (`advance`,
`applySnap`, `applyConf`, `propDrop` change no `PState`; `stepDown` cannot fire). The ghost
state is unchanged: it holds the `PState` only (`RState.p`).
-/
module

public import Proof.go_etcd_io.raft.v3.Protocol.Refinement
public import Proof.go_etcd_io.raft.v3.Protocol.StepR

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI GMap go_etcd_io.raft.v3

section ghost
variable [FfiSyntax]
variable {GF : BundledGFunctors} [AllG GF] [InvGS GF]

theorem ownRaftGhost_stepR (γ : RaftNames) (dec : CCDec) (id : w64) (r : RState)
    (recv : List Msg) (r' : RState) (HS : StaticR γ.reCfg r) (HV : RoleVoter id γ.reCfg r) :
    StepR (StaticAdm γ.reCfg) dec id r recv r' →
    ⊢ ([∗list] m ∈ recv, isMessage (GF := GF) γ m) -∗
      rdCred γ (rdCount recv) -∗
      ownRaftGhost γ id r.p ={⊤}=∗
      ownRaftGhost γ id r'.p := by
  intro Hstep
  iintro Hrecv Hcr Hown
  ihave %Hst := ownRaftGhost_static γ id r.p $$ Hown
  iapply ownRaftGhost_stepC γ _ (CfgStatic.simple γ ∅ Hst) id r.p recv r'.p
    (stepR_static Hstep HS HV).1 $$ Hrecv Hcr Hown

end ghost

end EtcdGrove
end Perennial
