/-
Lean-first (no Rocq counterpart).

# The refinement to Antithesis's binding: `antSim_ready` (#33 S4, the invariant phase; parity B1)

Below `mskB1a`: `rdCtx_of` (the context after `GC`), then `ready_nonleader` (every kind but a
leader's) with its leader premises discharged: a win (`ready_win`), a proposal (`ready_prop`), a
commit (`ready_cmt`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Sim.ReadyMain
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Sim.ReadyWin
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Sim.Stmts

@[expose] public section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace AntSim

open AntCheck go_etcd_io.raft.v3

/-- **`antSim_ready` below `mskB1a`**: a reported `Ready` is a step of the binding, keeping the
relation (`antSim_ready.stmt` over `ReachIn msk`, for the runs `msk` admits; `R.boot` either way). -/
theorem antSim_ready_in [GooseExts] (msk : SimMask) (hmsk : msk ≤ mskB1a) :
    ∀ (R : RunCfg) (dec : CCDec) (S : AntCheck.State) (V : Fin R.N → NodeView) (net : List Msg)
      (xnet : List XMsg) (evs : List AntCheck.Event) (G : RaftFacts) (n : Fin R.N) (r₁ : RState)
      (xs : List XMsg) (rd : ReadyD),
      InMask msk R net xnet →
      SimPre R dec S V net xnet evs G → R.md.async = false →
      ReachIn msk R dec (admOf G) net xnet n (V n) r₁ xs → ReadyOutP R n (V n) r₁ xs rd →
      Reported (V n) rd → Told (V n) → ReadyFacts G (nodeId n) r₁ → TermRoom (V n) →
      SimStep R dec evs G
        (evReady (nodeId n) (V n).byE (roleStr rd.pre rd.role) rd.term rd.vote rd.commit rd.ents rd.snap)
        (setV V n ((V n).afterReady r₁ rd)) net xnet := by
  intro R dec S V net xnet evs G n r₁ xs rd hin hpre _ hr hro hrep htold hrf htb
  obtain ⟨S1, hx⟩ := rdCtx_of hmsk hin hpre hr hro hrep htold hrf htb
  obtain ⟨hR, hT, hVt, hC, -⟩ := hx.hro
  rw [hx.hpf, hx.hsn, hR, hT, hVt, hC]
  exact ready_nonleader hx
    (fun src rej mt hvc hsrc hq hlm hL hents hpc =>
      ready_win hx src rej mt hvc hsrc hq hlm hL hents hpc)
    (fun es hby hvl hne hents hplog hpl hpt hpv hpc =>
      ready_prop hx es hby hvl hne hents hplog hpl hpt hpv hpc)
    (fun hvl hpl hpt hpv hplog hents hlt hcm hns =>
      ready_cmt hx hvl hpl hpt hpv hplog hents hlt hcm hns)

end AntSim
end EtcdGrove
end Perennial
