/-
Lean-first (no Rocq counterpart).

# The refinement to Antithesis's binding: `antSim_ready` (#33 S4, the invariant phase)

`ready_nonleader` (every kind but a leader's) with its leader premises discharged: a win
(`ready_win`), a proposal (`ready_prop`), a commit (`ready_cmt`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Sim.ReadyWin
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Sim.Stmts

@[expose] public section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace AntSim

/-- **`antSim_ready`**: a reported `Ready` is a step of the binding, keeping the relation. -/
theorem antSim_ready [GooseExts] : antSim_ready.stmt := by
  intro S V net evs G n ps₁ rd hp hs hl hgo hr hro hrep htold hrf htb
  exact ready_nonleader S V net evs G n ps₁ rd hp hs hl hgo hr hro hrep htold hrf htb
    (fun src rej mt hvc hsrc hq hlm hL hents =>
      ready_win S V net evs G n ps₁ rd hp hs hl hgo hr hro hrep hrf src rej mt hvc hsrc hq hlm hL hents)
    (fun es hby hvl hne hents hplog hpl hpt hpv hpc =>
      ready_prop S V net evs G n ps₁ rd hp hs hl hgo hr hro hrf es hby hvl hne hents hplog hpl hpt hpv hpc)
    (fun hvl hpl hpt hpv hplog hents hlt hcm hns =>
      ready_cmt S V net evs G n ps₁ rd hp hs hl hgo hr hro hrep hrf hvl hpl hpt hpv hplog hents hlt hcm hns)

end AntSim
end EtcdGrove
end Perennial
