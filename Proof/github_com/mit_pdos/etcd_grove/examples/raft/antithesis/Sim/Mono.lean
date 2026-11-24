/-
Lean-first (no Rocq counterpart).

# The refinement to Antithesis's binding: `Reach` and `Quiet` are monotone in `net` (#33 S4)

The harness holds only a lower bound of the messages sent (`γ.sent`) when it takes a node's
steps: a step over the messages sent then is one over every later list of them.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Sim.Stmts

@[expose] public section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace AntSim

section mono
variable [GooseExts]

theorem Reach.mono {id : w64} {net net' : List Msg} (hn : net <+: net') {v : NodeView} {ps : PState}
    (h : Reach id net v ps) : Reach id net' v ps :=
  match h with
  | .stay _ hi => .stay _ hi
  | .input _ inp _ hi hb hc hm hs =>
    .input _ inp _ hi hb hc (fun m hmi => ⟨hn.subset (hm m hmi).1, (hm m hmi).2⟩) hs
  | .advance _ _ hp hc hb ha => .advance _ _ hp hc hb ha

theorem Quiet.mono {id : w64} {net net' : List Msg} (hn : net <+: net') {v v' : NodeView}
    (h : Quiet id net v v') : Quiet id net' v v' :=
  match h with
  | .input _ inp hi hm => .input _ inp hi (fun m hmi => ⟨hn.subset (hm m hmi).1, (hm m hmi).2⟩)
  | .noReady _ ps₁ hr h1 h2 h3 h4 h5 h6 => .noReady _ ps₁ (hr.mono hn) h1 h2 h3 h4 h5 h6
  | .silentReady _ ps₁ rd hr hro hnr => .silentReady _ ps₁ rd (hr.mono hn) hro hnr

end mono

end AntSim
end EtcdGrove
end Perennial
