/-
Lean-first (no Rocq counterpart).

# The refinement to Antithesis's binding: `Reach` and `Quiet` are monotone in `net` and `xnet` (#33 S4)

The harness holds only a lower bound of the messages sent (`γ.sent`, and of the transfer messages)
when it takes a node's steps: a step over the messages sent then is one over every later list of them
(`Reach`, `Quiet`, and their masked forms `ReachIn`, `QuietIn`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Sim.Scope

@[expose] public section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace AntSim

section mono
variable [GooseExts]
variable {R : RunCfg} {dec : CCDec} {Adm : List EntryM → CCState → Prop} {n : Fin R.N}
  {net net' : List Msg} {xnet xnet' : List XMsg}

theorem Reach.mono (hn : net <+: net') (hx : xnet <+: xnet') {v : NodeView} {r₁ : RState}
    {xs : List XMsg} (h : Reach R dec Adm net xnet n v r₁ xs) : Reach R dec Adm net' xnet' n v r₁ xs :=
  match h with
  | .stay _ hi => .stay _ hi
  | .input _ inp _ _ hi hb hc hxc hm hxm hs =>
    .input _ inp _ _ hi hb hc hxc (fun m hmi => ⟨hn.subset (hm m hmi).1, (hm m hmi).2⟩)
      (fun x hxi => ⟨hx.subset (hxm x hxi).1, (hxm x hxi).2⟩) hs
  | .advance _ _ hp hxp hce hrp hb ha hns => .advance _ _ hp hxp hce hrp hb ha hns

theorem Quiet.mono (hn : net <+: net') (hx : xnet <+: xnet') {v v' : NodeView}
    (h : Quiet R dec Adm net xnet n v v') : Quiet R dec Adm net' xnet' n v v' :=
  match h with
  | .input _ inp hi hm hxm =>
    .input _ inp hi (fun m hmi => ⟨hn.subset (hm m hmi).1, (hm m hmi).2⟩)
      (fun x hxi => ⟨hx.subset (hxm x hxi).1, (hxm x hxi).2⟩)
  | .noReady _ r₁ hr h1 h2 h3 h4 h5 h6 h7 => .noReady _ r₁ (hr.mono hn hx) h1 h2 h3 h4 h5 h6 h7
  | .silentReady _ r₁ xs rd hr hro hnr => .silentReady _ r₁ xs rd (hr.mono hn hx) hro hnr

theorem ReachIn.mono {msk : SimMask} (hn : net <+: net') (hx : xnet <+: xnet') {v : NodeView}
    {r₁ : RState} {xs : List XMsg} (h : ReachIn msk R dec Adm net xnet n v r₁ xs) :
    ReachIn msk R dec Adm net' xnet' n v r₁ xs :=
  match h with
  | .stay _ hi => .stay _ hi
  | .input _ inp _ _ hk hi hb hc hxc hm hxm hs =>
    .input _ inp _ _ hk hi hb hc hxc (fun m hmi => ⟨hn.subset (hm m hmi).1, (hm m hmi).2⟩)
      (fun x hxi => ⟨hx.subset (hxm x hxi).1, (hxm x hxi).2⟩) hs
  | .advance _ _ hp hxp hce hrp hb ha hns => .advance _ _ hp hxp hce hrp hb ha hns

theorem QuietIn.mono {msk : SimMask} (hn : net <+: net') (hx : xnet <+: xnet') {v v' : NodeView}
    (h : QuietIn msk R dec Adm net xnet n v v') : QuietIn msk R dec Adm net' xnet' n v v' :=
  match h with
  | .input _ inp hk hi hm hxm =>
    .input _ inp hk hi (fun m hmi => ⟨hn.subset (hm m hmi).1, (hm m hmi).2⟩)
      (fun x hxi => ⟨hx.subset (hxm x hxi).1, (hxm x hxi).2⟩)
  | .noReady _ r₁ hr h1 h2 h3 h4 h5 h6 h7 => .noReady _ r₁ (hr.mono hn hx) h1 h2 h3 h4 h5 h6 h7
  | .silentReady _ r₁ xs rd hr hro hnr => .silentReady _ r₁ xs rd (hr.mono hn hx) hro hnr

end mono

end AntSim
end EtcdGrove
end Perennial
