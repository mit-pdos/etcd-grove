/-
The node prophecy's resolution (notes/proph-swiftpaxos.md): an event's `Resolve` opens the node's
prophecy invariant (`client.nodeLockR`, Spec/client/Ghost.lean) around the single atomic
`ResolveProph`, and runs the caller's protocol update inside it (at `⊤ ∖ ↑client.nodeProphN`): the
prophecy loses the event's value, the node's half of its future words loses the event's words.

The lemma is proved first with the invariant at the weakest-precondition's own `invGS` (so `iinv`
finds the WP's invariant accessor), then restated with the invariant as the specs write it
(`GooseGlobalGS.gooseInvGS`, the same instance unfolded).
-/
module

public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.client.Ghost
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.client.LinHelp

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  netShaExts_has netShaExts_hasSha256

section wpinv
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics]

/-- The resolution under the invariant, the invariant at the WP's `invGS`. -/
theorem client.wp_resolveNode' (γ : sp.Names) (n : sp.PNode) (p : proph_id) (e : sp.PEv)
    (he : sp.PEvWf e) (Q : IProp netDistGF) (Φ : val → IProp netDistGF) :
    inv client.nodeProphN (client.nodeLockR γ n p) ∗
    (∀ W' : List w64, ghostMapElem γ.pred n (DFrac.own (1 : Qp).half) (sp.encP e ++ W')
        ={⊤ ∖ ↑client.nodeProphN}=∗ ghostMapElem γ.pred n (DFrac.own (1 : Qp).half) W' ∗ Q) ∗
    (Q -∗ Φ #()) ⊢
    WP (ResolveProph (Val #p) (Val (sp.encE e))) {{ Φ }} := by
  iintro ⟨#Hi, Hupd, HΦ⟩
  iinv Hi with HI
  iunfold client.nodeLockR at HI
  icases HI with ⟨%pvs, >Hpr, >Hw⟩
  wp_apply_core wp_resolve_proph p pvs (sp.encE e) (by simp [sp.encE]) $$ Hpr
  iintro %pvs' ⟨%Hpvs, Hpr⟩
  rw [Hpvs, sp.flatMap_valWs_cons he]
  imod Hupd $$ %_ Hw with ⟨Hw, HQ⟩
  imodintro
  isplitl [Hpr Hw]
  · inext
    iunfold client.nodeLockR
    iexists pvs'
    iframe
  iapply HΦ $$ HQ

end wpinv

section specinv
attribute [local instance] GooseGlobalGS.gooseInvGS
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics]

/-- **An event's resolution** (`ResolveProph p (sp.encE e)`, `p` the node's prophecy): opens the
node's prophecy invariant and runs the caller's update of the node's half of its future words
(at `⊤ ∖ ↑client.nodeProphN`), atomically with the resolution. -/
theorem client.wp_resolveNode (γ : sp.Names) (n : sp.PNode) (p : proph_id) (e : sp.PEv)
    (he : sp.PEvWf e) (Q : IProp netDistGF) (Φ : val → IProp netDistGF) :
    inv client.nodeProphN (client.nodeLockR γ n p) ∗
    (∀ W' : List w64, ghostMapElem γ.pred n (DFrac.own (1 : Qp).half) (sp.encP e ++ W')
        ={⊤ ∖ ↑client.nodeProphN}=∗ ghostMapElem γ.pred n (DFrac.own (1 : Qp).half) W' ∗ Q) ∗
    (Q -∗ Φ #()) ⊢
    WP (ResolveProph (Val #p) (Val (sp.encE e))) {{ Φ }} :=
  client.wp_resolveNode' γ n p e he Q Φ

end specinv

end Perennial.github_com.imdea_software.swiftpaxos

end
