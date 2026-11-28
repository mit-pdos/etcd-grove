/-
The vocabulary of the hraft kit's API service (`service.API`, notes/dsv-hraft.md, S5): a server's
API over its raft and its store (`isAPI`), and what `API.Apply` answers (`applyOut`).
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.service.FsmDefs
public import Dsverify.Proof.github_com.hashicorp.raft.core.Laws

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace github_com.hashicorp.raft.examples.hraftnet.service

open github_com.hashicorp.raft proto gprot

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.Assumptions]

/-- The API's mutex invariant: the term of a barrier the API saw complete (S6 adds its meaning). -/
def apiMuInv (a : Loc) : IProp GF :=
  iprop(∃ t : w64, structFieldRef API go!"barrierIn" a ↦ t)

/-- **Server `i`'s API `a`** (persistent): its raft (`isRaft`, whose responses are the store's:
`rc.respP = respP γ fc alb`), its store, the two timeouts, and its mutex. -/
def isAPI (a : Loc) (γ : GNames) (rc : RCtx GF) (i : SID) (fc : FCtx GF) (alb : GName) : IProp GF :=
  iprop(∃ (r fsm : Loc) (enq wt : time.Duration),
    structFieldRef API go!"r" a ↦□ r ∗ structFieldRef API go!"fsm" a ↦□ fsm ∗
    structFieldRef API go!"enqueue" a ↦□ enq ∗ structFieldRef API go!"wait" a ↦□ wt ∗
    isRaft r γ rc i ∗ ⌜rc.respP = respP γ fc alb⌝ ∗ isStore γ fc alb i fsm ∗
    sync.isMutex (structFieldRef API go!"mu" a) (apiMuInv a))

instance isAPI_persistent a γ rc i fc alb : Persistent (isAPI (GF := GF) a γ rc i fc alb) := by
  unfold isAPI; infer_instance

/-- **What `API.Apply` answered** for the command `d` (its token `opTok γ d n`): no effect (`2`), with
the token back; unknown (`3`); or done (`1`): the command is committed at some `k`, the frontier has
passed the committed prefix `es` that ends there, and `Found`/`V` are the FSM's answer to it. -/
def applyOut (γ : GNames) (fc : FCtx GF) (d : List w8) (n : Nat) (rep : ApplyReply) : IProp GF :=
  iprop((⌜rep.Status' = W64 2⌝ ∗ opTok γ d n) ∨ ⌜rep.Status' = W64 3⌝ ∨
    (⌜rep.Status' = W64 1⌝ ∗ ∃ (k : Nat) (e : Entry) (es : RLog), CIdx γ k e ∗
      ⌜e.kind = kCommand ∧ e.data = d ∧ es.length = k ∧ respAt es = result.mk rep.Found' rep.V'⌝ ∗
      cIdxs γ es ∗ frLb fc es))

end defs

end github_com.hashicorp.raft.examples.hraftnet.service
end Perennial
