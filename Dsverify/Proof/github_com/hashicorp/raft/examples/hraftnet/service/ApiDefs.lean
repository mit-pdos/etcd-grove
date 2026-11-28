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

/-- The FSM's read side is persistent for the store's responses. -/
instance fsmAt_respP_persistent γ fc alb i s : Persistent (fsmAt (GF := GF) γ (respP γ fc alb) i s) := by
  unfold fsmAt; infer_instance

/-- **A barrier of term `T` completed at server `i`** (persistent; the lab's hr3 `barrierFact`): `i` led
`T`, and its FSM had processed an index `s` past `T`'s election part (`len0 T < s`: the barrier's), with
the store's responses (`respP γ fc alb`). -/
def barrierFact (γ : GNames) (i : SID) (fc : FCtx GF) (alb : GName) (T : Nat) : IProp GF :=
  iprop(∃ (n0 s : Nat), leaderIs γ T i ∗ len0Is γ T n0 ∗ ⌜n0 < s⌝ ∗ fsmAt γ (respP γ fc alb) i s)

instance barrierFact_persistent γ i fc alb T : Persistent (barrierFact (GF := GF) γ i fc alb T) := by
  unfold barrierFact fsmAt; infer_instance

/-- The API's mutex invariant: the term of a barrier the API saw complete (`0`: none), with its
`barrierFact` (S6: `Read`'s `WayVerify` skips the barrier in that term). -/
def apiMuInv (a : Loc) (γ : GNames) (i : SID) (fc : FCtx GF) (alb : GName) : IProp GF :=
  iprop(∃ t : w64, structFieldRef API go!"barrierIn" a ↦ t ∗
    (⌜t = W64 0⌝ ∨ barrierFact γ i fc alb (uint.nat t)))

/-- **Server `i`'s API `a`** (persistent): its raft (`isRaft`, whose responses are the store's:
`rc.respP = respP γ fc alb`), its store, the two timeouts, and its mutex. -/
def isAPI (a : Loc) (γ : GNames) (rc : RCtx GF) (i : SID) (fc : FCtx GF) (alb : GName) : IProp GF :=
  iprop(∃ (r fsm : Loc) (enq wt : time.Duration),
    structFieldRef API go!"r" a ↦□ r ∗ structFieldRef API go!"fsm" a ↦□ fsm ∗
    structFieldRef API go!"enqueue" a ↦□ enq ∗ structFieldRef API go!"wait" a ↦□ wt ∗
    isRaft r γ rc i ∗ ⌜rc.respP = respP γ fc alb⌝ ∗ isStore γ fc alb i fsm ∗
    sync.isMutex (structFieldRef API go!"mu" a) (apiMuInv a γ i fc alb))

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

/-- **A read's claim** (S6, the API's `Read` deposit; the clients prove it, `KitRead.lean`): for the store's
prefix `es` at the read (ending with a command, the frontier past it) and the read bound the server proved
(the store had applied `k0 ≤ |es|`, no command lies in `(k0, k]`, and the read's registration frontier,
of length `n0`, is within `k`), `Ψ` of `es`'s register (found, value). -/
def rdClaim (γ : GNames) (fc : FCtx GF) (n0 : Nat) (Ψ : Bool → List w8 → IProp GF) : IProp GF :=
  iprop(∀ (es : RLog) (k0 k : Nat), ⌜lastCmd es ∧ k0 ≤ es.length ∧ n0 ≤ k⌝ -∗
    noCmdBetween γ k0 (k + 1) -∗ frLb fc es -∗ £ 1 -∗ £ 1 ={⊤}=∗
      Ψ (regOf es).isSome ((regOf es).getD []))

end defs

end github_com.hashicorp.raft.examples.hraftnet.service
end Perennial
