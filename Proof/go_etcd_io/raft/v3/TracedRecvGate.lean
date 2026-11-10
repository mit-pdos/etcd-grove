/-
Lean-first (no Rocq counterpart). **The receive line's gate, either mode** (2026-11-10, trace-check Q8
stage 1 slice 13, `notes/decisions.md`, "Q8 stage 1 (slice 13)"): `raft.Step`'s first gate
(`stepGates`' `"Hgrecv"`, the receive hook's `HookGateOpt s.gh.tr r (recvGate …) _`) from the
capability, as `trCapB_hookGate` gives a node event's (`TracedHooksGlobal.lean`): traced, by the law of
a receive line (`trCap_fire_recv`), from the line's phase step `PhaseStepR`, its facts `FxPresR` and the
received message's token; untraced, from the struct's nil logger.
-/
module

public import Proof.go_etcd_io.raft.v3.TracedHooksGlobal
public import Proof.go_etcd_io.raft.v3.TracedMsg

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3 TraceSim

section gate
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- **The received message's token, by the cluster's trace mode**: nothing untraced; traced, the token
`k` of the specification's message `m` in flight (`inFlight`, which the receive line consumes). -/
def recvTok (tr : Option GName) (k : Nat) (m : Etcdraft.Msg) : IProp GF :=
  match tr with
  | none => iprop(emp)
  | some γd => iprop(∃ tn, traceDir γd tn ∗ inFlight tn k m)

/-- **A receive line's facts, by the cluster's trace mode** (`FxPresR` traced, nothing untraced). -/
def FxPresRT (tr : Option GName) (γ : RaftNames) (id : w64) (m : Etcdraft.Msg) (E : TraceEv → Prop)
    (Mid : Etcdraft.Server → Prop) (Φ Φ' : List w64 → ServerC → List Etcdraft.Msg → Prop) : IProp GF :=
  match tr with
  | none => iprop(True)
  | some _ => FxPresR γ id m E Mid Φ Φ'

/-- **A receive line's gate, either mode**: the logger `tl0` (nil when untraced), the capability in
phase `Φ`, the line's facts and the received message's token give the receive hook's gate, whose update
gives the capability in phase `Φ'` (its `booted` flag set): traced by `trCap_fire_recv`, untraced from
the nil logger. -/
theorem trCapB_hookGateRecv (tr : Option GName) (γ : RaftNames) (r : Loc) (id : w64) (c : CfgM)
    (tl0 : GoInterface) (E : TraceEv → Prop) (b : Bool) (k : Nat) (m : Etcdraft.Msg)
    (Mid : Etcdraft.Server → Prop) (Φ Φ' : List w64 → ServerC → List Etcdraft.Msg → Prop)
    (Λ Λ' : Option TraceEv → Prop)
    (hps : PhaseStepR id c m E Mid Φ Φ') (hΛ : ∀ e, E e → Λ' (some e))
    (hOk : tr.isSome → ∀ e, E e → TraceEv.Ok (elements c.incoming).length e)
    (hok : tr = none → TraceLoggerOk tl0) :
    (r.[raft, go!"traceLogger"] ↦□ tl0 ∗ trCapB tr γ r id c b Φ Λ ∗ FxPresRT tr γ id m E Mid Φ Φ' ∗
        recvTok tr k m : IProp GF) ⊢
      HookGateOpt tr r (some E) (trCapB tr γ r id c true Φ' Λ') := by
  cases tr with
  | none =>
    simp only [trCapB]
    iintro ⟨#Hl, -, -, -⟩
    iapply hookGateOpt_none r (some E) tl0 iprop(emp) (hok rfl)
    iframe Hl
  | some γd =>
    simp only [FxPresRT, recvTok]
    iintro ⟨-, Hcap, Hfx, Htok⟩
    icases trCapB_logger γd γ r id c b Φ Λ $$ Hcap with ⟨%tl, #Htl, Hcap⟩
    iunfold HookGateOpt
    imodintro
    iexists tl
    isplitr
    · iexact Htl
    isplitr
    · ipureintro; intro h; cases h
    simp only [TraceFireOpt]
    iapply trCap_fire_recv γd γ r id c tl E k m Mid Φ Φ' Λ Λ' hps hΛ (hOk rfl)
    iframe Htl Hfx Htok
    iapply trCapB_trCap
    iexact Hcap

end gate

end EtcdGrove
end Perennial
