-- The copy for the part `KvNet/` of `RaftNoAx/Proof/go_etcd_io/raft/v3/TraceNopLemmas.lean` (etc/copy-part.py; rerun it, do not edit).
/-
Lean-first (no Rocq counterpart). **The traced mode is empty in raft's build without `with_tla`**:
what the proofs of this tree's empty trace hooks (`state_trace_nop.go`) share.

In this build the logger's contract `isTraceLogger γt tl` is `tl = nil` (`InvTraceLogger.lean`), and
the traced half of the event builder's gate (`TraceFire (some γd) tl E Q`, `TracedCap.lean`) asks
for it of a non-nil logger: it is absurd. So whatever the mode the gate gives its `Q` without
logging anything (`traceFire_nop`, `traceFireOpt_nop`, `traceFireN_nop`), which is what an empty
hook returns.

Main tree only: imported by the hooks' proofs `trace<Hook>.lean` and by nothing else (the
`with_tla` tree `RaftTla/` has its own hook proofs and no module of this name).
-/
module

public import KvNet.Proof.go_etcd_io.raft.v3.TracedCap

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section nop
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **No traced gate in this build**: a traced node's gate holds the contract of a non-nil logger. -/
theorem traceFire_some_false (γd : GName) (tl : GoInterface) (E : TraceEv → Prop) (Q : IProp GF) :
    TraceFire (some γd) tl E Q ⊢ False := by
  dsimp only [TraceFire]
  iintro ⟨%tn, -, Hl, %Hnn, -⟩
  iapply isTraceLogger_ne_nil tn.tr tl Hnn $$ Hl

/-- ... nor one for an event that is logged ... -/
theorem traceFireOpt_some_false (γd : GName) (tl : GoInterface) (E : TraceEv → Prop) (Q : IProp GF) :
    TraceFireOpt (some γd) tl (some E) Q ⊢ False :=
  traceFire_some_false γd tl E Q

/-- ... nor one for a positive number of events. -/
theorem traceFireN_some_false (γd : GName) (tl : GoInterface) (E : TraceEv → Prop) (n : Nat)
    (Q : IProp GF) : TraceFireN (some γd) tl E (n + 1) Q ⊢ False :=
  traceFire_some_false γd tl E _

/-- **The gate gives `Q` with nothing logged**, whatever the mode: untraced it is `Q` with the nil
logger, traced it is absurd. -/
theorem traceFire_nop (tr : Option GName) (tl : GoInterface) (E : TraceEv → Prop) (Q : IProp GF) :
    TraceFire tr tl E Q ⊢ Q := by
  cases tr with
  | none => dsimp only [TraceFire]; iintro ⟨-, HQ⟩; iexact HQ
  | some γd => exact (traceFire_some_false γd tl E Q).trans false_elim

/-- ... and so does the gate for an event that may or may not be logged ... -/
theorem traceFireOpt_nop (tr : Option GName) (tl : GoInterface) (oE : Option (TraceEv → Prop))
    (Q : IProp GF) : TraceFireOpt tr tl oE Q ⊢ Q := by
  cases oE with
  | none => exact .rfl
  | some E => exact traceFire_nop tr tl E Q

/-- ... and the gate for `n` events. -/
theorem traceFireN_nop (tr : Option GName) (tl : GoInterface) (E : TraceEv → Prop) (Q : IProp GF) :
    ∀ n, TraceFireN tr tl E n Q ⊢ Q
  | 0 => traceFireOpt_nop tr tl none Q
  | n + 1 => (traceFire_nop tr tl E _).trans (traceFireN_nop tr tl E Q n)

end nop

end EtcdGrove
end Perennial
