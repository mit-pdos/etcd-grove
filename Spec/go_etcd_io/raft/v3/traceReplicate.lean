/-
Port of election_proof/spec_traceReplicate.v (feb5c73d4).
-/
module

public import Proof.go_etcd_io.raft.v3.TracedCap

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `traceReplicate(r, es...)`: one `Replicate` node event of `r`'s state per normal entry of the
batch (`traceNodeEvent(rsmReplicate, r)` in the loop), the entries read-only and given back.

One spec for both modes (Q8 stage 1, slice 2, 2026-11-09): untraced, the gate `trOwn` is `emp` and
`TraceFireN` the nil logger and `Q`; traced, raft's state is lent through the gate and the caller's
updates fire in a row, one per normal entry (`TraceFireN … (normalCount ents)`). Its traced instance
is the Draft's `traceReplicate.tracedSpec` (`TracedHooks.lean`). Until slice 2: `⌜TraceLoggerOk tl⌝`
(increment 1, `notes/trace-validation-hooks.md`). -/
abbrev traceReplicate.spec : Prop :=
  ∀ (c : CfgM) (r : Loc) (id : w64) (s : NState) (es : GoSlice) (dq : DFrac) (ents : List EntryM)
    (tl : GoInterface) (Q : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ entsPts es dq ents ∗
      r.[raft, go!"traceLogger"] ↦□ tl ∗ trOwn s.gh.tr (ownRaftPhysCV c c.voters r id s) ∗
      TraceFireN s.gh.tr tl (NodeEvOf (W64 5) id s c) (normalCount ents) Q }}
    (App (App (Val #(functions traceReplicate [])) (Val #r)) (Val #es))
  {{ RET #(); entsPts es dq ents ∗ trOwn s.gh.tr (ownRaftPhysCV c c.voters r id s) ∗ Q }}

end spec

end EtcdGrove
end Perennial
