/- Port of election_proof/spec_traceConfChangeEvent.v (feb5c73d4). -/
module

public import Proof.go_etcd_io.raft.v3.RaftReadLend

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

/-- `traceConfChangeEvent(cfg, r)`: reads `r.traceLogger` and returns when it is nil; otherwise reports
`ApplyConfChange`: an event of raft's state at its old configuration `c` (`traceEvent`), with the new
configuration `cn`'s incoming voters (`cfg.Voters[0].Slice()`, formatted, as the properties' `cc`).

One spec for both modes (2026-11-12, trace-check step 4; `notes/trace-check-design.md` §3.4), by the
caller's mode `tr`, in `traceEvent.spec`'s form: the logger's gate `TraceFire tr tl E Q` (untraced: a nil
logger and `Q`; traced: every `CCEvOf id s c cn` event allowed by `E`), and under the gate `trOwn tr`
what only the traced branch reads: raft's state lent read-only out
of a resource `P` (`RaftReadLend`: the header's fields, the log, the `trk` field and its configuration's
maps), so that `switchToConfig`, whose struct is open at its tracker at the call, can lend it, and the
new configuration (`ownConfigC`, read), both given back (as `R`). (Until 2026-11-12 the untraced statement,
`⌜TraceLoggerOk tl⌝` giving `True`, and the frozen Draft's `traceConfChangeEvent.tracedSpec`, raft's
state closed, beside it: the latter is now this spec's instance, `TracedConfChangeHook.lean`.) -/
abbrev traceConfChangeEvent.spec : Prop :=
  ∀ (cfgv : tracker.Config) (r : Loc) (tl : GoInterface) (tr : Option GName) (E : TraceEv → Prop)
    (Q R : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ r.[raft, go!"traceLogger"] ↦□ tl ∗
      trOwn tr iprop(∃ (c cn : CfgM) (id : w64) (s : NState) (prsm : Loc) (prs : GMap w64 Loc)
          (pvs : GMap w64 Progress) (P : IProp GF),
        P ∗ RaftReadLend P c r id s ∗ ownConfigC cn cfgv prsm prs pvs ∗
        ⌜∀ e, CCEvOf id s c cn e → E e⌝ ∗ (P ∗ ownConfigC cn cfgv prsm prs pvs -∗ R)) ∗
      TraceFire tr tl E Q }}
    (App (App (Val #(functions traceConfChangeEvent [])) (Val #cfgv)) (Val #r))
  {{ RET #(); trOwn tr R ∗ Q }}

end spec

end EtcdGrove
end Perennial
