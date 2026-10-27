/-
`v3compactor.New` (`compactor.go`). Lean-first (no Rocq counterpart); the spec-first pilot
(`notes/compactor-pilot-plan.md`, phase 1: the specs, written before the proofs).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver.api v3compactor

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- `New(lg, mode, retention, rg, c)`: for mode `"periodic"` (a retention of at least `10ns`: the
pilot's configuration, `notes/compactor-pilot-plan.md`, phase 0; the code runs with
`|retention| ≥ 10ns`, `issues/etcd-compactor-periodic-tiny-retention.md`, but a negative period
busy-loops with an effective retention of zero, the misconfiguration that issue's etcd-io/etcd#22396
rejects) or `"revision"`, a compactor (`compactorOk`)
with its run token, whose `Run` takes the environment's contracts (`modeRunPre`: the caller's
`compactableOk` is at C1's permit, `modePermit`) and calls `Compact` only at revisions C1 allows;
for another mode, an error. A nil `lg` is replaced by
`zap.NewNop()`. (Until 2026-10-27 an axiom whose post was `True`.) -/
abbrev v3compactor.New.spec : Prop :=
  ∀ (lg : Loc) (mode : GoString) (ret : time.Duration) (E : CompactEnv GF),
  (mode = go!"periodic" → 10 ≤ sint.Z ret) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor }}
    (App (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor.New)) (Val #lg)) (Val #mode)) (Val #ret)) (Val #E.rg)) (Val #E.c))
  {{ (cp err : GoInterface), RET (PairV #cp #err);
      (⌜err = GoInterface.nil⌝ ∗ ∃ RunTok : IProp GF,
        compactorOk cp RunTok (modeRunPre mode E (sint.Z ret)) ∗ RunTok) ∨
      ⌜err ≠ GoInterface.nil ∧ mode ≠ go!"periodic" ∧ mode ≠ go!"revision"⌝ }}

end spec

end EtcdGrove
end Perennial
