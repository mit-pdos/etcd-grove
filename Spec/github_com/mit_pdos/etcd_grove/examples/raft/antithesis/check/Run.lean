/-
Lean-first (no Rocq counterpart). #33 S3b (2026-11-23), `notes/antithesis-check-design.md` §10.

`Run(cfg, evs)` (`examples/raft/antithesis/check/check.go`): the check of a stream of rawnode
reports against `EtcdBinding.tla`, as TLC with TraceKit's `StreamEvent` checks it. Its spec: it
returns the verdict the Lean transcription's `run` (`Tla/Check.lean`) gives the stream, so
`ACCEPTED` exactly when `Accepts cfg evs`, and `REJECTED k` / `VIOLATED k names` otherwise.

The premise (`Run`'s, which `Main`'s proof discharges from the harness's stream, S4):
- `run cfg evs = .ok v`: no evaluation error. Where TLC would stop with one, the Go panics (an
  `EvalError`), which a triple's postcondition does not describe; `Main` needs `ACCEPTED`, which
  includes it (`Accepts`), so the harness's proof gives it with acceptance;
- `Stream.Bounded evs`, `Config.Bounded cfg`: the stream's numbers and size, and the
  configuration's sets, far from the Go `int`'s overflow (`Rep.lean`).
The configuration and the stream are read, not written (`configRO`, `eventsRO`, persistent).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Rep

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace AntCheck

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Assumptions]

/-- See the file header. -/
abbrev Run.spec : Prop :=
  ∀ (cp : Loc) (cfg : Config) (sl : GoSlice) (evs : List Event) (v : Verdict),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check ∗
      configRO cp cfg ∗ eventsRO sl evs ∗
      ⌜Config.Bounded cfg ∧ Stream.Bounded evs ∧ run cfg evs = .ok v⌝ }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Run))
      (Val #cp)) (Val #sl))
  {{ (r : G.Verdict), RET #r; verdictRO r v }}

end spec

end AntCheck
end EtcdGrove
end Perennial
