/-
The statements of the names-only libraries' specs the swiftpaxos proof uses, copied from the lab
(dsverify-lab `harness/lean/Harness/Proof/{math/rand,os/signal}.lean`, `Harness/Proof/uuid/Specs.lean`),
where the lab proved them from its own models. Here `math/rand` (Perennial's translation), `os/signal`
and `github.com/google/uuid` (configured names only, `Dsverify/Code/**.toml`) have no bodies, so each
is a field of `SwiftHyps` (Hyps.lean; notes/dsv-swiftpaxos.md, "Hypotheses").

**Port changes.**
* `uuid.New`/`UUID.ID`: the lab's results were functions of the UUID's bytes (`isV4`, `idOf`, proved from
  its model of `uuid`'s code); the proof uses neither, so here `New` returns some `UUID` and `ID` some `w32`.
* `os.signal.Notify`: the lab's model never delivers a signal (its `Notify` keeps no reference to the
  channel), and `hook.HookUser1`'s proof relies on it (the channel's bag holds no message). Here that
  is `os.signal.NotifyQuiet.spec`, **an assumption of the deployment** (no `SIGUSR1` is sent to a
  node), not a fact of Go's `os/signal`: the separate class `SwiftNoSignals` (Hyps.lean), over the
  one signal `HookUser1` passes.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Base

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section specs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [github_com.imdea_software.swiftpaxos.SwiftNetPkgState GF]

/-- lab `Harness/Proof/math/rand.lean` `math.rand.NewSource.spec`. -/
abbrev math.rand.NewSource.spec : Prop :=
  ∀ (seed : w64),
    {{ isPkgInit (PROP := IProp GF) pkg_id.math.rand }}
      (App (Val (@! math.rand.NewSource)) (Val #seed))
    {{ (src : GoInterface), RET #src; True }}

/-- lab `math.rand.New.spec`. -/
abbrev math.rand.New.spec [math.rand.Assumptions] : Prop :=
  ∀ (src : GoInterface),
    {{ isPkgInit (PROP := IProp GF) pkg_id.math.rand }}
      (App (Val (@! math.rand.New)) (Val #src))
    {{ (r : Loc), RET #r; ∃ v : math.rand.Rand, r ↦ v }}

/-- lab `math.rand.Intn.spec` (the package-level `Intn`). -/
abbrev math.rand.Intn.spec : Prop :=
  ∀ (n : w64), 0 < sint.Z n →
    {{ isPkgInit (PROP := IProp GF) pkg_id.math.rand }}
      (App (Val (@! math.rand.Intn)) (Val #n))
    {{ (x : w64), RET #x; ⌜0 ≤ sint.Z x ∧ sint.Z x < sint.Z n⌝ }}

/-- `signal.Notify(c, SIGUSR1)` (the fork's `hook.HookUser1`; `SIGUSR1` is the literal
`syscall.Signal(0xa)`) in a deployment where no signal is sent: nothing. **Not a library spec**: real
Go's `Notify` registers `c`, and the runtime sends every `SIGUSR1` the process receives on it. It is
the environment assumption `SwiftNoSignals` (Hyps.lean), as dsv-rabia's `os.signal.NoSignals`
(`NotifyQuiet.spec`), restricted (Upamanyu's rabia review, #24) to the signals actually passed. -/
abbrev os.signal.NotifyQuiet.spec : Prop :=
  ∀ (c : GoChan) (sig : GoSlice) (dq : DFrac), c ≠ chan.nil →
    {{ isPkgInit (PROP := IProp GF) pkg_id.os.signal ∗
        sig ↦*{dq} [interface.mkOk syscall.Signal.ty #(W64 10)] }}
      (App (App (Val (@! os.signal.Notify)) (Val #c)) (Val #sig))
    {{ RET #(); sig ↦*{dq} [interface.mkOk syscall.Signal.ty #(W64 10)] }}

/-- lab `Harness/Proof/uuid/Specs.lean` `uuid.wp_New` (see the file header). -/
abbrev github_com.google.uuid.New.spec : Prop :=
    {{ (True : IProp GF) }}
      (App (Val (@! github_com.google.uuid.New)) (Val #()))
    {{ (u : github_com.google.uuid.UUID), RET #u; True }}

/-- lab `uuid.wp_ID` (see the file header). -/
abbrev github_com.google.uuid.UUID.ID.spec [github_com.google.uuid.Assumptions] : Prop :=
  ∀ (u : github_com.google.uuid.UUID),
    {{ (True : IProp GF) }}
      (App (Val (u @!! github_com.google.uuid.UUID.ty @!! go!"ID")) (Val #()))
    {{ (x : w32), RET #x; True }}

end specs

end Perennial
