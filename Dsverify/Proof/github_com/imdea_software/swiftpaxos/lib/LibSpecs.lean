/-
The statements of the names-only libraries' specs the swiftpaxos proof uses, copied from the lab
(dsverify-lab `harness/lean/Harness/Proof/{math/rand,os/signal}.lean`, `Harness/Proof/uuid/Specs.lean`),
where the lab proved them from its own models. Here `math/rand` (Perennial's translation), `os/signal`
and `github.com/google/uuid` (configured names only, `Dsverify/Code/**.toml`) have no bodies, so each
is a hypothesis (Hyps.lean; notes/dsv-swiftpaxos.md, "Hypotheses"). `math/rand`'s specs are
dsv-rabia's (`Dsverify/Proof/math/rand/Spec.lean`, the class `math.rand.Hyps`).

**Port changes.**
* `uuid.New`/`UUID.ID`: the lab's results were functions of the UUID's bytes (`isV4`, `idOf`, proved from
  its model of `uuid`'s code); the proof uses neither, so here `New` returns some `UUID` and `ID` some `w32`.
* `os.signal.Notify`: the lab's model never delivers a signal (its `Notify` keeps no reference to the
  channel), and `hook.HookUser1`'s proof relies on it (the channel's bag holds no message). Here that
  is dsv-rabia's `os.signal.NotifyQuiet.spec usr1Sigs`, **an assumption of the deployment** (no
  `SIGUSR1` is sent to a node), not a fact of Go's `os/signal`: the environment class
  `os.signal.NoSignals usr1Sigs`, over the one signal `HookUser1` passes.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Base
public import Dsverify.Proof.math.rand.Spec
public import Dsverify.Proof.os.signal.Spec

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

/-- The signals `hook.HookUser1` registers (`signal.Notify(c, SIGUSR1)`; the fork writes `SIGUSR1`
as the literal `syscall.Signal(0xa)`), as the `os.Signal` values of its slice literal. The
environment assumption over them is dsv-rabia's `os.signal.NoSignals usr1Sigs`
(Dsverify/Proof/os/signal/Spec.lean): no `SIGUSR1` is sent to a node. **Not a library spec**:
real Go's `Notify` registers `c`, and the runtime sends every `SIGUSR1` the process receives on
it. -/
abbrev github_com.imdea_software.swiftpaxos.usr1Sigs : List os.Signal := os.signal.usr1Sigs

/-- lab `Harness/Proof/uuid/Specs.lean` `uuid.wp_New` (see the file header): `New()` returns some
`UUID`. Go's `New` is `Must(NewRandom())`: it reads 16 bytes from `crypto/rand.Reader` (the OS's
randomness) and panics if that read fails. That it does not fail is **an assumption of the
environment**, not a fact of the library: so this is the separate class `SwiftOsRandom`
(Hyps.lean), not a `SwiftHyps` field. -/
abbrev github_com.google.uuid.New.spec : Prop :=
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.google.uuid }}
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
