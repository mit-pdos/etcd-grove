/-
`run(cfg, checks)` (`dsmain.go`): the gates set; the model server; its admin clientset; a
cancelable context (cancelled at the end, deferred); the node created by the admin (a panic on an
error); the informer factory over the non-admin clientset; the four typed informers; the
controller (`NewDaemonSetsController`, a panic on an error) over a new backoff; the factory
started; `go dsc.Run(ctx, 2)`; the DaemonSet created by the admin (a panic on an error);
`checks` checks a millisecond apart. Lean-first; track C of the DaemonSet run (`notes/k8s-daemonset-run/design.md`).

**The ghost state** `run`'s proof allocates (the run's design): `apiInv γa γ` right after
`NewServer` (the API state's clients' half and a mirror's half; `apiReader` follows, which the
factory takes); the node create through it with the mirror's other half; the controller (with the
pod family `podFamOk`); then `s1Inv γ c` from the mirror's half, the constructor's `dscFresh`,
`s1Ok_init` at the state after the node create; the DaemonSet create inside `s1Inv` (track B's
step lemma for an admin create of a `newDsOk` DaemonSet); each check over `s1Reader_of_inv`.
The informers' not-started tokens (decisions R6, R7) go to the constructor, which registers its
handlers pending; after `s1Inv`, its `dscActivate` gives them back whole for `factory.Start`.

**Scope** (decision R8): the model's ambiguous writes off. With them on, Go refutes the spec:
a create that commits and reports a timeout leads a later sync to create a second pod on the node
and the checker panics (`issues/k8s-daemonset-ambiguous-create-duplicate-pod.md`, 5 of 200 runs of
`TestAmbiguousWritesDetected`). `Main`'s call, at `serverConfig()` (`dsCfg`, the flag on), is the
one place the closed theorem's proof cannot pass (`Main.wp_proof`'s named `sorry`).

**Premises**: the thread bound under the reader pools' size (`threadBound ≤ 2^30 - 1`, the
constructor's and the informers' pools) and the receipt bound `NewServer` takes; the main thread's
token (the controller's `Run` goroutine is forked with the token the fork hands back); the right
to register the controller's metric (`prometheus.nameFree dsMetricName`, from program start).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.dsmain.Defs

@[expose] public section

set_option autoImplicit false

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace dsmain

open Iris Iris.BI apimodel dsctl informers

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.dsmain.Assumptions]

/-- **`run(cfg, checks)`**: returns (no panic). -/
abbrev run.spec : Prop :=
  ∀ (cfg : github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.Config) (nchk : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.dsmain ∗ threadTok ∗ ⌜threadBound GF ≤ 2 ^ 30 - 1⌝ ∗ ⌜receiptBound GF ≤ 2 ^ 63⌝ ∗
      ⌜cfg.AmbiguousWrites' = false⌝ ∗ prometheus.nameFree dsMetricName }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.dsmain.run)) (Val #cfg)) (Val #nchk))
  {{ (n : w64), RET #n; True }}

end spec

end dsmain
end EtcdGrove
end Perennial
