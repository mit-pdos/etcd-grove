/-
The package-initialization instance of prometheus. One home, shared by the server's `Base.lean` files and
the WAL (until 2026-11-15 declared in the backend's `Base.lean` and the WAL's `DepsPkgInit.lean`;
notes/wal-lean-integration.md).

(prom-registry, 2026-11-22, notes/prom-registry.md) Its fact: the variable `defaultRegistry` holds the
default registry, the model's (`promreg`, run by the trusted glue `TrustedCode/.../prometheus.lean`),
naming IDs by `descId`. Hand-written, not `define_is_pkg_init`: the glue's `defaultRegistry.init`
initializes the model's package, which the translation's `pkgImportedPkgs` (`[time]`) does not list, so
its dependencies are `time` and `promreg` (`etc/gen-init.py`'s `EXTRA_DEPS`, which the generated package
tables follow). Until then its fact was `True` (names only).
-/
module

public import GeneratedProof.github_com.prometheus.client_golang.prometheus
public import Proof.github_com.prometheus.client_golang.prometheus.Registry
public import Perennial.Proof.ProofPrelude
public import Perennial.Proof.io
public import Perennial.Proof.fmt
public import Perennial.Proof.time
public import Perennial.Proof.sync
public import Perennial.Proof.strings
public import Perennial.Proof.errors
public import Perennial.Proof.sort
public import Perennial.Proof.context
public import Perennial.Proof.bytes

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.iris.dupNamespace false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section init
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

namespace github_com.prometheus.client_golang.prometheus

/-- prometheus's fact: `defaultRegistry` holds the model's registry, naming IDs by `descId`. -/
def promInit : IProp GF :=
  iprop(∃ l : Loc, globalAddr defaultRegistry ↦□ l ∗ EtcdGrove.promreg.isRegistry EtcdGrove.prometheus.descId l)

instance promInit_persistent : Persistent (promInit (GF := GF)) := by
  unfold promInit; infer_instance

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.github_com.prometheus.client_golang.prometheus where
  isPkgInitDeps := iprop(isPkgInit (PROP := IProp GF) pkg_id.time ∗
    isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.promreg ∗ True)
  isPkgInitDef := promInit
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.github_com.prometheus.client_golang.prometheus where
  get_is_pkg_init_prop_def g :=
    g pkg_id.github_com.prometheus.client_golang.prometheus =
        isPkgInit (PROP := IProp GF) pkg_id.github_com.prometheus.client_golang.prometheus ∧
      GetIsPkgInitProp pkg_id.time g ∧
      GetIsPkgInitProp pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.promreg g ∧ True

end github_com.prometheus.client_golang.prometheus

end init

end Perennial
