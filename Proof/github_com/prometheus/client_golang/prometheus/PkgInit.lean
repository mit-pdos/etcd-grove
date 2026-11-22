/-
The package-initialization instance of prometheus. One home, shared by the server's `Base.lean` files and the
WAL (until 2026-11-15 declared in the backend's `Base.lean` and the WAL's `DepsPkgInit.lean`;
notes/wal-lean-integration.md).

(prom-registry, route (b), Option 4, 2026-11-22: notes/prom-registry.md) Its fact is the default registry
(`promInit γ`), at the run's registry ghost name `γ`, which the program's proof chooses: the package's fact
is parameterized (`IsPkgInitParam`, Perennial's `Pkg.lean`) by `EtcdGrove.prometheus.PromRegGS GF`. An
importer's fact holds `isPkgInitSome` of it (no parameter); code proved at a known name uses the local
instance `isPkgInit_inst` (`[PromRegGS GF]`); the well-formedness instance takes the parameter, and so do
those of every importer (`[EtcdGrove.prometheus.PromRegGS GF]` binders): it fixes the name the
initializer establishes. Until then the fact was `True`.
-/
module

public import GeneratedProof.github_com.prometheus.client_golang.prometheus
public import Proof.github_com.prometheus.client_model.go.PkgInit
public import Proof.github_com.prometheus.client_golang.prometheus.RegInv
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

/-- **prometheus's fact at the registry ghost name `γ`**: the default registry `r` (the variable
`defaultRegistry`, and `DefaultRegisterer`, the same `*Registry` as a `Registerer`; both read-only after
the initializer) is a registry (`isRegistry γ r`: its maps under its lock, the registered keys' rights
owned by its invariant). -/
def promInit (γ : GName) : IProp GF :=
  iprop(∃ r : Loc, globalAddr defaultRegistry ↦□ r ∗
    globalAddr DefaultRegisterer ↦□ (interface.mkOk (go.GoType.PointerType Registry.ty) #r) ∗
    EtcdGrove.prometheus.isRegistry γ r)

instance promInit_persistent (γ : GName) : Persistent (promInit (GF := GF) γ) := by
  unfold promInit; infer_instance

/-- The package's fact at each registry ghost name. -/
instance isPkgInitParam_inst :
    IsPkgInitParam (IProp GF) pkg_id.github_com.prometheus.client_golang.prometheus where
  Param := EtcdGrove.prometheus.PromRegGS GF
  inst x := define_is_pkg_init (promInit x.γ)

/-- The package's fact at the name in scope (code proved at a known name: the registering
initializers, `MustRegister`'s and `Register`'s proofs). -/
instance isPkgInit_inst [x : EtcdGrove.prometheus.PromRegGS GF] :
    IsPkgInit (IProp GF) pkg_id.github_com.prometheus.client_golang.prometheus :=
  IsPkgInitParam.inst (PROP := IProp GF) (pkg_name := pkg_id.github_com.prometheus.client_golang.prometheus) x

instance get_isPkgInit_wf_inst [EtcdGrove.prometheus.PromRegGS GF] :
    GetIsPkgInitWf (IProp GF) pkg_id.github_com.prometheus.client_golang.prometheus :=
  build_get_is_pkg_init_wf

/-- The fact's user part at the name in scope. -/
theorem promInit_of_isPkgInit [EtcdGrove.prometheus.PromRegGS GF] :
    isPkgInit (PROP := IProp GF) pkg_id.github_com.prometheus.client_golang.prometheus ⊢
      promInit (EtcdGrove.prometheus.PromRegGS.γ (GF := GF)) :=
  isPkgInit_access _

end github_com.prometheus.client_golang.prometheus

end init

end Perennial
