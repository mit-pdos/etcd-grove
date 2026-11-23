/-
`EtcdGrove.initLb_of_spec` without its guard (`ExternalInit`), for the part `Dsverify/`'s generated
initializers (`etc/gen-init.py`, `dsv_inits`): an external package that `Net/`'s `ExternalInit` does
not list (`marshal`). The part imports `Net/`'s `PkgInitExt`, which declares `ExternalInit`, so it
cannot declare one of its own. Proved (the guard is unused in `initLb_of_spec`'s proof).
-/
module

public import Net.Proof.runtime.PkgInitExt

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Dsv

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section ax
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- An external initializer keeps the initialized packages (`EtcdGrove.initLb_of_spec`). -/
theorem initLb_of_spec (p : GoString) (init : val)
    [IsPkgInit (IProp GF) p] [GetIsPkgInitWf (IProp GF) p]
    (Hstd : ∀ (get_is_pkg_init : GoString → IProp GF),
      GetIsPkgInitProp p get_is_pkg_init →
      {{ ownInitializing get_is_pkg_init }} (App (Val init) (Val #()))
      {{ RET #(); ownInitializing get_is_pkg_init ∗ isPkgInit (PROP := IProp GF) p }}) :
    ∀ (get_is_pkg_init : GoString → IProp GF), GetIsPkgInitProp p get_is_pkg_init →
    ∀ σ0, {{ ownInitLb get_is_pkg_init σ0 }} (App (Val init) (Val #()))
      {{ RET #(); ownInitLb get_is_pkg_init σ0 ∗ isPkgInit (PROP := IProp GF) p }} :=
  fun g hg σ0 => initLb_of_initSpec init g _ (Hstd g hg) σ0

end ax

end Dsv
end EtcdGrove
end Perennial
