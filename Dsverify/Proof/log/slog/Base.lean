/-
The package fact of `log.slog` (the model `models/log/slog`, translated with its bodies; the vr kit,
notes/dsv-vr.md): `DiscardHandler` holds `discardHandler{}` as a `Handler` (`dhV`), and
`defaultLogger` points, for good, to a `Logger` whose handler is `defaultHandler{}` (`defHV`). Both
are read-only after the initializer (the model has no `SetDefault`).
-/
module

public import Net.Proof.net.Base
public import Dsverify.GeneratedProof.log.slog
public import Perennial.Proof.context.Base
public import Perennial.Proof.errors.Base
public import Perennial.Proof.fmt.Base
public import Perennial.Proof.strconv.Base
public import Perennial.Proof.strings.Base

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI

namespace log.slog

section def_
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics] [package_sem : log.slog.Assumptions]

/-- `DiscardHandler`'s value: `discardHandler{}` as a `Handler`. -/
abbrev dhV : GoInterface := interface.mkOk discardHandler.ty #(zero_val discardHandler)

/-- The default logger's handler: `defaultHandler{}` as a `Handler`. -/
abbrev defHV : GoInterface := interface.mkOk defaultHandler.ty #(zero_val defaultHandler)

/-- The package fact: `DiscardHandler` holds `dhV`; `defaultLogger` points to a `Logger` whose
handler is `defHV` (persistent). -/
def pkgState : IProp GF :=
  iprop(globalAddr DiscardHandler ↦□ dhV ∗
    ∃ dl : Loc, globalAddr defaultLogger ↦□ dl ∗
      structFieldRef Logger go!"handler" dl ↦□ defHV)

instance pkgState_persistent : Persistent (pkgState (GF := GF)) := by
  unfold pkgState; infer_instance

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.log.slog :=
  define_is_pkg_init (pkgState (GF := GF))
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.log.slog :=
  build_get_is_pkg_init_wf

/-- The package fact, from `isPkgInit`. -/
theorem pkgState_of_init : isPkgInit (PROP := IProp GF) pkg_id.log.slog ⊢ pkgState (GF := GF) :=
  isPkgInit_access (PROP := IProp GF) pkg_id.log.slog

end def_

end log.slog
end Perennial
