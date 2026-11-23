/-
The package fact of `log.slog` (the model `models/log/slog`, translated with its bodies; the vr kit,
notes/dsv-vr.md): `DiscardHandler` holds `discardHandler{}` as a `Handler` (`dhV`), and
`defaultLogger` points, for good, to a `Logger` whose handler is `defaultHandler{}` (`defHV`). Both
are read-only after the initializer (the model has no `SetDefault`).
-/
module

public import Net.Proof.net.Base
public import Dsverify.GeneratedProof.log.slog

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI

namespace log.slog

section def_
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics] [package_sem : log.slog.Assumptions]

/-- `DiscardHandler`'s value: `discardHandler{}` as a `Handler`. -/
abbrev dhV : GoInterface := interface.mkOk discardHandler.ty #(discardHandler.mk)

/-- The default logger's handler: `defaultHandler{}` as a `Handler`. -/
abbrev defHV : GoInterface := interface.mkOk defaultHandler.ty #(defaultHandler.mk)

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

end def_

end log.slog
end Perennial
