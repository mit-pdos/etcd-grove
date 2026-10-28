/-
`(*Reflector).list(ctx)` (`reflector.go:674`): the reflector's (re)list: in a goroutine (with a
`recover` that forwards a panic), list through the pager at `relistResourceVersion()` (and once
more from `""` after an expired or too-large version); wait for it or for the context; then
replace the store with the list's items at the list's version (`syncWith`, the FIFO's `Replace`)
and record that version. Lean-first; phase 4 of `notes/k8s-daemonset-plan.md`, fifth round.

Stated for the reflector of an informer of the model API server's resource `res` (as `watch`):
from the reflector's state at its last version `n` (`none` before the first list), either
* the list succeeds: the list's objects, registered with the informer, are the table of a state at
  least every state the reflector knew, at that state's version, at least the reflector's last;
  its `Replace` is pushed through the informer invariant (`infInv_pushReplaceAU`) and the
  reflector's last version becomes the list's; or
* the list fails: an error, the reflector's state at `n` (only its "unavailable" flag may change);
  or
* the context is done first: `nil`, the context seen done (the listing goroutine keeps the
  reflector's fields; `watch` then returns at once).

Callees' named hypotheses: `meta.ListAccessor`, `meta.ExtractListWithAlloc`, `meta.LenList`,
`Trace.Step`, the `apierrors` predicates (boundary, pending approval),
`isTooLargeResourceVersionError` (not proved this round).
-/
module

public import Spec.k8s_io.client_go.tools.cache.Reflector__watch

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace cache

open Iris Iris.BI k8s_io.client_go.tools.cache apimodel informer

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.tools.cache.Assumptions]

/-- **`r.list(ctx)`**: see the file header. -/
abbrev Reflector.list.spec : Prop :=
  ∀ (r f : Loc) (lw : GoInterfaceOk) (et : reflect.Type') (dh : GoFunc) (ctx : GoInterfaceOk)
    (dch : GoChan) (γd : ChanNames) (γa : ApiNames)
    (cfg : github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.Config) (res : Res)
    (γf : FifoNames) (γt : TsNames) (γi : InfNames) (n : Option Nat),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.tools.cache ∗ reflFixed r f lw et dh ∗
      reflEnv γa cfg res γf γt γi f lw et ∗ stableCtx ctx dch γd ∗ reflSt r γa γi n }}
    (App (Val (r @!! go.GoType.PointerType Reflector.ty @!! go!"list")) (Val #(GoInterface.ok ctx)))
  {{ (err : GoInterface), RET #err;
      (⌜err = interface.nil⌝ ∗ ∃ k, reflSt r γa γi (some k)) ∨
      (⌜err ≠ interface.nil⌝ ∗ reflSt r γa γi n) ∨
      (⌜err = interface.nil⌝ ∗ ctxSeen dch γd) }}

end spec

end cache
end EtcdGrove
end Perennial
