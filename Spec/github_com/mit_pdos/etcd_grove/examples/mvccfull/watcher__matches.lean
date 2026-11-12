/- Lean-first (no Rocq counterpart).

`w.matches(ch)` (`examples/mvccfull/mvccfull.go`): whether the watcher expects the change `ch`
(`matchesM`): its key in the watcher's range, and the watcher's filter (`0` none, `1` no puts, `2`
no deletes) keeping its kind (`filtOk`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.inRange

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccfull

open Iris Iris.BI github_com.mit_pdos.etcd_grove.examples.mvccfull

section model
variable [GooseExts]

/-- **The filter `f` keeps a change of this kind** (`del`): `1` drops the puts, `2` the deletes. -/
def filtOk (f : w64) (del : Bool) : Bool := if del then decide (f ≠ W64 2) else decide (f ≠ W64 1)

/-- **A watcher of the range `[kk, e)` (`endNil`) and filter `f` expects the change `ch`.** -/
def matchesM (f : w64) (endNil : Bool) (kk e : GoString) (ch : change) : Bool :=
  inRangeM endNil kk e ch.key' && filtOk f ch.del'

end model

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccfull.Assumptions]

/-- See the file header. -/
abbrev watcher.matches.spec : Prop :=
  ∀ (w : Loc) (wv : watcher) (dq dk de : DFrac) (kk e : GoString) (ch : change),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.mvccfull ∗ w ↦{dq} wv ∗ wv.key' ↦*{dk} kk ∗ wv.end' ↦*{de} e }}
    (App (w @!! go.GoType.PointerType watcher.ty @!! go!"matches") (Val #ch))
  {{ RET #(matchesM wv.filter' (decide (wv.end' = slice.nil)) kk e ch);
      w ↦{dq} wv ∗ wv.key' ↦*{dk} kk ∗ wv.end' ↦*{de} e }}

end spec

end mvccfull
end EtcdGrove
end Perennial
