/- Lean-first (no Rocq counterpart).

`w.advance(r)` (`examples/mvccrand/mvccrand.go`): the watcher's expected position moves past the
change at revision `r` it just received (`advW`): to the first change after it of revision
`r` when `r` is past its revision, else one change further in its revision.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccrand.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccrand

open Iris Iris.BI github_com.mit_pdos.etcd_grove.examples.mvccrand

/-- The watcher `wv` after `advance(r)`. -/
def advW [GooseExts] (wv : watcher) (r : w64) : watcher :=
  if sint.Z wv.rev' < sint.Z r then { wv with rev' := r, index' := W64 1 }
  else { wv with index' := wv.index' + W64 1 }

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccrand.Assumptions]

/-- See the file header. -/
abbrev watcher.advance.spec : Prop :=
  ∀ (w : Loc) (wv : watcher) (r : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.mvccrand ∗
      w ↦ wv }}
    (App (Val (w @!! go.GoType.PointerType watcher.ty @!! go!"advance")) (Val #r))
  {{ RET #(); w ↦ advW wv r }}

end spec

end mvccrand
end EtcdGrove
end Perennial
