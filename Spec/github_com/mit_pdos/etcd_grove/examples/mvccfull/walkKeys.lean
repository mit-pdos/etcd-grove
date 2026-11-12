/- Lean-first (no Rocq counterpart).

`walkKeys(ks, p, depth)` (`examples/mvccfull/mvccfull.go`): appends to `ks` the strings over `a`,
`b`, `c` that extend `p` (`p` itself unless empty) up to length `depth`, in increasing order
(`walkM p (depth - len(p))`, `Base.lean`; `walkKeys(nil, "", d)` is `keysOf d`, sorted:
`keysOf_sorted`). For `len(p) ≤ depth` (else Go's recursion never ends); the slice is owned.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccfull.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccfull

open Iris Iris.BI github_com.mit_pdos.etcd_grove.examples.mvccfull

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccfull.Assumptions]

/-- See the file header. -/
abbrev walkKeys.spec : Prop :=
  ∀ (s : GoSlice) (ks0 : List GoString) (p : GoString) (depth : w64),
  (p.length : Int) ≤ sint.Z depth →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.mvccfull ∗ s ↦* ks0 ∗ ownSliceCap GoString s (DFrac.own 1) }}
    (App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.mvccfull.walkKeys)) (Val #s)) (Val #p)) (Val #depth))
  {{ (s' : GoSlice), RET #s'; s' ↦* (ks0 ++ walkM p (sint.nat depth - p.length)) ∗
      ownSliceCap GoString s' (DFrac.own 1) }}

end spec

end mvccfull
end EtcdGrove
end Perennial
