/- Lean-first (no Rocq counterpart).

`inBounds(lo, v, hi, what)` (`examples/mvccfull/mvccfull.go`): returns when `lo ≤ v` and the
value `hi.Load()` reads is at least `v`. The load is the caller's atomic step: the caller gives the
atomic int's points-to at the load's instant (at any fraction, from its invariant), with the
promise that its value is at least `v` (a member's `revHi` is at least the store's revision,
which never decreases: `notes/mvccfull-proof-plan.md`, M), and gets `Φ` back, as
`sync.atomic.Int64.Load`'s spec.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccfull.Base
public import Perennial.Proof.sync.atomic.Base

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
abbrev inBounds.spec : Prop :=
  ∀ (lo v : w64) (hi : Loc) (what : GoString), sint.Z lo ≤ sint.Z v →
  ⊢ ∀ Φ : val → IProp GF, isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.mvccfull -∗
    (|={⊤,∅}=> ▷ ∃ (dq : DFrac) (x : w64), sync.atomic.ownInt64 hi dq x ∗ ⌜sint.Z v ≤ sint.Z x⌝ ∗
      (sync.atomic.ownInt64 hi dq x ={∅,⊤}=∗ Φ #())) -∗
    WP (App (App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.mvccfull.inBounds)) (Val #lo)) (Val #v)) (Val #hi)) (Val #what)) {{ Φ }}

end spec

end mvccfull
end EtcdGrove
end Perennial
