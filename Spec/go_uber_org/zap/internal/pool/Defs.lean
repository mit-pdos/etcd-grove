/-
The vocabulary of zap's generic `sync.Pool` wrapper (`internal/pool/pool.go`; zap-z2, 2026-11-23):
`ownPool`, a pool `New` returned, not used yet, and `isPool`, a pool whose elements satisfy a
predicate, which `Get` returns and `Put` takes (over Perennial's `sync.isPool`). Lean-first.
-/
module

public import GeneratedProof.go_uber_org.zap.internal.pool
public import Perennial.Proof.sync.PoolDefs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- An element of a `pool.Pool[T]` (`T`'s values are `V`s): a `V` boxed at `T` (`Put` and `New`'s
closure convert their `T` to `any`), satisfying `Q`. -/
def zap.internal.pool.elemOk {V : Type} (T : go.GoType) (Q : V → IProp GF) (x : GoAny) :
    IProp GF :=
  iprop(∃ v : V, ⌜x = interface.mkOk T #v⌝ ∗ Q v)

/-- `fn : func() T` returns a `V` satisfying `Q` (persistent: a pool may call it any number of
times). -/
def zap.internal.pool.fnSpec {V : Type} (fn : GoFunc) (Q : V → IProp GF) : IProp GF :=
  iprop({{ True }} (App (Val #fn) (Val #())) {{ (v : V), RET #v; Q v }})

instance zap.internal.pool.fnSpec_persistent {V : Type} (fn : GoFunc) (Q : V → IProp GF) :
    Persistent (zap.internal.pool.fnSpec (GF := GF) fn Q) := by
  unfold zap.internal.pool.fnSpec; infer_instance

/-- **The pool at `p`, as `New[T](fn)` returns it** (exclusive): its `sync.Pool` not used yet, whose
`New` (`func() any { return fn() }`) meets `sync.newSpec` for the elements of any `Q` that `fn`'s
results satisfy. `ownPool_init` turns it into an `isPool`. -/
def zap.internal.pool.ownPool {V : Type} [ZeroVal V] (T : go.GoType) (p : Loc)
    (fn : GoFunc) : IProp GF :=
  iprop(∃ v : sync.Pool,
    typedPointsto (structFieldRef (go_uber_org.zap.internal.pool.Pool V) go!"pool" p) v (DFrac.own 1) ∗
    ⌜v.local' = null ∧ v.New' ≠ func.nil⌝ ∗
    □ (∀ Q : V → IProp GF, zap.internal.pool.fnSpec fn Q -∗
        sync.newSpec v.New' iprop(True) (zap.internal.pool.elemOk T Q)))

/-- **A `pool.Pool[T]` at `p` whose elements satisfy `Q`** (persistent): its `sync.Pool` is an
`isPool` with a non-nil `New` that needs nothing, whose values are `T`-boxed `V`s with `Q`. `Get`
returns one, `Put` takes one. -/
def zap.internal.pool.isPool {V : Type} [ZeroVal V] (T : go.GoType) (p : Loc)
    (Q : V → IProp GF) : IProp GF :=
  iprop(∃ f : GoFunc, ⌜f ≠ func.nil⌝ ∗
    sync.isPool (structFieldRef (go_uber_org.zap.internal.pool.Pool V) go!"pool" p) f iprop(True)
      (zap.internal.pool.elemOk T Q))

instance zap.internal.pool.isPool_persistent {V : Type} [ZeroVal V] (T : go.GoType)
    (p : Loc) (Q : V → IProp GF) : Persistent (zap.internal.pool.isPool (GF := GF) T p Q) := by
  unfold zap.internal.pool.isPool; infer_instance

/-- A pool `New` returned becomes an `isPool` for any `Q` its function's results satisfy. -/
theorem zap.internal.pool.ownPool_init [sync.Assumptions] {V : Type} [ZeroVal V] (T : go.GoType) (p : Loc)
    (fn : GoFunc) (Q : V → IProp GF) (E : CoPset) :
    zap.internal.pool.ownPool (GF := GF) (V := V) T p fn ∗ zap.internal.pool.fnSpec fn Q ⊢
      |={E}=> zap.internal.pool.isPool T p Q := by
  unfold zap.internal.pool.ownPool zap.internal.pool.isPool
  iintro ⟨⟨%v, Hp, %hv, #Hnew⟩, #Hfn⟩
  imod sync.init_Pool _ v iprop(True) (zap.internal.pool.elemOk T Q) E hv.1 $$ [Hp] with #Hpool
  · iframe
    iapply Hnew
    iexact Hfn
  imodintro
  iexists v.New'
  iframe #
  ipureintro
  exact hv.2

end defs

end EtcdGrove
end Perennial
