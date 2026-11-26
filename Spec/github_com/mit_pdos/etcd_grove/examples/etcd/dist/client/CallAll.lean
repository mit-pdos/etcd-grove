/- Lean-first (no Rocq counterpart).

`CallAll[I, O](addrs, ins, call)` (`examples/etcd/dist/client/await.go`), at `[any, any]` (#50 N10a):
**`call(addrs[c], ins[c])` at every index `c`, all at once** (one goroutine each, joined by a
`sync.WaitGroup`), its results `outs[c], oks[c]`.

**The triple:** the addresses `aL` and the inputs `xs` (as many, read-only), a resource `P c` per index,
and `call`'s triple from `P c` to a result predicate `Q c o ok` (run in a goroutine of its own, so with
no token); `CallAll` returns the slices `outs` and `oks`, of `len(addrs)` elements, and each index's
element of both, with `Q c` of them (the goroutines' results, collected after `wg.Wait()`). The level
token is threaded: each `wg.Add(1)` deposits it until the `go` statement (the wait group backed by
thread tokens, `sync.tokJoinL` at level `0`), whose counter stays below `2 ^ 31` because each
goroutine not done holds a thread token's level `0` (`threadBound GF ≤ 2 ^ 30`; the caller's, as
`RunWatch.spec`'s).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_dist_client

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.Assumptions]

/-- See the file header. -/
abbrev CallAll.spec : Prop :=
  ∀ (addrs ins : GoSlice) (aL : List GoString) (xs : List GoInterface) (call : GoFunc)
    (P : Nat → IProp GF) (Q : Nat → GoInterface → Bool → IProp GF),
  threadBound GF ≤ 2 ^ 30 → xs.length = aL.length →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client ∗
      levelTok 0 ∗ addrs ↦*□ aL ∗ ins ↦*□ xs ∗ ([∗list] c ∈ List.range aL.length, P c) ∗
      □ (∀ (c : Nat) (a : GoString) (x : GoInterface), ⌜aL[c]? = some a ∧ xs[c]? = some x⌝ -∗
          {{ P c }} (App (App (Val #call) (Val #a)) (Val #x))
          {{ (o : GoInterface) (ok : Bool), RET (PairV #o #ok); Q c o ok }}) }}
    (App (App (App (Val #(functions github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.CallAll
      [go.any, go.any])) (Val #addrs)) (Val #ins)) (Val #call))
  {{ (outs oks : GoSlice), RET (PairV #outs #oks); levelTok 0 ∗
      ⌜sint.Z outs.len = aL.length ∧ sint.Z oks.len = aL.length⌝ ∗
      [∗list] c ∈ List.range aL.length, ∃ (o : GoInterface) (ok : Bool),
        typedPointsto (sliceIndexRef GoInterface ((c : Nat) : Int) outs) o (DFrac.own 1) ∗
        typedPointsto (sliceIndexRef Bool ((c : Nat) : Int) oks) ok (DFrac.own 1) ∗ Q c o ok }}

end spec

end etcd_dist_client
end EtcdGrove
end Perennial
