/-
**The capability map's lock, with its reader slots pooled** (prove-ps2-cap, 2026-11-23): what
`etcdserver/api`'s package fact holds (`capInit`, the instance in `apply/Base.lean`), so that
`IsCapabilityEnabled` (`capability.go`) can read-lock `enableMapMu` and read `enabledMap`.
Lean-first (no Rocq counterpart).

`enableMapMu` guards `enabledMap` (`capMapP`): `enabledMap` holds a map that nothing writes after
the package's initializer (`init()` sets it to a fresh map literal; `UpdateCapability` sets it,
under the write lock, to one of `capabilityMaps`' inner maps, which nothing writes either:
`EnableCapability`, the only writer of a map's entries, is called by etcd's tests only), or `nil`
(`capabilityMaps[v]` of a version it does not list). So the lock's invariant holds the variable at
a fraction and its map read-only (`↦$□`): a writer under the guard (`isRWMutexGuard`, kept in the
fact for `UpdateCapability`, whose callers `RaftCluster.Recover`/`SetVersion` are still assumed)
may store another read-only map or `nil`.

The reader slots are in a thread pool at level 0 (`threadPool.isThreadPoolL`, Perennial's
`sync.init_RWMutex_threadPoolL`): a reader borrows one with a level-0 token for the critical
section and gets the token back after `RUnlock` (`IsCapabilityEnabled.spec`; its callers, v3rpc's
interceptors, pay with a gRPC run's level 0, `RevokeCtx.lean`'s header). The pool needs
`threadBound GF ≤ 2 ^ 30` (the lock's `actualMaxReaders`), which the initializer cannot assume:
the fact gives the pool under that bound (`∀ _ : threadBound GF ≤ 2 ^ 30, …`), and the initializer
builds it when the bound holds (`capInit_alloc`).
-/
module

public import Code.go_etcd_io.etcd.server.v3.etcdserver.api
public import Perennial.Golang.Theory.Map
public import Perennial.Proof.sync
public import Perennial.Proof.sync.RWMutexThreads

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProofMode

namespace go_etcd_io.etcd.server.v3.etcdserver.api

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **What `enableMapMu` guards, at the fraction `q`**: `enabledMap` holds `nil` or a read-only
map. -/
def capMapP (q : Qp) : IProp GF :=
  iprop(∃ m : Loc, typedPointsto (globalAddr enabledMap) m (DFrac.own q) ∗
    (⌜m = map.nil⌝ ∨ ∃ mm : GMap GoString Bool, m ↦$□ mm))

instance capMapP_fractional : Fractional (capMapP (GF := GF)) where
  fractional q1 q2 := by
    unfold capMapP
    constructor
    · iintro ⟨%m, Hm, #Hc⟩
      icases (typedPointsto_frac_add _ _ q1 q2).1 $$ Hm with ⟨H1, H2⟩
      isplitl [H1]
      · iexists m; iframe; iframe #
      · iexists m; iframe; iframe #
    · iintro ⟨⟨%m1, H1, #Hc⟩, ⟨%m2, H2, -⟩⟩
      icombine H1 H2 gives %Hm
      subst Hm
      iexists m1
      isplitl [H1 H2]
      · iapply (typedPointsto_frac_add _ _ q1 q2).2; iframe
      · iexact Hc

/-- The pool's namespace. -/
def capPoolN : Namespace := nroot .@ "api_capability_pool"

/-- **The package fact** (persistent): under the thread bound the lock's reader counter needs, the
lock's guard (a writer's, `UpdateCapability`) and its reader slots, pooled at level 0. -/
def capInit : IProp GF :=
  iprop(∀ (_ : threadBound GF ≤ 2 ^ 30), ∃ γ : GName,
    sync.isRWMutexGuard (globalAddr enableMapMu) capMapP ∗
    threadPool.isThreadPoolL capPoolN 0 γ (sync.ownRWMutex (globalAddr enableMapMu) capMapP))

instance capInit_persistent : Persistent (capInit (GF := GF)) := by
  unfold capInit; infer_instance

end defs

section alloc
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [sync_sem : sync.Assumptions]

/-- **The fact's allocation** (the package's initializer): from `enabledMap` holding a read-only
map and the fresh lock, the guard and the pool when the thread bound holds (otherwise the fact is
vacuous). -/
theorem capInit_alloc (E : CoPset) (m : Loc) (mm : GMap GoString Bool) :
    typedPointsto (GF := GF) (globalAddr enabledMap) m (DFrac.own 1) ∗ m ↦$□ mm ∗
      typedPointsto (GF := GF) (globalAddr enableMapMu) (zero_val sync.RWMutex) (DFrac.own 1) ⊢
    |={E}=> capInit := by
  iintro ⟨Hm, #Hmm, Hmu⟩
  by_cases Hb : threadBound GF ≤ 2 ^ 30
  · imod (sync.init_RWMutex_threadPoolL capMapP (E := E) capPoolN 0 (globalAddr enableMapMu) Hb)
      $$ [Hm] Hmu with ⟨%γ, #HG, #HP⟩
    · inext
      unfold capMapP
      iexists m
      iframe Hm
      iright
      iexists mm
      iexact Hmm
    imodintro
    unfold capInit
    iintro %_
    iexists γ
    iframe #
  · imodintro
    unfold capInit
    iintro %H
    exact absurd H Hb

end alloc

end go_etcd_io.etcd.server.v3.etcdserver.api

end Perennial
