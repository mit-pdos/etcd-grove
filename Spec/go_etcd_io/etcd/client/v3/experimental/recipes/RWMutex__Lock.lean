/-
`(*RWMutex).Lock()` (`rwmutex.go`): create a key `pfx + "write/<UnixNano>"` with the session's lease
(`newUniqueEphemeralKey`), store it in `myKey`, then `waitOnLastRev(pfx)` until done.

**Users**: `T/v3_lock_test.go:331` (with `Unlock`/`RUnlock` by the test's main goroutine). Snippet:
`recipes/rwmutex.go` (`ReqFencedWrite`).

**Proof sketch**: `newUniqueEphemeralKey.spec` with the caller's update unchanged (its `Q` fired at
the key's creation, the queueing point); on success store `myKey` (`rwmOwn`); then a loop of
`waitOnLastRev.spec` (`R > 0`: a successful write's revision, `sint.Z (W64 R) = R` by
`etcdState_revFits` at the creation's commit, which the update snapshots); its `true` gives the
`etcdLb` with `rwHeld`, at a state reached from the creation (`R ≤ σ.kv.rev`). Errors: `recipeErrOk`.

**What it guarantees** (revision fencing, `notes/specs-only/top.md` §2): when two acquisitions of the
same mutex conflict (two writers, or a writer and a reader), the later key's acquisition saw the
earlier key gone (`rwHeld` at the later one's state: the earlier key's mod revision, below the
later's creation, is no longer there). So the earlier holder held from its acquisition until its key
was deleted (by `Unlock`, or its lease's expiry, an environment step at any time), and a write it
fences with `If(CreateRevision(myKey) = R)` takes effect only while it holds. **With no lease
expiry** (W0's `EnvCfg.leaseExpiry = false`: a deployment whose leases outlive the run) a key is
deleted only by its owner's `Unlock`/`RUnlock` (the caller's delete update), so this is the tests'
exclusion in time: a writer and any other holder never hold at once (snippet
`ReqNoTwoHolders`). With lease expiry it is revision fencing only.

**Changes**: old spec (`rwLockResult`, `rwHeldAt` over the recipes' client invariant) stated the same
fact over the old certificates; now the caller's update at the creation and the history fact.

**Margin**: an error after the key's creation leaves `myKey` set (the code does): the post says so;
the key may still be there.
-/
module

public import Spec.go_etcd_io.etcd.client.v3.experimental.recipes.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Recipes

open Iris Iris.BI EtcdModel EtcdWire ClientV3
open go_etcd_io.etcd.client.v3.experimental.recipes

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.experimental.recipes.Assumptions]

/-- **`m.Lock()`**: a writer's key `pfx/write/<n>` created (with the session's lease) by one transaction the caller's update linearizes; `nil` only once every key under `pfx` older than it is gone (`rwHeld`). -/
def RWMutex.Lock.spec : Prop :=
  ∀ (m : Loc) (γ : Cluster) (who : Principal) (id : w64) (pfx : GoString) (my : Option RKSt)
    (Q : State → State → GoString → Resp → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.experimental.recipes ∗ rwmOwn m γ who id pfx my ∗ etcdPeek γ ∗
      AU <{ ∃∃ (σ : State), etcdState γ σ }> @ ⊤ \ ↑etcdN, ∅
        <{ ∀∀ (σ' : State) (k : GoString) (res : Resp),
             ⌜uniqueKeyIn (pfx ++ go!"write") k ∧ Step who (putNewReq k [] (sint.Z id)) σ σ' res ∧ ¬ txnCmpFailed res⌝ ∗
             etcdState γ σ',
           COMM Q σ σ' k res }> }}
    (App (Val (m @!! go.GoType.PointerType RWMutex.ty @!! go!"Lock")) (Val #()))
  {{ (err : GoInterface), RET #err;
      (∃ σ σ' k res, Q σ σ' k res ∗
        ((⌜txnSucceeded res⌝ ∗
           rwmOwn m γ who id pfx (some { live := true, key := k, rev := W64 σ'.kv.rev, val := [] }) ∗
           ((⌜err ≠ GoInterface.nil⌝ ∗ recipeErrOk err) ∨
            (⌜err = GoInterface.nil⌝ ∗ ∃ σh : State, etcdLb γ σh ∗
              ⌜σ'.kv.rev ≤ σh.kv.rev ∧ rwHeld (pfxRange (pfx)) σ'.kv.rev σh.kv.store⌝))) ∨
         (⌜∃ e, res = .err e ∧ err = errVal e⌝ ∗ rwmOwn m γ who id pfx my))) ∨
      (indefCall err ∗ rwmOwn m γ who id pfx my) }}

end spec

end Recipes
end EtcdGrove
end Perennial
