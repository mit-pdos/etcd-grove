/-
The exported results of etcd's `cache` package, restated at top level, with the trust base of
each printed in the build log (`#print axioms`): what the cache proofs come to, in one file.
Every Go function of the package has a `Spec`/`Proof` pair and a linked result
(`Link.lean`, generated); the results below are the ones a client of the package uses.

* **`New`** (`cache_New`): from a client of etcd for the prefix (`isEtcdClient`, the trust
  boundary about the client) and options, `New` returns either `nil` and an error (a rejected
  configuration) or a cache (`isCacheFields`, every field) with its handles (`cacheHandles`):
  the readers `Get` needs, the slots `Watch` needs, the handles `WaitForNextResync` needs, the
  token `Close` needs; its three loops (resync, watch, progress requests) run.
* **`Get`** (`cache_Get`): the answer is etcd's state at a revision the cache holds
  (`isEtcdKvs`), restricted to the requested range; a linearizable request is at least as fresh
  as etcd was when it started (`cacheGetResult`).
* **`Watch`** (`cache_Watch`) and **its delivery theorem** (`cache_Watch_delivery`): every
  prefix of the responses the caller receives on the returned channel is a `cacheWatchLog`, and
  such a log is, unless the request was rejected, exactly etcd's events under the key range from
  the start revision on, in order, with no gap and no duplicate, each batch certified by etcd's
  step from the previous one (`EtcdStep`), possibly ended by a compaction's cancel after
  everything below the compaction revision.
* `WaitForRevision`, `WaitForNextResync`, `Close`, `Ready`, `WaitReady`, `RequestProgress`: the
  remaining methods of `Cache`.
-/
module

public import Proof.go_etcd_io.etcd.cache.v3.Link

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.cache.v3

section results
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

/-- `New(client, prefix, opts...)` (`Spec/go_etcd_io/etcd/cache/v3/New.lean`). -/
theorem cache_New : New.spec (GF := GF) (hG := hG) := wp_New

/-- `c.Get(ctx, key, opts...)` (`Spec/go_etcd_io/etcd/cache/v3/Cache__Get.lean`). -/
theorem cache_Get : Cache.Get.spec (GF := GF) (hG := hG) := Cache.wp_Get

/-- `c.Watch(ctx, key, opts...)` (`Spec/go_etcd_io/etcd/cache/v3/Cache__Watch.lean`). -/
theorem cache_Watch : Cache.Watch.spec (GF := GF) (hG := hG) := Cache.wp_Watch

/-- **The `Watch` delivery theorem.** A log `L` of responses received from a `Watch` on
`[key, rangeEnd)` from `sr` (a `cacheWatchLog`: what `cache_Watch`'s channel and
`wp_cacheWatch_receive` give a consumer) is one of:
* the demux's delivery to the watch: its events are exactly the events of etcd's batches `bs`
  whose keys are in the range, in order (no gap, no duplicate), the log in order (`SentOrdered`),
  the batches each of one revision, increasing, and each certified by etcd's step from at most
  the previous one (`certChain (etcdStepCert pfx) p₀ bs`), and for `sr ≠ 0` all at or above
  `sr` with `p₀ < sr` (nothing etcd did from `sr` on is missing);
* such a delivery, complete below a compaction revision `n`, followed by the compaction's
  cancel response;
* the single cancel response of a rejected request. -/
theorem cache_Watch_delivery (pfx key rangeEnd : GoString) (sr : w64) (L : List RespModel) :
    cacheWatchLog (GF := GF) (etcdStepCert pfx) (some (keyPredForRange key rangeEnd)) sr L ⊢
      (∃ (bs : List Batch) (p₀ : Int),
        ⌜eventsOf L = bs.flatten.filter (fun e => keyPredForRange key rangeEnd e.key) ∧
          SentOrdered L ∧ StreamOk bs ∧
          (sr ≠ W64 0 → p₀ < sint.Z sr ∧ ∀ b ∈ bs, sint.Z sr ≤ sint.Z (batchRev b))⌝ ∗
        certChain (etcdStepCert pfx) p₀ bs) ∨
      (∃ (L0 : List RespModel) (n : w64) (bs : List Batch) (p₀ : Int),
        ⌜L = L0 ++ [cancelModel n] ∧
          eventsOf L0 = bs.flatten.filter (fun e => keyPredForRange key rangeEnd e.key) ∧
          SentOrdered L0 ∧ StreamOk bs ∧ (∀ b ∈ bs, sint.Z (batchRev b) < sint.Z n) ∧
          (sr ≠ W64 0 → p₀ < sint.Z sr ∧ ∀ b ∈ bs, sint.Z sr ≤ sint.Z (batchRev b))⌝ ∗
        certChain (etcdStepCert pfx) p₀ bs) ∨
      ⌜∃ r, L = [r] ∧ r.canceled = true ∧ r.events = []⌝ := by
  unfold cacheWatchLog
  iintro (H | ⟨%L0, %n, %HL, H⟩ | %H)
  · ileft
    iapply cacheWatch_delivery pfx key rangeEnd sr L $$ H
  · iright; ileft
    icases cacheWatch_delivery_compacted pfx key rangeEnd sr n L0 $$ H with
      ⟨%bs, %p₀, %Hf, Hc⟩
    iexists L0, n, bs, p₀
    iframe Hc
    ipureintro
    exact ⟨HL, Hf⟩
  · iright; iright
    ipureintro; exact H

/-- `c.WaitForRevision(ctx, rev)`. -/
theorem cache_WaitForRevision : Cache.WaitForRevision.spec (GF := GF) (hG := hG) :=
  Cache.wp_WaitForRevision

/-- `c.WaitForNextResync(ctx)`. -/
theorem cache_WaitForNextResync : Cache.WaitForNextResync.spec (GF := GF) (hG := hG) :=
  Cache.wp_WaitForNextResync

/-- `c.Close()`. -/
theorem cache_Close : Cache.Close.spec (GF := GF) (hG := hG) := Cache.wp_Close

end results

end EtcdGrove
end Perennial

/-! The trust base of the cache's results, printed in the build log. -/
#print axioms Perennial.EtcdGrove.cache_New
#print axioms Perennial.EtcdGrove.cache_Get
#print axioms Perennial.EtcdGrove.cache_Watch
#print axioms Perennial.EtcdGrove.cache_Watch_delivery
#print axioms Perennial.EtcdGrove.cache_WaitForRevision
#print axioms Perennial.EtcdGrove.cache_WaitForNextResync
#print axioms Perennial.EtcdGrove.cache_Close
