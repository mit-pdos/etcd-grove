/-
**The compactor's watch of its key: a response's facts** (Q1 (b) of `notes/k8s-compactor-plan.md`,
2026-11-04). Lean-first (no Rocq counterpart).

A response of the client's watch of `compact_rev_key` (`watcher.Watch.spec`'s `watchStateElem`)
is a read of a state `σ` at which the caller's read update fired, here with `keyHistOk`: its events
are `σ`'s events of the key through `σ`'s revision (`watchStateRespOk`), whose values
`keyHistOk` says are `keyValOk`. So the response is `respKeyOk`, what `fromWatchResponse` takes
(`respKeyOk_of_state`).
-/
module

public import Proof.k8s_io.apiserver.pkg.storage.etcd3.CompactorDefs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

/-- An event of the revisions `[lo, hi)` of `σ` in `o`'s range is an event of one of them, of a key
in the range. -/
theorem mem_rangeEvents {σ : KVState} {o : OpFull} {lo hi : Nat} {ev : mvcc.EvM}
    (h : ev ∈ σ.rangeEvents o lo hi) :
    ∃ m, lo ≤ m ∧ m < hi ∧ ev ∈ σ.revEvents m ∧ inRange o.key o.base.rangeEnd ev.kv.key := by
  unfold KVState.rangeEvents at h
  rw [List.mem_filter, List.mem_flatten] at h
  obtain ⟨⟨l, hl, hev⟩, hr⟩ := h
  rw [List.mem_map] at hl
  obtain ⟨m, hm, rfl⟩ := hl
  rw [List.mem_range'] at hm
  obtain ⟨i, hi, rfl⟩ := hm
  refine ⟨lo + 1 * i, by omega, by omega, hev, ?_⟩
  simpa using hr

section proofs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **A response of the key's watch at a state with `keyHistOk` is `respKeyOk`** (see the file
header): `o` the watch of the key alone. -/
theorem respKeyOk_of_state (γk : KVNames) (recorded : w64 → IProp GF) (o : OpFull)
    (ho : o.key = compactRevKey) (he : o.base.rangeEnd = []) (σ : KVState) (c c' : w64)
    (v : go_etcd_io.etcd.client.v3.WatchResponse) (r : RespModel) :
    respAt v r ∗ keyHistOk γk recorded σ ∗ watchStateRespOk o σ c c' v r ⊢
      respKeyOk γk recorded v := by
  iintro ⟨#Hr, #Hk, #Hw⟩
  unfold respKeyOk
  isplitr
  · unfold watchStateRespOk
    icases Hw with (⟨%H, #He⟩ | %H | %H | ⟨%H, -⟩)
    · iexact He
    all_goals
      have hn : v.closeErr' = GoInterface.nil :=
        Classical.byContradiction fun h => H.1 (Or.inl h)
      rw [hn]; iapply go_etcd_io.etcd.cache.v3.statusErrOk_nil
  iexists r
  iframe Hr
  unfold watchStateRespOk
  icases Hw with (⟨%H, -⟩ | %H | %H | ⟨%H, #Hev⟩)
  · ileft; ipureintro; exact H.1
  · iright
    iintro !> %i %e %h
    rw [H.2.1] at h; simp at h
  · iright
    iintro !> %i %e %h
    rw [isProgressNotify_events H.2.1] at h; simp at h
  · iright
    iintro !> %i %e %h
    unfold eventsIs
    icases Hev with ⟨%Hlen, #Hall⟩
    obtain ⟨ev, hev⟩ : ∃ ev, (σ.rangeEvents o (sint.nat c + 1) (sint.nat c' + 1))[i]? = some ev := by
      have hi : i < r.events.length := (List.getElem?_eq_some_iff.mp h).1
      exact ⟨_, List.getElem?_eq_getElem (by omega)⟩
    ihave #He := Hall $$ %i %e %ev %h %hev
    unfold eventIs
    icases He with ⟨-, #Hkv⟩
    iexists ev.kv
    iframe Hkv
    unfold keyHistOk
    icases Hk with ⟨-, -, #Hhist⟩
    obtain ⟨m, -, hm, hmem, hin⟩ := mem_rangeEvents (List.mem_of_getElem? hev)
    iapply Hhist
    ipureintro
    obtain ⟨-, -, h0, -, hc', -⟩ := H
    refine ⟨?_, hmem, ?_⟩
    · have : sint.nat c' ≤ σ.rev := by
        rw [show sint.nat c' = (sint.Z c').toNat from rfl]; omega
      omega
    · unfold inRange at hin
      rw [he, if_pos rfl, ho] at hin
      exact of_decide_eq_true hin

end proofs

end k8s
end EtcdGrove
end Perennial
