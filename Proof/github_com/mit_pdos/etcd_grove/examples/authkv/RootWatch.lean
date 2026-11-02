/-
**Root's watch of the history** (`Main`'s `root.Watcher.Watch(hctx, "", WithPrefix(), WithRev(1))`
and `Collect`; 2026-10-30). Lean-first (no Rocq counterpart).

The watch reads the KV state through the history invariant's read update (`akHist_readAu`): each
response is a read of a state `σ` with `stateHistOk σ`, its events `σ`'s events of the range
(`watchStateRespOk`), each one of some revision's (`rangeEvents_mem`), so admitted (`evHistOk`);
a set-up put's event is a put, as the state is well formed up to the response's last revision
(`revEvents_setupPut_put`). `root_resp` is `Collect.spec`'s premise on a response at the per-event
fact `rootEvOk` (no relation kept on the cursor), which `histOk_of_rootEvOk` turns into
`CheckHistory`'s premise. `watch_all_ok`: the options make a range watch from revision `1`.

**u's watch** (`ucli.Watcher.Watch(uctx, lo, WithRange(hi), WithRev(1))`, `watch_ab_ok`): its events
are of the range `[a, b)` (`rangeEvents` filters by it), which is the range u may read
(`permitted_of_inRange_ab`); `u_resp` is `Collect.spec`'s premise at `permittedK u` of the key, so
`Main`'s check of each event by `Permitted("u", key)` never panics. No auth fact is needed: a
refused watch has no events.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.authkv.Hist
public import Proof.github_com.mit_pdos.etcd_grove.examples.common.RespChan
public import Proof.github_com.mit_pdos.etcd_grove.examples.authkv.WorkCalls

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace authkv

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver client

section pure
variable [GooseExts]

/-- **A collected event of root's watch the history admits** (`histOk_of_evHistOk`'s premise). -/
def rootEvOk (e : common.wev) : Prop :=
  permittedK (writerK e.Key') e.Key' ∨ e.Key' = endKey ∨ (e.Put' = true ∧ setupPutK e.Key' e.Val')

/-- `CheckHistory`'s premise, from every collected event's `rootEvOk`. -/
theorem histOk_of_rootEvOk (evs : List common.wev)
    (h : ∀ (i : Nat) (e : common.wev), evs[i]? = some e → rootEvOk e) : histOk evs endKey :=
  histOk_of_evHistOk evs fun e he => by
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 he
    exact h i e hi

/-- An event of a range's events is one of a revision's in the interval. -/
theorem rangeEvents_mem (σ : KVState) (o : OpFull) (lo hi : Nat) (ev : mvcc.EvM)
    (h : ev ∈ σ.rangeEvents o lo hi) : ∃ m, lo ≤ m ∧ m < hi ∧ ev ∈ σ.revEvents m := by
  unfold KVState.rangeEvents at h
  obtain ⟨l, hl, hev⟩ := List.mem_flatten.1 (List.mem_filter.1 h).1
  obtain ⟨m, hm, rfl⟩ := List.mem_map.1 hl
  obtain ⟨hm1, hm2⟩ := List.mem_range'_1.1 hm
  exact ⟨m, hm1, by omega, hev⟩

/-- `Watch("", WithPrefix(), WithRev(1))`: a range watch from revision `1`. -/
theorem watch_all_ok :
    (opWatchModel ([] : GoString) [withPrefixM, withRevM (W64 1)]).isRangeWatch (W64 1) = true ∧
      ¬ opWatchPanics ([] : GoString) [withPrefixM, withRevM (W64 1)] := by
  refine ⟨?_, ?_⟩
  · simp [opWatchModel, op_simps, OpFull.isRangeWatch]
  · simp [opWatchModel, opWatchPanics, OpFull.watchPanics, op_simps]

/-- `Watch(lo, WithRange(hi), WithRev(1))`: a range watch of `[a, b)` from revision `1`. -/
theorem watch_ab_ok :
    ((opWatchModel lo [withRangeM hi, withRevM (W64 1)]).isRangeWatch (W64 1) = true ∧
      ¬ opWatchPanics lo [withRangeM hi, withRevM (W64 1)]) ∧
    (opWatchModel lo [withRangeM hi, withRevM (W64 1)]).key = lo ∧
    (opWatchModel lo [withRangeM hi, withRevM (W64 1)]).base.rangeEnd = hi := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · simp [opWatchModel, op_simps, OpFull.isRangeWatch]
  · simp [opWatchModel, opWatchPanics, OpFull.watchPanics, op_simps]
  · simp [opWatchModel, op_simps]
  · simp [opWatchModel, op_simps]

end pure

section resp
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **One response of root's watch** (see the file header): `Collect.spec`'s premise at
`I := True`, `A := True` and the per-event fact `rootEvOk`. -/
theorem root_resp (o : OpFull) (n : Nat) (c c' : w64)
    (v : go_etcd_io.etcd.client.v3.WatchResponse) (r : RespModel) (hne : ¬ watchErr v)
    (_ : True) :
    ⊢ □ (True : IProp GF) -∗
      common.stateOk (GF := GF) o (fun σ => iprop(⌜stateHistOk σ⌝)) c c' v r ={⊤}=∗
      ⌜True⌝ ∗
      □ ∀ (j : Nat) (e : EvModel), ⌜r.events[j]? = some e⌝ -∗
        ∃ kvv : EtcdKv, kvValAt e.kv kvv ∗ iprop(⌜rootEvOk (common.evWev e kvv.value)⌝) := by
  iintro - Hok
  unfold common.stateOk
  icases Hok with ⟨%σ, %HS, #Hr⟩
  unfold watchStateRespOk
  icases Hr with (⟨%H, -⟩ | %H | %H | ⟨%H, #Hev⟩)
  · exact absurd H.1 hne
  · imodintro
    isplitr
    · ipureintro; trivial
    iintro !> %j %e %h
    rw [H.2.1] at h
    simp at h
  · have he0 := isProgressNotify_events H.2.1
    imodintro
    isplitr
    · ipureintro; trivial
    iintro !> %j %e %h
    rw [he0] at h
    simp at h
  · obtain ⟨-, -, -, -, -, -, hok⟩ := H
    iunfold eventsIs at Hev
    icases Hev with ⟨%hlen, #Hall⟩
    imodintro
    isplitr
    · ipureintro; trivial
    iintro !> %j %e %hj
    have hjl : j < (σ.rangeEvents o (sint.nat c + 1) (sint.nat c' + 1)).length := by
      rw [← hlen]; exact (List.getElem?_eq_some_iff.mp hj).1
    have hev := List.getElem?_eq_getElem hjl
    ihave #Hei := Hall $$ %j %e %_ %hj %hev
    iunfold eventIs at Hei
    icases Hei with ⟨%Hp, #Hkv⟩
    obtain ⟨hty, hek, -⟩ := Hp
    iexists _
    iframe Hkv
    ipureintro
    obtain ⟨m, -, hm2, hm⟩ := rangeEvents_mem σ o _ _ _ (List.mem_of_getElem? hev)
    unfold rootEvOk common.evWev
    simp only
    rw [hek]
    rcases HS m _ hm with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · have hd := revEvents_setupPut_put σ (sint.nat c') m hok (by omega) _ hm h
      rw [hd] at hty
      simp only [Bool.false_eq_true, ↓reduceIte] at hty
      exact Or.inr (Or.inr ⟨by simp [hty], h⟩)

/-- **One response of u's watch** (see the file header): `Collect.spec`'s premise at `I := True`,
`A := True` and the per-event fact `permittedK u` of the key, for a watch of `[a, b)`. -/
theorem u_resp (o : OpFull) (ho : o.key = lo ∧ o.base.rangeEnd = hi) (Q : KVState → IProp GF)
    (n : Nat) (c c' : w64) (v : go_etcd_io.etcd.client.v3.WatchResponse) (r : RespModel)
    (hne : ¬ watchErr v) (_ : True) :
    ⊢ □ (True : IProp GF) -∗ common.stateOk (GF := GF) o Q c c' v r ={⊤}=∗
      ⌜True⌝ ∗
      □ ∀ (j : Nat) (e : EvModel), ⌜r.events[j]? = some e⌝ -∗
        ∃ kvv : EtcdKv, kvValAt e.kv kvv ∗
          iprop(⌜permittedK go!"u" (common.evWev e kvv.value).Key'⌝) := by
  iintro - Hok
  unfold common.stateOk
  icases Hok with ⟨%σ, -, #Hr⟩
  unfold watchStateRespOk
  icases Hr with (⟨%H, -⟩ | %H | %H | ⟨%H, #Hev⟩)
  · exact absurd H.1 hne
  · imodintro
    isplitr
    · ipureintro; trivial
    iintro !> %j %e %h
    rw [H.2.1] at h
    simp at h
  · have he0 := isProgressNotify_events H.2.1
    imodintro
    isplitr
    · ipureintro; trivial
    iintro !> %j %e %h
    rw [he0] at h
    simp at h
  · iunfold eventsIs at Hev
    icases Hev with ⟨%hlen, #Hall⟩
    imodintro
    isplitr
    · ipureintro; trivial
    iintro !> %j %e %hj
    have hjl : j < (σ.rangeEvents o (sint.nat c + 1) (sint.nat c' + 1)).length := by
      rw [← hlen]; exact (List.getElem?_eq_some_iff.mp hj).1
    have hev := List.getElem?_eq_getElem hjl
    ihave #Hei := Hall $$ %j %e %_ %hj %hev
    iunfold eventIs at Hei
    icases Hei with ⟨%Hp, #Hkv⟩
    obtain ⟨-, hek, -⟩ := Hp
    iexists _
    iframe Hkv
    ipureintro
    have hin := (List.mem_filter.1 (List.mem_of_getElem? hev)).2
    rw [ho.1, ho.2] at hin
    unfold common.evWev
    simp only
    rw [hek]
    exact permitted_of_inRange_ab _ hin

/-- **`CheckHistory`'s premise from `Collect`'s result** at `rootEvOk` (`histOk_of_rootEvOk`). -/
theorem histOk_of_collected (evs : List common.wev) :
    (□ ∀ (i : Nat) (e : common.wev), ⌜evs[i]? = some e⌝ -∗ iprop(⌜rootEvOk e⌝)) ⊢
      (⌜histOk evs endKey⌝ : IProp GF) := by
  iintro #H
  ihave %Hall : ⌜∀ (i : Nat) (e : common.wev), evs[i]? = some e → rootEvOk e⌝ $$ []
  · iapply BI.pure_forall.2
    iintro %i
    iapply BI.pure_forall.2
    iintro %e
    iapply BI.pure_wand.1
    iintro %h
    iapply H $$ %i %e %h
  ipureintro; exact histOk_of_rootEvOk evs Hall

end resp

end authkv
end EtcdGrove
end Perennial
