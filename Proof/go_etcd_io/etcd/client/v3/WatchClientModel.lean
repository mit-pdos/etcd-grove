/-
**`run`'s bookkeeping** (the watch slice's unit W-C, 2026-10-15; pure): what the gRPC watch stream's
main goroutine (`watchGRPCStream.run`, `client/v3/watch.go`) knows of the requests it sent, the
responses it received, its substreams and its maps, and the facts its proof keeps about them.
Lean-first, no Rocq counterpart.

* `WPh`: a substream's phase: `queued` (in `resuming`, its create sent at an up position or not),
  `reg X` (registered at the watch id `X`, in `substreams`), `closedRun X` (registered, its `recvc`
  closed by `run` on the server's cancel, in `closing`), `orphan` (its create refused: `recvc`
  closed, in no map).
* `RunSt`: the requests sent (`L`), the responses received (`Dm`), the pending create (`pend`),
  the answered positions (`ansd`), the registered ids (`regs`), `substreams` (`M`), `resuming`
  (`l`), `closing` (`CL`), `cancelSet` (`CS`).
* `phOk S ws ph`: a substream's phase agrees with the maps; `gOk S U`: the facts across them
  (`U`, the substreams `run` made and has not yet seen stop).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.InvWatchStream

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace client

open v3rpc

/-! ## The model -/

/-- A substream's phase (see the file header). -/
inductive WPh where
  | queued (si : Option Nat)
  | reg (X : w64)
  | closedRun (X : w64)
  | orphan

/-- What `run` knows (see the file header). -/
structure RunSt where
  L : List WatchReqM
  Dm : List WatchRespM
  pend : Option Nat
  ansd : List Nat
  regs : List w64
  M : GMap w64 Loc
  l : List Loc
  CL : GMap Loc Unit
  CS : GMap w64 Unit

/-- **A substream's phase agrees with the maps.** -/
def phOk (S : RunSt) (ws : Loc) : WPh → Prop
  | .queued si => (∀ X, S.M !! X ≠ some ws) ∧ ws ∈ S.l ∧ S.CL !! ws = none ∧
      (∀ i, si = some i → S.pend = some i ∧ S.l.head? = some ws) ∧
      (si = none → S.l.head? = some ws → S.pend = none)
  | .reg X => S.M !! X = some ws ∧ ws ∉ S.l ∧ S.CL !! ws = none ∧ X ∈ S.regs ∧
      X ≠ W64 (-1) ∧
      (S.CS !! X = none → ∀ i, S.L[i]? = some (WatchReqM.cancel X) → i ∈ S.ansd) ∧
      (∀ i i', S.L[i]? = some (WatchReqM.cancel X) → S.L[i']? = some (WatchReqM.cancel X) → i ∉ S.ansd →
        i' ∉ S.ansd → i = i')
  | .closedRun X => S.M !! X = some ws ∧ ws ∉ S.l ∧ S.CL !! ws = some () ∧ X ∈ S.regs ∧
      X ≠ W64 (-1) ∧ ¬ idLive S.Dm X ∧ (∀ i, S.L[i]? = some (WatchReqM.cancel X) → i ∈ S.ansd)
  | .orphan => (∀ X, S.M !! X ≠ some ws) ∧ ws ∉ S.l ∧ S.CL !! ws = none

/-- **The facts across the maps and the stream** (`U`: the substreams `run` made, not yet seen
stop). -/
def gOk (S : RunSt) (U : GMap Loc Unit) : Prop :=
  (∀ X ws, S.M !! X = some ws → U !! ws = some ()) ∧
  (∀ X Y ws, S.M !! X = some ws → S.M !! Y = some ws → X = Y) ∧
  (∀ ws ∈ S.l, ws ≠ null → U !! ws = some ()) ∧
  (S.l.filter (fun x => decide (x ≠ null))).Nodup ∧
  (∀ ws, S.CL !! ws = some () → U !! ws = some ()) ∧
  U !! null = none ∧
  (∀ x ∈ S.L, (∃ c, x = WatchReqM.create c) ∨ (∃ id, x = WatchReqM.cancel id)) ∧
  (∀ (i : Nat) c, S.L[i]? = some (WatchReqM.create c) → i ∈ S.ansd ∨ S.pend = some i) ∧
  (∀ (i : Nat) (id : w64), S.L[i]? = some (WatchReqM.cancel id) → id ∈ S.regs) ∧
  (∀ i, S.pend = some i → i ∉ S.ansd ∧ (∃ c, S.L[i]? = some (WatchReqM.create c)) ∧ S.l ≠ []) ∧
  (∀ i ∈ S.ansd, i < S.L.length) ∧
  (∀ j m ρ, S.Dm[j]? = some m → m.src = some ρ →
    ρ.id ≠ W64 (-1) ∧ idLive (S.Dm.take j) ρ.id) ∧
  (∀ m ∈ S.Dm, m.src = none → m.created = true → m.canceled = false → m.watchId ∈ S.regs)

/-- The model at `run`'s start: nothing sent, received or made. -/
def RunSt.init : RunSt :=
  { L := [], Dm := [], pend := none, ansd := [], regs := [], M := ∅, l := [], CL := ∅, CS := ∅ }

theorem gOk_init : gOk RunSt.init ∅ := by
  unfold gOk RunSt.init
  simp [GMap.lookup_empty]

/-! ## Watch ids -/

/-- The control responses of the id `X`. -/
abbrev ctrlOf (L : List WatchRespM) (X : w64) : List WatchRespM :=
  L.filter (fun m => decide (m.src = none ∧ m.watchId = X))

/-- **`idLive` one response on**: a control response of the id decides; any other leaves it. -/
theorem idLive_snoc (L : List WatchRespM) (m : WatchRespM) (X : w64) :
    idLive (L ++ [m]) X =
      if m.src = none ∧ m.watchId = X then (m.created && !m.canceled) = true else idLive L X := by
  unfold idLive
  rw [List.filter_append]
  by_cases h : m.src = none ∧ m.watchId = X
  · rw [if_pos h]
    have : List.filter (fun m => decide (m.src = none ∧ m.watchId = X)) [m] = [m] := by
      simp [h]
    rw [this, List.getLast?_append]
    simp
  · rw [if_neg h]
    have : List.filter (fun m => decide (m.src = none ∧ m.watchId = X)) [m] = [] := by
      simp [h]
    rw [this, List.append_nil]

/-- A live id was announced: some control response of the id is a created, not canceled, one. -/
theorem idLive_exists {L : List WatchRespM} {X : w64} (h : idLive L X) :
    ∃ m ∈ L, m.src = none ∧ m.watchId = X ∧ m.created = true ∧ m.canceled = false := by
  unfold idLive at h
  cases hl : (L.filter (fun m => decide (m.src = none ∧ m.watchId = X))).getLast? with
  | none => rw [hl] at h; cases h
  | some m =>
    rw [hl] at h
    simp only [Option.map_some, Option.some.injEq, Bool.and_eq_true, Bool.not_eq_eq_eq_not,
      Bool.not_true] at h
    have hm := List.mem_of_getLast? hl
    rw [List.mem_filter] at hm
    simp only [decide_eq_true_eq] at hm
    exact ⟨m, hm.1, hm.2.1, hm.2.2, h.1, h.2⟩

/-- The responses with events of the watcher `w`, by their mvcc response. -/
theorem sentEvsOf_snoc (L : List WatchRespM) (m : WatchRespM) (w : Loc) :
    sentEvsOf (L ++ [m]) w =
      sentEvsOf L w ++ (match m.src with
        | some ρ => if ρ.w = w ∧ ρ.evs ≠ [] then [ρ] else []
        | none => []) := by
  unfold sentEvsOf
  rw [List.filterMap_append, List.filter_append]
  congr 1
  cases h : m.src with
  | none => simp [h]
  | some ρ =>
    by_cases hc : ρ.w = w ∧ ρ.evs ≠ []
    · simp [h, hc]
    · simp only [List.filterMap_cons, h, List.filterMap_nil, if_neg hc]
      simp only [List.filter_eq_nil_iff, List.mem_singleton, forall_eq, decide_eq_true_eq]
      exact hc

/-- The events of a list of responses, those without events left out. -/
theorem flatten_evs_filter (rs : List mvcc.RespM) :
    ((rs.filter (fun x => decide (x.evs ≠ []))).map mvcc.RespM.evs).flatten =
      (rs.map mvcc.RespM.evs).flatten := by
  induction rs with
  | nil => rfl
  | cons x xs ih =>
    by_cases h : x.evs = []
    · rw [List.filter_cons_of_neg (by simp [h])]
      simp only [List.map_cons, List.flatten_cons, h, List.nil_append]
      exact ih
    · rw [List.filter_cons_of_pos (by simp [h])]
      simp only [List.map_cons, List.flatten_cons]
      rw [ih]

end client
end EtcdGrove
end Perennial
