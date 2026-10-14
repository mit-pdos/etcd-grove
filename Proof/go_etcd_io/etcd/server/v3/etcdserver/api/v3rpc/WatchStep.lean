/-
**The watch guarantee as the server model's steps** (the watch slice's unit W-S, 2026-10-14):
the pure bridge from mvcc's watch events (`mvcc.watchEvents log rng lo hi`: the events of the
revisions `[lo, hi)` of `log` whose key the range `rng` covers, `InvWatchStore.lean`) to the
server model's step facts (`srvStep E r0 r1 pfx evs`, `ClientModel.lean`, over the client's
events of a revision under a prefix, `txn.revEvs`). Lean-first, no Rocq counterpart.

* `evmToEtcd`: the client's event (`EtcdEv`) of a watch event (`EvM`): a delete is type `1`, a
  put type `0`, the key-value as sent.
* `watchEvents_rev_eq`: for a range covering exactly the keys under `pfx` (`hcov`), the watch
  events of one revision `x` of a well-formed log (`LogWf'`, `log.length < 2 ^ 63`: what mvcc's
  certificate `idxCert` gives) are the client's events of `x` under `pfx`.
* `watchEvents_filter_rev`: a block of watch events, cut at a revision (by `kv.modRev`), is that
  revision's watch events; `watchEvents_mid`: two consecutive cumulative blocks give the events
  between.
* `watchStreamSpec_step`: no watch event strictly between `r0` and `r1` gives no client event
  there, and the client's events of `r1` are its watch events; `srvStep_of_watch`: with a
  certified small log, the server model's step.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.ClientModel
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.SyncModel

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace v3rpc

open Iris Iris.BI Iris.ProofMode mvcc txn

/-! ## The client's event of a watch event -/

/-- **The client's event of a watch event**: a delete is type `1`, a put type `0` (`changeEv`'s
convention, etcd's `mvccpb.Event_EventType`), with the key-value as the watch event carries it. -/
def evmToEtcd (e : EvM) : EtcdEv := { typ := if e.del then W32 1 else W32 0, kv := e.kv }

/-- The key-value a change of revision `r` writes on the state `s`, as `changeKv` finds it: a
put's new record (`putNv`), a delete's key alone. -/
def chKv (r : w64) (s : List EtcdKv) : Change → EtcdKv
  | .put k val l => putNv r k val l s
  | .del k => zeroKv k

theorem chKv_key (r : w64) (s : List EtcdKv) (c : Change) : (chKv r s c).key = c.key := by
  cases c with
  | put k val l => exact putNv_key r k val l s
  | del k => rfl

/-- `changeKv` of the first change of `c :: cs`. -/
theorem changeKv_zero (r : w64) (b : List EtcdKv) (hb : b.Pairwise etcdKvLess) (c : Change)
    (cs : List Change) : changeKv r b (c :: cs) 0 = some (chKv r b c) := by
  cases c with
  | put k val l =>
    unfold changeKv
    simp only [List.getElem?_cons_zero, List.take_succ_cons, List.take_zero]
    show findKey k (applyChanges r b [.put k val l]) = _
    rw [show applyChanges r b [.put k val l] = putKv r k val l b from rfl,
      findKey_putKv_self_eq hb]
    simp only [chKv, putNv, findKey]
    cases b.find? (fun v => decide (v.key = k)) <;> rfl
  | del k => rfl

/-- `changeKv` of a later change of `c :: cs` is that of `cs` from the state after `c`. -/
theorem changeKv_succ (r : w64) (b : List EtcdKv) (c : Change) (cs : List Change) (i : Nat) :
    changeKv r b (c :: cs) (i + 1) = changeKv r (applyChange r b c) cs i := by
  unfold changeKv
  simp only [List.getElem?_cons_succ, List.take_succ_cons]
  rfl

/-- **`evsOfRevM` one change at a time**. -/
theorem evsOfRevM_cons (m : Nat) (b : List EtcdKv) (hb : b.Pairwise etcdKvLess) (c : Change)
    (cs : List Change) :
    evsOfRevM m b (c :: cs) =
      evOfKv m (chKv (W64 (m : Int)) b c) :: evsOfRevM m (applyChange (W64 (m : Int)) b c) cs := by
  unfold evsOfRevM
  rw [List.length_cons, List.range_succ_eq_map, List.filterMap_cons, changeKv_zero _ b hb,
    List.filterMap_map]
  simp only [Option.map_some]
  congr 1

/-- **The events of one revision, under the prefix** (from the state `b` before them): a range
covering exactly the keys under `pfx` keeps of the watch events the client's events under `pfx`. -/
theorem evsOfRevM_under (m : Nat) (rng : WatchRange) (pfx : GoString)
    (hcov : ∀ k, rng.covers k = true ↔ pfx <+: k) (hm : W64 (m : Int) ≠ W64 0) :
    ∀ (cs : List Change) (b : List EtcdKv), b.Pairwise etcdKvLess → CrPos b →
      ((evsOfRevM m b cs).filter (fun ev => rng.covers ev.kv.key)).map evmToEtcd =
        evsUnder pfx (W64 (m : Int)) b cs
  | [], _, _, _ => by unfold evsOfRevM; rfl
  | c :: cs, b, hb, hcr => by
    rw [evsOfRevM_cons m b hb c cs]
    have ih := evsOfRevM_under m rng pfx hcov hm cs (applyChange (W64 (m : Int)) b c)
      (applyChange_sorted hb _ c) (hcr.applyChange _ hm c)
    have hkey : (evOfKv m (chKv (W64 (m : Int)) b c)).kv.key = c.key := by
      unfold evOfKv; split <;> simp [chKv_key]
    have hev : evmToEtcd (evOfKv m (chKv (W64 (m : Int)) b c)) = changeEv (W64 (m : Int)) b c := by
      cases c with
      | del k =>
        unfold evOfKv chKv
        simp [zeroKv, evmToEtcd, changeEv]
      | put k val l =>
        have hne : (putNv (W64 (m : Int)) k val l b).createRev ≠ W64 0 := by
          unfold putNv
          cases hf : b.find? (fun v => decide (v.key = k)) with
          | none => exact hm
          | some old => exact hcr old (List.mem_of_find?_eq_some hf)
        unfold evOfKv chKv
        simp only [hne, ↓reduceIte]
        rfl
    simp only [evsUnder, List.filter_cons, hkey]
    by_cases hp : pfx <+: c.key
    · have hc : rng.covers c.key = true := (hcov _).2 hp
      simp only [hc, ↓reduceIte, hp, List.map_cons, hev, ih, List.singleton_append]
    · have hc : rng.covers c.key = false := by
        cases h : rng.covers c.key
        · rfl
        · exact absurd ((hcov _).1 h) hp
      simp only [hc, Bool.false_eq_true, ↓reduceIte, hp, ih, List.nil_append]

/-- **The watch events of a revision are the client's events of it** (a range covering exactly
the keys under `pfx`; a well-formed log, as mvcc's certificate gives it). -/
theorem watchEvents_rev_eq (log : Log) (hwf : LogWf' log) (hlen : log.length < 2 ^ 63)
    (rng : WatchRange) (pfx : GoString) (hcov : ∀ k, rng.covers k = true ↔ pfx <+: k) (x : Nat) :
    (watchEvents log rng x (x + 1)).map evmToEtcd = revEvs log pfx x := by
  unfold watchEvents revEvs
  rw [logEvents_succ, ← List.getD_eq_getElem?_getD]
  by_cases hx : x = 0
  · subst hx
    have h0 : log.getD 0 [] = [] := by
      rw [List.getD_eq_getElem?_getD]
      cases h : log[0]? with
      | none => rfl
      | some cs =>
        have hne : log ≠ [] := by intro h'; rw [h'] at h; simp at h
        rw [hwf.1 hne] at h; cases h; rfl
    rw [h0]
    unfold evsOfRevM
    rfl
  · rcases Nat.lt_or_ge x log.length with hxl | hxl
    · have hm : W64 ((x : Nat) : Int) ≠ W64 0 := by
        intro h
        have := W64_inj_of_lt (a := x) (b := 0) (by omega) (by omega) h
        omega
      exact evsOfRevM_under x rng pfx hcov hm _ _ (stateAt_sorted _ _)
        (CrPos.stateAt log hwf hlen _)
    · have hn : log.getD x [] = [] := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (l := log) (by omega)]; rfl
      rw [hn]
      unfold evsOfRevM
      rfl

/-! ## Cutting a block of watch events at a revision -/

/-- Every watch event of `[a, b)` is at one of its revisions. -/
theorem watchEvents_mem_rev (log : Log) (rng : WatchRange) (a b : Nat) (ev : EvM)
    (h : ev ∈ watchEvents log rng a b) : ∃ j, a ≤ j ∧ j < b ∧ ev.kv.modRev = W64 (j : Int) := by
  unfold watchEvents at h
  obtain ⟨j, h1, h2, hj⟩ := (mem_logEvents log a b ev).1 (List.mem_filter.1 h).1
  exact ⟨j, h1, h2, evsOfRevM_modRev_sm j _ (stateAt_sorted _ _) _ ev hj⟩

/-- **A block of watch events, cut at the revision `x`** (by the events' mod revisions): the
watch events of `x` alone (revisions below `2 ^ 63`, so that `W64` is injective on them). -/
theorem watchEvents_filter_rev (log : Log) (rng : WatchRange) (a b x : Nat) (hax : a ≤ x)
    (hxb : x < b) (hb : b ≤ 2 ^ 63) :
    (watchEvents log rng a b).filter (fun e => decide (e.kv.modRev = W64 (x : Int))) =
      watchEvents log rng x (x + 1) := by
  rw [watchEvents_append log rng hax (Nat.le_of_lt hxb),
    watchEvents_append log rng (Nat.le_succ x) hxb, List.filter_append, List.filter_append]
  have hoff : ∀ lo hi, (∀ j, lo ≤ j → j < hi → j ≠ x) → hi ≤ b →
      (watchEvents log rng lo hi).filter (fun e => decide (e.kv.modRev = W64 (x : Int))) = [] := by
    intro lo hi hne hhi
    rw [List.filter_eq_nil_iff]
    intro e he
    obtain ⟨j, h1, h2, hj⟩ := watchEvents_mem_rev log rng lo hi e he
    rw [hj]
    simp only [decide_eq_true_eq]
    intro h
    exact hne j h1 h2 (W64_inj_of_lt (by omega) (by omega) h)
  rw [hoff a x (fun j _ h => by omega) (by omega),
    hoff (x + 1) b (fun j h _ => by omega) (Nat.le_refl _)]
  rw [List.filter_eq_self.2]
  · simp
  · intro e he
    obtain ⟨j, h1, h2, hj⟩ := watchEvents_mem_rev log rng x (x + 1) e he
    have : j = x := by omega
    subst this
    simp [hj]

/-- **The events between two consecutive cumulative blocks**: if the events received so far are
`watchEvents log rng lo d0` and, with the next ones `evs`, `watchEvents log rng lo d1`, then
`evs` are the watch events of `[d0, d1)` (or none: then `d1 ≤ d0` may hold). -/
theorem watchEvents_mid (log : Log) (rng : WatchRange) (lo d0 d1 : Nat) (evs : List EvM)
    (h0 : lo ≤ d0) (h : watchEvents log rng lo d0 ++ evs = watchEvents log rng lo d1) :
    evs = [] ∨ (d0 ≤ d1 ∧ evs = watchEvents log rng d0 d1) := by
  rcases Nat.le_total d0 d1 with hle | hle
  · right
    refine ⟨hle, ?_⟩
    rw [watchEvents_append log rng h0 hle] at h
    exact List.append_cancel_left h
  · left
    by_cases hl : lo ≤ d1
    · rw [watchEvents_append log rng hl hle] at h
      have := congrArg List.length h
      simp only [List.length_append] at this
      exact List.eq_nil_of_length_eq_zero (by omega)
    · rw [watchEvents_empty log rng (show d1 ≤ lo by omega)] at h
      exact (List.append_eq_nil_iff.1 h).2

/-! ## The step -/

/-- **`watchStreamSpec_step`** (pure): with no watch event of the range strictly between the
revisions `r0` and `r1`, the client has no event under `pfx` there, and its events of `r1` are
the watch events of `r1` (a range covering exactly the keys under `pfx`, a well-formed log). -/
theorem watchStreamSpec_step (log : Log) (hwf : LogWf' log) (hlen : log.length < 2 ^ 63)
    (rng : WatchRange) (pfx : GoString) (hcov : ∀ k, rng.covers k = true ↔ pfx <+: k)
    (r0 r1 : Nat)
    (hnone : ∀ x : Nat, r0 < x → x < r1 → watchEvents log rng x (x + 1) = []) :
    (∀ x : Nat, (r0 : Int) < x → x < (r1 : Int) → revEvs log pfx x = []) ∧
      revEvs log pfx r1 = (watchEvents log rng r1 (r1 + 1)).map evmToEtcd := by
  refine ⟨fun x h1 h2 => ?_, (watchEvents_rev_eq log hwf hlen rng pfx hcov r1).symm⟩
  rw [← watchEvents_rev_eq log hwf hlen rng pfx hcov x, hnone x (by omega) (by omega)]
  rfl

section model
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- **The server model's step from the watch events**: a certified small log with revision `r1`
(`r0 ≤ r1 < log.length`), no watch event of a range covering exactly the keys under `pfx`
strictly between `r0` and `r1`: `srvStep` of `r1`'s watch events. -/
theorem srvStep_of_watch (E : apply.AEnv GF) (log : Log) (rng : WatchRange) (pfx : GoString)
    (hcov : ∀ k, rng.covers k = true ↔ pfx <+: k) (r0 r1 : Nat) (h01 : r0 ≤ r1)
    (h1 : r1 < log.length)
    (hnone : ∀ x : Nat, r0 < x → x < r1 → watchEvents log rng x (x + 1) = []) :
    srvLog E log ⊢
      srvStep E (W64 (r0 : Int)) (W64 (r1 : Int)) pfx
        ((watchEvents log rng r1 (r1 + 1)).map evmToEtcd) := by
  iintro #Hl
  ihave %Hp : ⌜LogWf' log ∧ log.length < 2 ^ 63⌝ $$ [Hl]
  · unfold srvLog
    icases Hl with ⟨Hc, -⟩
    iapply idxCert_pure $$ Hc
  obtain ⟨hwf, hlen⟩ := Hp
  obtain ⟨hz, hs⟩ := watchStreamSpec_step log hwf hlen rng pfx hcov r0 r1 hnone
  have e0 : sint.Z (W64 (r0 : Int)) = r0 := by word
  have e1 : sint.Z (W64 (r1 : Int)) = r1 := by word
  unfold srvStep
  iexists log
  iframe Hl
  ipureintro
  refine ⟨by omega, by omega, by omega, fun x hx1 hx2 => hz x (by omega) (by omega), ?_⟩
  rw [e1]
  simpa using hs

end model

end v3rpc
end EtcdGrove
end Perennial
