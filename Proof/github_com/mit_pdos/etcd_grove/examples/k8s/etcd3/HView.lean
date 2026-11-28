/-
Lean-first (no Rocq counterpart).

# The indexed history (`hview`, K9 step 3)

- `hviewOwn v hs`: the Go `hview` `v` (`export.go`) is a view of the history holding `hs`: its `h`
  holds `hs` (`histOwn`) and its `sts[i]`, read-only, holds the store at revision `lo + i`
  (`histN hs (lo + i)`). `viewFrom h lo` builds one, `v.at r` reads it, returning what `histAt h r`
  would (`hview__at.lean`: its post is `histAt`'s).
- `histN_prefix`: the last store of a prefix `l ++ [s]` of `hs` is `hs`'s at revision `l.length + 1`
  (a node of the walk back from the newest is at its own revision).
- `wp_max_u64`: the builtin `max` of two `uint64`s (moved here from `target.lean`), and
  `eventsInL`'s lemmas (from `wantEvents.lean`): for the `*Idx` functions too.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.WDefs

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Input Output Obj item mstore mcfg hnode state WEvent change hview)

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

theorem histN_prefix (l hs : List GSt) (s : GSt) (h : l ++ [s] <+: hs) :
    histN hs (l.length + 1) = s := by
  obtain ⟨t, rfl⟩ := h
  unfold histN
  have : (l ++ [s] ++ t).take (l.length + 1) = l ++ [s] := by
    exact List.take_left' (by simp)
  rw [this]; simp

theorem eventsInL_succ_of_lt2 (x : Input) (hs : List GSt) (lo hi : Nat) (h : lo < 2) :
    eventsInL x hs lo hi = eventsInL x hs (lo + 1) hi := by
  unfold eventsInL
  rcases Nat.lt_or_ge lo hi with hl | hl
  · obtain ⟨n, hn⟩ : ∃ n, hi - lo = n + 1 := ⟨hi - lo - 1, by omega⟩
    have hn' : hi - (lo + 1) = n := by omega
    have hev : evAtL x hs lo = none := by simp [evAtL]; omega
    rw [hn, hn', List.range'_succ, List.filterMap_cons, hev]
  · rw [show hi - lo = 0 by omega, show hi - (lo + 1) = 0 by omega]
    rfl

theorem eventsInL_max2 (x : Input) (hs : List GSt) (lo hi : Nat) :
    eventsInL x hs lo hi = eventsInL x hs (max lo 2) hi := by
  rcases Nat.lt_or_ge lo 2 with h | h
  · rw [eventsInL_succ_of_lt2 x hs lo hi h]
    rcases Nat.lt_or_ge (lo + 1) 2 with h2 | h2
    · rw [eventsInL_succ_of_lt2 x hs (lo + 1) hi h2]
      congr 1; omega
    · congr 1; omega
  · congr 1; omega

theorem eventsInL_snoc (x : Input) (hs : List GSt) (s r : Nat) (h : s ≤ r) :
    eventsInL x hs s (r + 1) = eventsInL x hs s r ++ (evAtL x hs r).toList := by
  unfold eventsInL
  rw [show r + 1 - s = (r - s) + 1 by omega, List.range'_concat, List.filterMap_append]
  congr 1
  rw [show s + 1 * (r - s) = r by omega]
  simp only [List.filterMap_cons, List.filterMap_nil]
  cases evAtL x hs r <;> rfl

theorem histAtL_eq_histN (hs : List GSt) (r : w64) : histAtL hs r = histN hs (uint.nat r) := rfl

theorem reliableOkL_eq (x : Input) (req : Nat) (evs : List WEv) (h : HSt) (lo0 hi : Nat)
    (hR : evRangeL evs = some (lo0, hi)) :
    reliableOkL x req evs h =
      if x.Match' = W64 2 ∧ req = 0 then false
      else if uint.nat h.st.rv + 1 < hi then false
      else evsEqL (eventsInL x h.hist (reliableLoL x req lo0) hi) (evs.filter fun e => e.t ≠ 3) := by
  unfold reliableOkL reliableLoL; rw [hR]

theorem range'_any_snoc (f : Nat → Bool) (m r : Nat) (h : m ≤ r) :
    (List.range' m (r + 1 - m)).any f = ((List.range' m (r - m)).any f || f r) := by
  rw [show r + 1 - m = (r - m) + 1 by omega, List.range'_concat, List.any_append]
  simp [show m + (r - m) = r by omega]

theorem range'_any_mono (f : Nat → Bool) (m a b : Nat) (h1 : m ≤ a) (h2 : a ≤ b)
    (h : (List.range' m (a - m)).any f = true) : (List.range' m (b - m)).any f = true := by
  rw [show b - m = (a - m) + (b - a) by omega, ← List.range'_append_1, List.any_append, h]

theorem watchListOkL_some (x : Input) (req : Nat) (evs : List WEv) (h : HSt) (k : Nat) (e : WEv)
    (hfi : evs.findIdx? (fun e => e.t = 3) = some k) (hk : evs[k]? = some e) :
    watchListOkL x req evs h =
      if !e.o.Annotated' then false
      else if (req ≠ 0 ∧ uint.nat e.o.ResourceVersion' < req) ∨ uint.nat e.o.ResourceVersion' < 1 ∨
          uint.nat h.st.rv < uint.nat e.o.ResourceVersion' then false
      else if !evsEqL (initialEventsL x (histN h.hist (uint.nat e.o.ResourceVersion'))) (evs.take k)
        then false
      else reliableOkL x req (evs.drop k) h := by
  unfold watchListOkL
  rw [hfi]
  simp only [List.getD_eq_getElem?_getD, hk, Option.getD_some]

theorem cfgOwn_hist (c : mcfg) (g : GCfg) :
    cfgOwn (GF := GF) c g ⊢ histOwn c.hist' g.st.hist ∗ ⌜g.st.hist.length < 2 ^ 64⌝ := by
  unfold cfgOwn
  iintro ⟨-, #Hh, -, %H⟩
  isplit
  · iexact Hh
  · ipureintro; exact H

theorem watchOkL_eq (x : Input) (y : Output) (h : HSt) (all : List WEv) (reqw : w64)
    (hf : (y.WFailed' || x.Skip') = false) (hd : decWEventsL y.WEvents' = some all)
    (hr : rejectsL all (uint.nat h.st.rv) = false) (hb : bookmarksOkL (keptL all) = true)
    (hp : parseRVD x.MinRV' = some reqw) :
    watchOkL x y h = if x.SendInit' = W64 2 then watchListOkL x (uint.nat reqw) (keptL all) h
      else reliableOkL x (uint.nat reqw) (keptL all) h := by
  unfold rejectsL at hr
  simp only [Bool.or_eq_false_iff] at hr
  unfold watchOkL
  rw [hf, hd]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [hr.1]
  simp only [Bool.false_eq_true, ↓reduceIte]
  unfold keptL at hr hb
  rw [hr.2, hb, hp]
  rfl

theorem watchOkL_false (x : Input) (y : Output) (h : HSt) (all : List WEv)
    (hf : (y.WFailed' || x.Skip') = false) (hd : decWEventsL y.WEvents' = some all)
    (hr : rejectsL all (uint.nat h.st.rv) = true ∨
      (rejectsL all (uint.nat h.st.rv) = false ∧ bookmarksOkL (keptL all) = false) ∨
      (rejectsL all (uint.nat h.st.rv) = false ∧ parseRVD x.MinRV' = none)) :
    watchOkL x y h = false := by
  unfold watchOkL
  rw [hf, hd]
  simp only [Bool.false_eq_true, ↓reduceIte]
  unfold rejectsL keptL at hr
  rcases hr with hr | ⟨hr, hb⟩ | ⟨hr, hp⟩
  · simp only [Bool.or_eq_true] at hr
    cases h1 : all.any (fun e => decide (5 ≤ e.t))
    · rcases hr with hr | hr
      · rw [h1] at hr; cases hr
      · simp only [Bool.false_eq_true, ↓reduceIte]; rw [hr]; rfl
    · rfl
  · simp only [Bool.or_eq_false_iff] at hr
    rw [hr.1]; simp only [Bool.false_eq_true, ↓reduceIte]; rw [hr.2, hb]; rfl
  · simp only [Bool.or_eq_false_iff] at hr
    rw [hr.1]; simp only [Bool.false_eq_true, ↓reduceIte]; rw [hr.2]
    cases hb : bookmarksOkL (List.filter (fun e => decide (e.t ≠ 4)) all)
    · rfl
    · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]; rw [hp]

/-- The Go `hview` `v` is a view of the history holding `hs` (see the file header). -/
def hviewOwn (v : hview) (hs : List GSt) : IProp GF :=
  iprop(histOwn v.h' hs ∗ ∃ ss : List mstore, v.sts' ↦*□ ss ∗
    □ (∀ (i : Nat) (s : mstore), ⌜ss[i]? = some s⌝ -∗ storeOwn s (histN hs (uint.nat v.lo' + i))))

instance hviewOwn_persistent (v : hview) (hs : List GSt) :
    Persistent (hviewOwn (GF := GF) v hs) := by
  unfold hviewOwn; infer_instance

end defs

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- The builtin `max` of two `uint64`s. -/
theorem wp_max_u64 (a b : w64) :
    {{ (True : IProp GF) }}
      (App (App (Val #(functions go.max [go.uint64, go.uint64])) (Val #a)) (Val #b))
    {{ (m : w64), RET #m; ⌜uint.nat m = max (uint.nat a) (uint.nat b)⌝ }} := by
  wp_start
  wp_if_destruct
  all_goals (iapply HΦ; ipureintro; rw [Nat.max_def]; split <;> word)

end proof

end k8s_etcd3
end EtcdGrove
end Perennial
