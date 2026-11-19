/-
Lean-first (no Rocq counterpart).

# Where a watch starts: `WatchFromL` from the store's stream (k8s 7g step 5, scope R3)

B5's premise `WatchFromL s0 x ws` (`RealWatch.lean`): the events after a watch-list's initial ones
(from its first bookmark), or all of any other watch's, mark revisions after the seeded revision
`s0`. Read off the store's guarantee (`kStreamOk` from the start point `st`, `kStartOk`) as
`streamOkL_of_kStreamOk` reads it, given `s0 ≤ st` (which the caller has from `kStartOk`: the
requested revision, at least `s0` by the floor, or a state the watch's read update fired at, past
the seeds).

- `tailOk_lo`: the events of a driver tail from the cursor `c` mark revisions after `c`;
- **`watchFromL_of_kStreamOk`**;
- `run_inv`: a property of the store that every step keeps holds of every configuration the
  pending model reaches (for `s0 ≤ st`: the configurations' histories only grow, `WatchQ.lean`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.KWatchBridge
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.RealWatch

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open k8s k8s_correctness
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Input Output Obj item)

section go
variable [GooseExts]

/-- **The events of a driver tail from the cursor `c` mark revisions after `c`** (`evLo`). -/
theorem tailOk_lo {x : Input} {hs : List GSt} (hwf : HistWf x hs) {c : Nat} {L : List WEv}
    (ht : TailOk x hs c L) : ∀ e ∈ L, c < evLo e := by
  induction ht with
  | nil c => intro e he; cases he
  | ev c r e rest hcr _ _ he _ ih =>
    intro e' he'
    rcases List.mem_cons.1 he' with rfl | he'
    · have h1 := (hwf.2.2 r e' he).1
      have h2 := evAtL_t he
      unfold evLo
      rw [if_neg (by omega)]
      omega
    · have := ih e' he'; omega
  | bm c p o rest hcp _ ho _ _ ih =>
    intro e' he'
    rcases List.mem_cons.1 he' with rfl | he'
    · unfold evLo
      simp only [↓reduceIte]
      omega
    · have := ih e' he'; omega

/-- A watch-list's initial events are Added events. -/
theorem kInitialL_t {Obj : Type} (dec : Dec Obj) (sel : Obj → Bool) (inS : GoString → Bool)
    (s : KVStore) : ∀ e ∈ kInitialL dec sel inS s, e.t = 0 := by
  intro e he
  unfold kInitialL at he
  obtain ⟨v, -, hv⟩ := List.mem_filterMap.1 he
  obtain ⟨o, -, ho⟩ := Option.bind_eq_some_iff.1 hv
  split at ho
  · cases ho; rfl
  · cases ho

theorem dropWhile_ne3_of_t0 (L : List WEv) (h : ∀ e ∈ L, e.t = 0) :
    L.dropWhile (fun e => e.t ≠ 3) = [] := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    have ha := h a (by simp)
    rw [List.dropWhile_cons_of_pos (by simp [ha])]
    exact ih (fun e he => h e (by simp [he]))

theorem dropWhile_ne3_append (L : List WEv) (b : WEv) (R : List WEv) (h : ∀ e ∈ L, e.t = 0)
    (hb : b.t = 3) : (L ++ b :: R).dropWhile (fun e => e.t ≠ 3) = b :: R := by
  induction L with
  | nil =>
    rw [List.nil_append, List.dropWhile_cons_of_neg (by simp [hb])]
  | cons a L ih =>
    have ha := h a (by simp)
    rw [List.cons_append, List.dropWhile_cons_of_pos (by simp [ha])]
    exact ih (fun e he => h e (by simp [he]))

/-- **`WatchFromL` from the store's stream** (see the file header). -/
theorem watchFromL_of_kStreamOk (s0 : w64) (x : Input) (h : HSt) (σ σ0 : KVState) (k : GoString)
    (reqw : w64) (m : KWatchMode) (sel : DObj → Bool) (emp : Bool) (z : DObj) (st : Nat)
    (evs : List (KWEv DObj)) (ws : List WEv)
    (hrel : KRelH h σ) (hlen : h.hist.length = σ.rev) (hw : KHistW σ)
    (hk : prepareKeyM go!"/objs" x.WKey' x.Recursive' = some k) (hlk : go!"/objs/" <+: x.WKey')
    (hsel : ∀ o, sel o = selD x o) (hemp : emp = true → ∀ o, sel o = true)
    (hm : kModeOk x (uint.nat reqw) m) (h0 : 1 ≤ σ0.rev) (hstart : kStartOk m σ0 st)
    (hs : kStreamOk driverCodec.dec sel emp z (kInScope (go!"/registry" ++ k) x.Recursive') m σ st
      evs)
    (hws : List.Forall₂ kWEvRel evs ws) (hst : uint.nat s0 ≤ st) :
    WatchFromL s0 x ws := by
  obtain ⟨_, hstle, full, htail, hpre⟩ := hs
  have hne := nonErr_rel hws
  have hwf := histWf_of_krel x h σ k hrel hlen hw hk hlk
  obtain ⟨_, hwl, hnwl⟩ := hm
  unfold WatchFromL
  by_cases hsi : x.SendInit' = W64 2
  · rw [if_pos hsi]
    obtain ⟨hfi, hbm⟩ := hwl hsi
    unfold kStartOk at hstart
    rw [if_pos hfi] at hstart
    obtain ⟨hst0, _⟩ := hstart
    have hst1 : 1 ≤ st := by omega
    unfold kIdealL at hpre
    rw [if_pos hfi, if_pos hbm] at hpre
    have hT := tailOk_of_kTail x h σ k sel emp z hrel hlen hw hk hlk hsel hemp htail hst1
    have hI0 := kInitialL_t driverCodec.dec sel (kInScope (go!"/registry" ++ k) x.Recursive')
      (σ.at st)
    rw [hne]
    rw [List.singleton_append] at hpre
    rcases prefix_append_cons hpre with hp | ⟨F', hF, hpF⟩
    · rw [dropWhile_ne3_of_t0 _ (fun e he => by
        obtain ⟨e', he', rfl⟩ := List.mem_map.1 he
        exact hI0 e' (hp.subset he'))]
      intro e he; cases he
    · rw [hF, List.map_append, List.map_cons,
        dropWhile_ne3_append _ _ _ (fun e he => by
          obtain ⟨e', he', rfl⟩ := List.mem_map.1 he
          exact hI0 e' he') rfl]
      intro e he
      rcases List.mem_cons.1 he with rfl | he
      · show uint.nat s0 < evLo (kToWEv ⟨3, z, st, true⟩)
        unfold evLo kToWEv
        simp only [↓reduceIte]
        have : uint.nat (W64 (st : Int)) = st :=
          W64_nat_lt st (by have := hrel.1; have := hstle hfi; omega)
        rw [this]
        omega
      · have := tailOk_lo hwf (tailOk_prefix hT _ (hpF.map _)) e he
        omega
  · rw [if_neg hsi]
    have hfi := hnwl hsi
    unfold kStartOk at hstart
    rw [if_neg (by simp [hfi])] at hstart
    unfold kIdealL at hpre
    rw [if_neg (by simp [hfi])] at hpre
    have hst1 : 1 ≤ st := by
      split at hstart <;> omega
    have hT := tailOk_of_kTail x h σ k sel emp z hrel hlen hw hk hlk hsel hemp htail hst1
    rw [hne]
    intro e he
    have := tailOk_lo hwf (tailOk_prefix hT _ (hpre.map _)) e he
    omega

/-! ## Invariants of the pending model's configurations -/

theorem pReach_inv {St I O : Type} [DecidableEq I] {P : linkv.PendSpec St I O} (Inv : St → Prop)
    (hstep : ∀ i s, Inv s → Inv (P.step i s).1) {c c' : linkv.PCfg St I}
    (h : linkv.PReach P c c') (hc : Inv c.st) : Inv c'.st := by
  induction h with
  | refl => exact hc
  | step hs _ ih =>
    apply ih
    cases hs with
    | apply i _ => exact hstep i _ hc
    | perm p _ => exact hc

theorem pStep_inv {St I O : Type} [DecidableEq I] {P : linkv.PendSpec St I O} (Inv : St → Prop)
    (hstep : ∀ i s, Inv s → Inv (P.step i s).1) {c c1 : linkv.PCfg St I} {i : I}
    {o : linkv.Ans O} (h : linkv.PStep P c i o c1) (hc : Inv c.st) : Inv c1.st := by
  cases h with
  | ok => exact hstep i c.st hc
  | errW => exact hc
  | errR => exact hc
  | obs => exact hc

/-- **A property of the store that every step keeps** holds of every configuration a run of the
pending model reaches. -/
theorem run_inv {St I O α : Type} [DecidableEq I] (P : linkv.PendSpec St I O)
    (dec : α → Option (I × linkv.Ans O)) (Inv : St → Prop)
    (hstep : ∀ i s, Inv s → Inv (P.step i s).1) :
    ∀ (l : List α) (S S' : linkv.PSet St I), (∀ c, S c → Inv c.st) →
      github_com.anishathalye.porcupine.Theory.run (linkv.pM P dec) S l = some S' →
      ∀ c, S' c → Inv c.st := by
  intro l
  induction l with
  | nil =>
    intro S S' hS h
    simp only [github_com.anishathalye.porcupine.Theory.run] at h
    cases h; exact hS
  | cons a l ih =>
    intro S S' hS h
    simp only [github_com.anishathalye.porcupine.Theory.run] at h
    split at h
    · rename_i S1 hS1
      refine ih S1 S' (fun c hc => ?_) h
      simp only [linkv.pM] at hS1
      obtain ⟨⟨i, o⟩, -, hst⟩ := Option.bind_eq_some_iff.1 hS1
      rw [linkv.pSeq_step_some hst] at hc
      obtain ⟨c0, c2, c1, h0, hr0, hs, hr1⟩ := hc
      exact pReach_inv Inv hstep hr1 (pStep_inv Inv hstep hs (pReach_inv Inv hstep hr0 (hS c0 h0)))
    · cases h

end go

end k8s_etcd3
end EtcdGrove
end Perennial
