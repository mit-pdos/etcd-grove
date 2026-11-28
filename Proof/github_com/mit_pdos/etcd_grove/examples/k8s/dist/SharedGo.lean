/-
Lean-first (no Rocq counterpart).

# k8s-dist K9: the Go search's landings contain K4's

`notes/k8s-dist-k9.md` §2.9. K4's `SearchRun A` lands a pending write only at `landingsFull A [] [] rv`
(`SharedSearch.lean`). Go's `settle` (`examples/k8s/etcd3/export.go`) lands it at `landings(revs, d, w,
b, full, in, out)`, whatever function of the configuration and the write that is (`SettleWith L`). Here:

- `SettleWith L`, `SearchStepWith L`, `SearchRunWith L`: K4's `SettleL`, `SearchStep`, `SearchRun` with
  the landings `L`;
- `SearchRunN A n0`: K4's `SearchRun A` whose every operation starts from a configuration at revision at
  least `n0` (the seeded store's), and `fullCompleteN`: `fullComplete`'s run is one (K4's `CRel`
  keeps `HRel.n0_le`);
- **`searchRunN_with`**: a `SearchRunN A n0` is a `SearchRunWith L` for any `L` that contains, at a
  configuration at revision `rv ≥ n0`, every landing of `landingsFull A [] [] rv` below `2^64`. Go's
  full-mode landings are such an `L` for `A = [0, n0] ++ anchors` (§2.9: the seed's revisions are at most
  `rv`, so they add only `rv + 1`, which Go always has).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.dist.SharedComplete

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_dist

open k8s_etcd3
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Input Output Obj)

section go
variable [GooseExts]

/-- **`settle` with landings `L`** (`L c w`: where the pending write `w` may land from `c`). -/
inductive SettleWith (L : GCfg → Input → List Nat) : GCfg → GCfg → Prop where
  | refl (c : GCfg) : SettleWith L c c
  | drop {c d : GCfg} (i : Nat) : i < c.pend.length →
      (mstepL (pendAt c i) c.st.st).1.rv = c.st.st.rv →
      SettleWith L ⟨c.st, removeAtL c.pend i⟩ d → SettleWith L c d
  | land {c d : GCfg} (i l : Nat) : i < c.pend.length →
      (mstepL (pendAt c i) c.st.st).1.rv ≠ c.st.st.rv →
      l ∈ L c (pendAt c i) →
      SettleWith L ⟨(kstepL (pendAt c i) (skipToL c.st (l - 1))).1, removeAtL c.pend i⟩ d →
      SettleWith L c d

/-- One step of the search with landings `L`. -/
def SearchStepWith (L : GCfg → Input → List Nat) (c : GCfg) (x : Input) (y : Output) (e : GCfg) : Prop :=
  ∃ d, SettleWith L c d ∧ e ∈ stepL ⟨skipToL d.st (targetL x y (uint.nat d.st.st.rv)), d.pend⟩ x y

/-- A run of the search with landings `L`. -/
inductive SearchRunWith (L : GCfg → Input → List Nat) : GCfg → List (Input × Output) → Prop where
  | nil (c : GCfg) : SearchRunWith L c []
  | cons {c e : GCfg} {x : Input} {y : Output} {ops : List (Input × Output)} :
      SearchStepWith L c x y e → SearchRunWith L e ops → SearchRunWith L c ((x, y) :: ops)

/-- **K4's run, each operation from a configuration at revision at least `n0`.** -/
inductive SearchRunN (A : List Nat) (n0 : Nat) : GCfg → List (Input × Output) → Prop where
  | nil (c : GCfg) : SearchRunN A n0 c []
  | cons {c e : GCfg} {x : Input} {y : Output} {ops : List (Input × Output)} :
      n0 ≤ uint.nat c.st.st.rv → SearchStep A c x y e → SearchRunN A n0 e ops →
      SearchRunN A n0 c ((x, y) :: ops)

/-- **`fullComplete`, with the revision floor**: the run it gives starts every operation at or above
the seeded store's revision. (`fullComplete`'s proof, keeping `HRel.n0_le`.) -/
theorem fullCompleteN (h0 : HSt) (A : List Nat) (ops : List (Input × Output)) (c' : GCfg)
    (hlen : h0.hist.length = uint.nat h0.st.rv) (hlast : h0.hist.getLast? = some h0.st)
    (hseed : ∀ g ∈ h0.hist, ∀ it ∈ g.items, uint.nat it.obj'.ResourceVersion' ≤ uint.nat h0.st.rv)
    (hA : AnchorsOk A ops) (hrun : SRun h0 ⟨h0, []⟩ ops c') :
    SearchRunN A (uint.nat h0.st.rv) ⟨h0, []⟩ ops := by
  have hn0 : 1 ≤ uint.nat h0.st.rv := by
    rw [← hlen]
    cases hh : h0.hist with
    | nil => rw [hh] at hlast; cases hlast
    | cons _ _ => simp
  have hinit : CRel A (uint.nat h0.st.rv) ⟨h0, []⟩ ⟨h0, []⟩ :=
    ⟨⟨id, [], HRel.init h0 hlen hlast hseed⟩, List.Perm.refl _, by simp, by simp⟩
  have main : ∀ c ops c', SRun h0 c ops c' → ∀ e, CRel A (uint.nat h0.st.rv) e c →
      (∀ p ∈ ops, OpAnchors A p.1 p.2) → SearchRunN A (uint.nat h0.st.rv) e ops := by
    intro c ops c' hr
    induction hr with
    | nil => intro e _ _; exact .nil _
    | cons hre hnw hps _ ih =>
      intro e hc hops
      have hle : uint.nat h0.st.rv ≤ uint.nat e.st.st.rv := by
        obtain ⟨_, _, h⟩ := hc.rel; exact h.n0_le
      obtain ⟨e', hst, hc'⟩ := hc.op hn0 hre hnw hps (hops _ List.mem_cons_self)
      exact .cons hle hst (ih e' hc' (fun p hp => hops p (List.mem_cons_of_mem _ hp)))
  exact main _ _ _ hrun _ hinit hA.2

/-- A step from below `2^64 - 1` does not lower the revision. -/
theorem kstepL_rv_ge (x : Input) (h : HSt) (hw : uint.nat h.st.rv + 1 < 2 ^ 64) :
    uint.nat h.st.rv ≤ uint.nat (kstepL x h).1.st.rv := by
  unfold kstepL
  split
  · exact Nat.le_refl _
  · unfold advanceL
    split <;> (try dsimp only) <;> rcases mstepL_rv x h.st with e | e <;> rw [e] <;> word

/-- **K4's settle is a settle with any landings containing K4's**, from a configuration at or above
`n0` (a landing raises the revision, so every configuration of the settle stays at or above `n0`). -/
theorem settleL_with {A : List Nat} {n0 : Nat} {L : GCfg → Input → List Nat}
    (hL : ∀ c w l, n0 ≤ uint.nat c.st.st.rv → l ∈ landingsFull A [] [] (uint.nat c.st.st.rv) →
      l < 2 ^ 64 → l ∈ L c w)
    {c d : GCfg} (hs : SettleL A c d) (hn : n0 ≤ uint.nat c.st.st.rv) : SettleWith L c d := by
  induction hs with
  | refl c => exact .refl c
  | drop i hi hsame _ ih => exact .drop i hi hsame (ih hn)
  | @land c d i l hi hch hl hl64 _ ih =>
    refine .land i l hi hch (hL c _ l hn hl hl64) (ih ?_)
    have hgt : uint.nat c.st.st.rv < l := by
      unfold landingsFull at hl
      rcases List.mem_cons.mp hl with e | e
      · omega
      · have := (List.mem_filter.mp e).2; simp at this; omega
    have hsk := skipToL_rv c.st (l - 1) (by omega)
    rw [Nat.max_eq_right (by omega)] at hsk
    have := kstepL_rv_ge (pendAt c i) (skipToL c.st (l - 1)) (by rw [hsk]; omega)
    show n0 ≤ uint.nat (kstepL (pendAt c i) (skipToL c.st (l - 1))).1.st.rv
    omega

/-- **K4's run is a run of the search with any landings containing K4's.** -/
theorem searchRunN_with {A : List Nat} {n0 : Nat} {L : GCfg → Input → List Nat}
    (hL : ∀ c w l, n0 ≤ uint.nat c.st.st.rv → l ∈ landingsFull A [] [] (uint.nat c.st.st.rv) →
      l < 2 ^ 64 → l ∈ L c w)
    {c : GCfg} {ops : List (Input × Output)} (hr : SearchRunN A n0 c ops) : SearchRunWith L c ops := by
  induction hr with
  | nil c => exact .nil c
  | cons hn hst _ ih =>
    obtain ⟨d, hsd, he⟩ := hst
    exact .cons ⟨d, settleL_with hL hsd hn, he⟩ ih

end go

end k8s_dist
end EtcdGrove
end Perennial
