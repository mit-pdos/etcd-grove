/-
Lean-first (no Rocq counterpart).

# The bridge to Kubernetes' checker, B3: the replay is determined by the responses (k8s 7g step 4)

`notes/k8s-7g-scope.md` §2.3, B3. Porcupine's second run over `correctness.Model` may pick another
linearization than the driver's (`kSpec`'s, projected on the unary operations); `NewReplay` then
runs along that one. Two facts make the checks after porcupine independent of the choice:

- **`replayL_perm`** (B3a): two linearizations of the same operations (`List.Perm`) that both
  replay give the same `RReplay`: the same state at every resource version and the same changes.
  Every write that moves the resource version answers its object at the new one (create, a writing
  update, delete); a write that does not (a no-op update, a failed one) leaves the state as it was.
  So the writes that move it come in the order of their responses' resource versions, and the
  state at each is a function of the operations. (Which of two updates with equal answers writes
  and which is the no-op can differ between linearizations; the states and changes cannot.)
- **`simR_step`** (B3b): along the driver's run, the replay's accumulator tracks the driver's
  configuration (`SimR`): its state is the configuration's store (`absR`), its states map holds
  `absR (histAtL hist r)` at every revision `r` from the seeded store's `s0` on, and its changes
  are the history's (`chgListL`). `ReplayAt s0 R h` is what the checks of a read or a watch at a
  configuration `h` use of the final replay `R` (B4, B5).

The premises on the states: `rmWf` (the stored objects' resource versions at most the state's, the
rewrite flags only on stored keys: `absR` of a seeded store satisfies it) and `HistSorted` (the
stores of the history keep their items in strictly increasing key order, as the store does).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.RReplay

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_correctness

open k8s_etcd3 k8sDeep
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Obj Input Output item)

section go
variable [GooseExts]

/-! ## Vocabulary -/

/-- **A well-formed model state**: every stored object's resource version is at most the state's,
and only stored keys carry a rewrite flag (`absR` of a seeded store; kept by every step). -/
def rmWf (m : RM) : Prop :=
  (∀ k o, m.items !! k = some o → uint.nat o.ResourceVersion' ≤ uint.nat m.rv) ∧
  (∀ k, (m.rewrites !! k).isSome → (m.items !! k).isSome)

/-- **The stores of a history keep their items in strictly increasing key order** (the store's
`setItem`; read off `KRelH`). -/
def HistSorted (hs : List GSt) : Prop :=
  ∀ r ≤ hs.length, ((histN hs r).items.map (·.key')).Pairwise go.GoStringLt

/-- **The changes of a history from revision `s0` on**, as the checker's `Change`s: for each
revision `r` in `(s0, |hs|]`, the item that differs between the stores at `r - 1` and `r`
(`changeAtL`), at its store key. -/
def chgListL (s0 : Nat) (hs : List GSt) : List RChange :=
  (List.range' (s0 + 1) (hs.length - s0)).filterMap fun r =>
    (changeAtL (histN hs (r - 1)).items (histN hs r).items r).map fun ch =>
      ⟨storeKeyL ch.key, W64 (r : Int), ch.cur, ch.prev⟩

/-- **The replay `R` agrees with the driver's configuration `h` up to its revision**: the state at
every resource version from `s0` to `h`'s is `h`'s store there, and the changes up to `h`'s
revision are its history's. -/
def ReplayAt (s0 : w64) (R : RReplay) (h : HSt) : Prop :=
  (∀ r : w64, uint.nat s0 ≤ uint.nat r → uint.nat r ≤ uint.nat h.st.rv →
    R.states !! r = some (absR (histAtL h.hist r))) ∧
  R.changes.filter (fun c => decide (uint.nat c.rv ≤ uint.nat h.st.rv)) =
    chgListL (uint.nat s0) h.hist

/-- **The replay's accumulator (state, states map, changes) tracks the configuration `h`**: the
state is `h`'s store, the states map is defined exactly from `s0` to `h`'s revision, every change
is at most `h`'s revision, and `ReplayAt`. -/
def SimR (s0 : w64) (acc : RM × GMap w64 RM × List RChange) (h : HSt) : Prop :=
  acc.1 = absR h.st ∧
  (∀ r : w64, (acc.2.1 !! r).isSome ↔ (uint.nat s0 ≤ uint.nat r ∧ uint.nat r ≤ uint.nat h.st.rv)) ∧
  (∀ c ∈ acc.2.2, uint.nat c.rv ≤ uint.nat h.st.rv) ∧
  ReplayAt s0 ⟨acc.2.1, acc.2.2⟩ h

/-! ## B3a: any two linearizations that replay give the same replay -/

/-- **B3a.** Two orders `l1`, `l2` of the same operations from a well-formed state, both accepted
by `NewReplay` (every `Step` true), give the same states and changes. The bound keeps the
resource versions from wrapping. -/
theorem replayL_perm (init : RM) (l1 l2 : List (Input × RResp)) (R1 R2 : RReplay)
    (hwf : rmWf init) (hn : uint.nat init.rv + l1.length < 2 ^ 64) (hp : l1.Perm l2)
    (h1 : replayL init l1 = some R1) (h2 : replayL init l2 = some R2) : R1 = R2 := by
  sorry

/-! ## B3b: along the driver's run, the replay is the driver's history -/

/-- **B3b, the start**: before any operation, the accumulator of `NewReplay` from the seeded
store's model tracks the seeded configuration. -/
theorem simR_init (h0 : HSt) (hlen : h0.hist.length = uint.nat h0.st.rv)
    (hlast : h0.hist.getLast? = some h0.st) :
    SimR h0.st.rv (absR h0.st, {[h0.st.rv := absR h0.st]}, []) h0 := by
  sorry

/-- **B3b, one step**: a unary operation the driver's model takes from `h` to `h'` (`kstepL`), whose
`Step` on the replay's state is accepted and lands on `h'`'s store (B1), keeps the accumulator
tracking the configuration. -/
theorem simR_step (s0 : w64) (acc : RM × GMap w64 RM × List RChange) (h : HSt)
    (x : Input) (resp : RResp) (acc' : RM × GMap w64 RM × List RChange)
    (hsim : SimR s0 acc h)
    (hlen : h.hist.length = uint.nat h.st.rv) (hlast : h.hist.getLast? = some h.st)
    (hsort : HistSorted (kstepL x h).1.hist)
    (hlen' : (kstepL x h).1.hist.length = uint.nat (kstepL x h).1.st.rv)
    (hrv : uint.nat (kstepL x h).1.st.rv < 2 ^ 63)
    (hstep : replayStepL (some acc) (x, resp) = some acc')
    (habs : acc'.1 = absR (kstepL x h).1.st) :
    SimR s0 acc' (kstepL x h).1 := by
  sorry

/-- **B3b, earlier configurations**: the final replay agrees with every configuration whose
history is a prefix of the final one's. -/
theorem replayAt_prefix (s0 : w64) (R : RReplay) (h hF : HSt)
    (hR : ReplayAt s0 R hF) (hpre : h.hist <+: hF.hist)
    (hlen : h.hist.length = uint.nat h.st.rv) (hlenF : hF.hist.length = uint.nat hF.st.rv) :
    ReplayAt s0 R h := by
  sorry

end go

end k8s_correctness
end EtcdGrove
end Perennial
