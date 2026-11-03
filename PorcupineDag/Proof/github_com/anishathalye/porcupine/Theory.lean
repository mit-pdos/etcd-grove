/-
Lean-first (no Rocq counterpart).

# Histories and linearizability, in pure terms (2026-11-02, from v1.3.1's `Theory.lean`)

What a history and its linearizability are (`Linearizable`, porcupine's definition: closed
intervals, an operation precedes another iff it returns strictly before the other is called),
copied from v1.3.1's proof (`Proof/github_com/anishathalye/porcupine/Theory.lean`) with the
order a linearization must respect as a parameter `R` of `Completes`/`Good`: PR #46's search
respects, besides real time, each client's listed order (`LinearizableCO`). The search's frames,
their chain of model steps and the abstract cache (`CacheOk`) are v1.3.1's; a frame also records
the candidate list it was lifted from (`DagTheory.lean`). v1.3.1's entry list is gone.
-/
module

@[expose] public section

namespace Perennial
namespace github_com.anishathalye.porcupine
namespace Theory

/-- An operation of a history: what it did (`val`: its input and output) and its interval
(`call`, `ret`: porcupine's `Operation.Call` and `Return`, closed). -/
structure Op (α : Type) where
  val : α
  call : Int
  ret : Int

/-- A deterministic sequential specification (porcupine's `Model`): from a state, an
operation either is allowed and leads to one state, or is not allowed. -/
structure SeqModel (σ α : Type) where
  init : σ
  step : σ → α → Option σ

variable {σ α : Type}

/-- The state after a sequence of operations, if the model allows them. -/
def run (M : SeqModel σ α) : σ → List α → Option σ
  | s, [] => some s
  | s, a :: l =>
    match M.step s a with
    | some s' => run M s' l
    | none => none

/-- Operation `a` of history `h` precedes operation `b` in real time: it returned before `b`
was called (porcupine's intervals are closed). -/
def Prec (h : List (Op α)) (a b : Nat) : Prop :=
  ∃ oa ob, h[a]? = some oa ∧ h[b]? = some ob ∧ oa.ret < ob.call

/-- The operations of `h` at indices `π`, in that order. -/
def vals (h : List (Op α)) (π : List Nat) : List α :=
  π.filterMap fun k => (h[k]?).map Op.val

/-- `π` orders the operations of `h` outside `S` so that the model can run them from `t`, and
respects the order `R` (`R a b`: `a` must come before `b`): no operation of `π` must come
before one earlier in `π`. -/
def Completes (M : SeqModel σ α) (h : List (Op α)) (R : Nat → Nat → Prop) (S : Nat → Prop)
    (t : σ) (π : List Nat) : Prop :=
  π.Nodup ∧ (∀ k, k ∈ π ↔ k < h.length ∧ ¬ S k) ∧ (run M t (vals h π)).isSome ∧
    π.Pairwise fun a b => ¬ R b a

/-- A configuration of the search (the operations `S` linearized, the model's state `t`) has
a completion respecting `R`. -/
def Good (M : SeqModel σ α) (h : List (Op α)) (R : Nat → Nat → Prop) (S : Nat → Prop) (t : σ) :
    Prop :=
  ∃ π, Completes M h R S t π

/-- Porcupine's linearizability: some order of all of `h`'s operations is allowed by the
model from its initial state and respects real time. -/
def Linearizable (M : SeqModel σ α) (h : List (Op α)) : Prop :=
  Good M h (Prec h) (fun _ => False) M.init

/-- Linearizability by an order that also respects `co` (PR #46's client order: an operation
listed before another of the same client comes first). -/
def LinearizableCO (M : SeqModel σ α) (h : List (Op α)) (co : Nat → Nat → Prop) : Prop :=
  Good M h (fun a b => Prec h a b ∨ co a b) (fun _ => False) M.init

/-- Respecting more is respecting less. -/
theorem good_mono {M : SeqModel σ α} {h : List (Op α)} {R R' : Nat → Nat → Prop}
    {S : Nat → Prop} {t : σ} (hRR : ∀ a b, R' a b → R a b) (hg : Good M h R S t) :
    Good M h R' S t := by
  obtain ⟨π, hnd, hmem, hrun, hpw⟩ := hg
  exact ⟨π, hnd, hmem, hrun, hpw.imp fun hn hr => hn (hRR _ _ hr)⟩

theorem linearizable_of_co {M : SeqModel σ α} {h : List (Op α)} {co : Nat → Nat → Prop}
    (hl : LinearizableCO M h co) : Linearizable M h :=
  good_mono (fun _ _ hp => Or.inl hp) hl

theorem good_congr {M : SeqModel σ α} {h : List (Op α)} {R : Nat → Nat → Prop}
    {S S' : Nat → Prop} {t : σ}
    (hS : ∀ i, S i ↔ S' i) (hg : Good M h R S t) : Good M h R S' t := by
  obtain ⟨π, hnd, hmem, hrun, hpw⟩ := hg
  exact ⟨π, hnd, fun k => by rw [hmem k, hS k], hrun, hpw⟩


/-! ## The search's abstract state -/

/-- A frame of the stack: the operation lifted, the state before it (`stackEntry.state`), the
candidate list it was lifted from (`fr`) and its position there (`frontierIdx`: the search
resumes below it). -/
structure Frame (σ : Type) where
  id : Nat
  pre : σ
  pos : Nat
  fr : List Nat

/-- The operations lifted (newest first). -/
def ids (fs : List (Frame σ)) : List Nat := fs.map Frame.id

/-- The frames are steps of the model from its initial state, to `s`. -/
def Chain (M : SeqModel σ α) (h : List (Op α)) : List (Frame σ) → σ → Prop
  | [], s => s = M.init
  | f :: fs, s => Chain M h fs f.pre ∧ ∃ o, h[f.id]? = some o ∧ M.step f.pre o.val = some s

theorem chain_det {M : SeqModel σ α} {h : List (Op α)} :
    ∀ {fs : List (Frame σ)} {s s' : σ}, Chain M h fs s → Chain M h fs s' → s = s'
  | [], _, _, h1, h2 => by simp only [Chain] at h1 h2; rw [h1, h2]
  | f :: fs, _, _, ⟨_, o, ho, hs⟩, ⟨_, o', ho', hs'⟩ => by
    rw [ho] at ho'; cases ho'; rw [hs] at hs'; cases hs'; rfl

/-- Lifting `y` from `(B, t)` leads only to configurations without completion. -/
def SuccBad (M : SeqModel σ α) (h : List (Op α)) (R : Nat → Nat → Prop) (B : List Nat) (t : σ)
    (y : Nat) : Prop :=
  ∀ o t', h[y]? = some o → M.step t o.val = some t' → ¬ Good M h R (· ∈ y :: B) t'

/-- A cached configuration is one of the stack's. -/
def OnStack (M : SeqModel σ α) (h : List (Op α)) (fs : List (Frame σ))
    (c : (Nat → Prop) × σ) : Prop :=
  ∃ fs', fs' <:+ fs ∧ (∀ i, c.1 i ↔ i ∈ ids fs') ∧ Chain M h fs' c.2

/-- Every cached configuration is on the stack or has no completion. -/
def CacheOk (M : SeqModel σ α) (h : List (Op α)) (R : Nat → Nat → Prop) (fs : List (Frame σ))
    (cache : List ((Nat → Prop) × σ)) : Prop :=
  ∀ c ∈ cache, OnStack M h fs c ∨ ¬ Good M h R c.1 c.2

theorem ids_suffix {fs fs' : List (Frame σ)} (hs : fs' <:+ fs) {i : Nat} (hi : i ∈ ids fs') :
    i ∈ ids fs :=
  (hs.map Frame.id).subset hi

end Theory
end github_com.anishathalye.porcupine
end Perennial
