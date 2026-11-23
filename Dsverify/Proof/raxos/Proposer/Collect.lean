/-
Package `proposer`: ghost helpers of `handleProposeRequest`'s iteration over `n` peers: the peers'
tokens (a reply per peer goroutine), the producers handed back to the closer, the collected
replies' representations.
-/
module

public import Dsverify.Proof.raxos.Proposer.Max
public import Dsverify.Proof.raxos.Proposer.Pure
public import Perennial.Golang.Theory.Chan.Idioms.Mpmc

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.raxos


open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Net
open Perennial.raxos.pure Perennial.raxos.msg
open raxos.replica.src

namespace prop

section collect
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [π : NetProtoGS] [qv : hyp.QpVocab GF]

/-- `m` fresh tokens, one per peer `0..m-1`. -/
theorem tokens_alloc (m : Nat) :
    ⊢@{IProp GF} |==> ∃ ts : Nat → GName, [∗list] j ∈ List.range' 0 m, token (ts j) := by
  induction m with
  | zero =>
    imodintro
    iexists (fun _ => default)
    simp only [List.range'_zero]
    iapply BigSepL.bigSepL_nil.2; iempintro
  | succ m ih =>
    imod ih with ⟨%ts, H⟩
    imod token_alloc with ⟨%g, Hg⟩
    imodintro
    iexists (fun j => if j = m then g else ts j)
    rw [List.range'_concat]
    iapply BigSepL.bigSepL_snoc.2
    isplitl [H]
    · iapply BigSepL.bigSepL_impl $$ H
      imodintro
      iintro %q %j %hj Ht
      have : j < m := by have := List.mem_range'.1 (List.mem_of_getElem? hj); omega
      have hne : j ≠ m := by omega
      simp only [hne, ↓reduceIte]; iexact Ht
    · simp only [Nat.zero_add, Nat.one_mul, ↓reduceIte]
      iexact Hg

/-- The producers' fragments the WaitGroup hands back, as a list. -/
theorem producers_collect (γm : MpmcNames) (m : Nat) :
    ⊢@{IProp GF} ([∗list] _x ∈ List.replicate m (), ∃ s, mpmcProducer γm s) -∗
      ∃ ss : List MSet, ⌜ss.length = m⌝ ∗ [∗list] s ∈ ss, mpmcProducer γm s := by
  induction m with
  | zero =>
    iintro -
    iexists []
    isplitr
    · ipureintro; rfl
    iapply BigSepL.bigSepL_nil.2; iempintro
  | succ m ih =>
    iintro H
    rw [List.replicate_succ]
    icases BigSepL.bigSepL_cons.1 $$ H with ⟨⟨%s, Hs⟩, H⟩
    ihave ⟨%ss, %Hss, Hl⟩ := ih $$ H
    iexists s :: ss
    isplitr
    · ipureintro; simp [Hss]
    iapply BigSepL.bigSepL_cons.2
    iframe

/-- A peer's token is not one of the collected replies'. -/
theorem tok_fresh (ts : Nat → GName) (got : List Got) (g' : Got) :
    ⊢@{IProp GF} ([∗list] g ∈ got, token (ts g.1)) -∗ token (ts g'.1) -∗
      ⌜g'.1 ∉ got.map Prod.fst⌝ ∗ [∗list] g ∈ got ++ [g'], token (ts g.1) := by
  iintro H Ht
  by_cases hm : g'.1 ∈ got.map Prod.fst
  · obtain ⟨g, hg, hgj⟩ := List.mem_map.1 hm
    icases BigSepL.bigSepL_mem_acc (Φ := fun g => token (GF := GF) (ts g.1)) hg $$ H with ⟨Hg, -⟩
    rw [hgj]
    iexfalso
    iapply token_exclusive $$ Hg Ht
  · isplitr
    · ipureintro; exact hm
    iapply BigSepL.bigSepL_snoc.2
    iframe

/-- A collected reply's representation. -/
theorem repliesRep_lookup (xs : List RecorderResponse) (sts : List RecSt) (m : Nat)
    (y : RecorderResponse) (st : RecSt) (hy : xs[m]? = some y) (hst : sts[m]? = some st) :
    ⊢@{IProp GF} repliesRep xs sts -∗ rrVal y st := by
  unfold repliesRep
  iintro ⟨%Hlen, #H⟩
  ihave ⟨%st', %Hst', Hv⟩ := BigSepL.bigSepL_lookup
    (Φ := fun k x => iprop(∃ st, ⌜sts[k]? = some st⌝ ∗ rrVal (GF := GF) x st)) hy $$ H
  rw [hst] at Hst'
  cases Hst'
  iexact Hv

theorem repliesRep_length (xs : List RecorderResponse) (sts : List RecSt) :
    ⊢@{IProp GF} repliesRep xs sts -∗ ⌜xs.length = sts.length⌝ := by
  unfold repliesRep
  iintro ⟨%Hlen, -⟩
  ipureintro; exact Hlen

end collect

end prop

end Perennial.raxos
