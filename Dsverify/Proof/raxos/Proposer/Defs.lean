/-
Package `proposer`'s internal predicates: a proposal value and its model value, decided slots
in a request, a recorder reply, and their persistence.
-/
module

public import Dsverify.Proof.raxos.Wire
public import Dsverify.Proof.raxos.Proposer.Strings

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.raxos


open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Net
open Perennial.raxos.pure Perennial.raxos.msg
open raxos.replica.src

namespace prop

theorem rep_set_step {A : Type} (a z : A) (n m : Nat) (h : n < m) :
    (List.replicate n a ++ List.replicate (m - n) z).set n a =
      List.replicate (n + 1) a ++ List.replicate (m - (n + 1)) z := by
  apply List.ext_getElem
  · simp; omega
  · intro i h1 h2
    simp only [List.getElem_set, List.getElem_append, List.getElem_replicate, List.length_replicate]
    by_cases hi : i = n
    · subst hi; simp
    · by_cases hi2 : i < n
      · simp [hi2, Ne.symm hi, show i < n + 1 by omega]
      · simp [hi2, Ne.symm hi, show ¬ i < n + 1 by omega]


/-- The configuration's replica count as a Go `int`. -/
theorem conf_n_sint (c : QConf) (hc : c.ok) :
    sint.Z (W64 c.n) = c.n ∧ 3 ≤ c.n ∧ c.n ≤ 5 := by
  rcases hc.1 with h | h <;> rw [h] <;> exact ⟨rfl, by omega, by omega⟩

/-- A majority of the configuration's replicas (`numReplicas/2+1`) as a Go `int`. -/
theorem conf_maj_sint (c : QConf) (hc : c.ok) :
    BitVec.sdiv (W64 c.n) (W64 2) + W64 1 = W64 ((c.n / 2 + 1 : Nat) : Int) ∧
      sint.Z (W64 ((c.n / 2 + 1 : Nat) : Int)) = ((c.n / 2 + 1 : Nat) : Int) ∧
      c.n / 2 + 1 < c.n := by
  rcases hc.1 with h | h <;> rw [h] <;> exact ⟨by decide, rfl, by omega⟩

theorem sint_of_nat (a : w64) (n : Nat) (h : n = sint.nat a) (h0 : 0 ≤ sint.Z a) :
    sint.Z a = n := by
  subst h; show sint.Z a = ((sint.Z a).toNat : Int); omega

theorem w64_of_sint (a : w64) (m : Nat) (hm : m < 2 ^ 62) (h : sint.Z a = m) : a = W64 m := by
  word

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [π : NetProtoGS] [qv : hyp.QpVocab GF]

include sem in
theorem dec_true {P : Prop} [Decidable P] (h : (#(decide P) : val) = #true) : P := by
  rw [intoVal_eq_iff] at h; simpa using h

include sem in
theorem dec_false {P : Prop} [Decidable P] (h : (#(decide P) : val) = #false) : ¬ P := by
  rw [intoVal_eq_iff] at h; simpa using h

include sem in
theorem dec_not_true {P : Prop} [Decidable P] (h : ¬ (#(decide P) : val) = #true) : ¬ P := by
  rw [intoVal_eq_iff] at h; simpa using h

include sem in
theorem dec_not_false {P : Prop} [Decidable P] (h : ¬ (#(decide P) : val) = #false) : P := by
  rw [intoVal_eq_iff] at h; simpa using h

/-- A `ProposerMessage_Proposal` value `x` holds the model value `v`: its tag, its ids
(persistent) and its client batches (persistent, registered). -/
def propRep (γ : QNames) (x : ProposerMessage_Proposal) (v : pure.Val) : IProp GF :=
  iprop(∃ (bps : List Loc) (bs : List Batch),
    ⌜sint.Z x.Priority' = v.prio ∧ sint.Z x.ProposerId' = v.pid ∧ sint.Z x.ThreadId' = v.tid⌝ ∗
    x.Ids' ↦*□ v.ids ∗ x.ClientBatches' ↦*□ bps ∗ repList repPMBatch bps .discard bs ∗
    ([∗list] b ∈ bs, batchReg γ b.id b) ∗ ⌜∀ b ∈ bs, batchFit b⌝)

/-- Decided slots `ds` in a slice of `*ProposerMessage_DecidedSlot` (persistent). -/
def dsRep (γ : QNames) (sl : GoSlice) (ds : List DSlot) : IProp GF :=
  iprop(∃ sps : List Loc, sl ↦*□ sps ∗ repList repPMSlot sps .discard ds ∗
    [∗list] d ∈ ds, decided γ d.index d.ids)

/-- A recorder's proposal at `l` (persistent). -/
def rpRep (l : Loc) (v : pure.Val) : IProp GF :=
  iprop(∃ x : RecorderResponse_Proposal, l ↦□ x ∗
    ⌜sint.Z x.Priority' = v.prio ∧ sint.Z x.ProposerId' = v.pid ∧ sint.Z x.ThreadId' = v.tid⌝ ∗
    x.Ids' ↦*□ v.ids)

/-- A `RecorderResponse` value holding the slot state `st` (persistent). -/
def rrVal (x : RecorderResponse) (st : RecSt) : IProp GF :=
  iprop(⌜sint.Z x.S' = st.S⌝ ∗ rpRep x.F' st.F ∗ rpRep x.M' st.M)

theorem repList_nil {A : Type} (rep : Loc → DFrac → A → IProp GF) (dq : DFrac) :
    ⊢ repList rep [] dq ([] : List A) := by
  unfold repList
  isplitr
  · ipureintro; rfl
  iapply BigSepL.bigSepL_nil.2; iempintro

theorem repList_snoc {A : Type} (rep : Loc → DFrac → A → IProp GF) (dq : DFrac)
    (ps : List Loc) (xs : List A) (p : Loc) (x : A) :
    ⊢ repList rep ps dq xs -∗ rep p dq x -∗ repList rep (ps ++ [p]) dq (xs ++ [x]) := by
  unfold repList
  iintro ⟨%Hlen, H⟩ Hx
  isplitr
  · ipureintro; simp [Hlen]
  iapply BigSepL.bigSepL_snoc.2
  isplitl [H]
  · iapply BigSepL.bigSepL_impl $$ H
    imodintro
    iintro %k %q %Hk ⟨%y, %Hy, H⟩
    iexists y
    iframe H
    ipureintro
    have : k < xs.length := by
      rw [← Hlen]; exact (List.getElem?_eq_some_iff.1 Hk).1
    rw [List.getElem?_append_left this]; exact Hy
  · iexists x
    iframe Hx
    ipureintro
    simp [Hlen]

theorem repList_lookup {A : Type} (rep : Loc → DFrac → A → IProp GF) (dq : DFrac)
    (ps : List Loc) (xs : List A) (k : Nat) (p : Loc) (hk : ps[k]? = some p)
    [∀ l a, Persistent (rep l dq a)] :
    ⊢ repList rep ps dq xs -∗ ∃ x, ⌜xs[k]? = some x⌝ ∗ rep p dq x := by
  unfold repList
  iintro ⟨%Hlen, H⟩
  iapply BigSepL.bigSepL_lookup (Φ := fun i p => iprop(∃ x, ⌜xs[i]? = some x⌝ ∗ rep p dq x)) hk $$ H

theorem repList_length {A : Type} (rep : Loc → DFrac → A → IProp GF) (dq : DFrac)
    (ps : List Loc) (xs : List A) :
    ⊢ repList rep ps dq xs -∗ ⌜ps.length = xs.length⌝ := by
  unfold repList
  iintro ⟨%Hlen, -⟩
  ipureintro; exact Hlen

instance decided_persistent (γ : QNames) (i : Int) (ids : List GoString) :
    Persistent (decided (GF := GF) γ i ids) := by
  unfold decided; infer_instance

instance repPMSingle_persistent (l : Loc) (m : GoString) :
    Persistent (repPMSingle (GF := GF) l .discard m) := by
  unfold repPMSingle; infer_instance

instance repList_persistent {A : Type} (rep : Loc → DFrac → A → IProp GF) (ps : List Loc)
    (xs : List A) [h : ∀ l a, Persistent (rep l .discard a)] :
    Persistent (repList rep ps .discard xs) := by
  unfold repList; infer_instance

instance repPMBatch_persistent (l : Loc) (b : Batch) :
    Persistent (repPMBatch (GF := GF) l .discard b) := by
  unfold repPMBatch; infer_instance

instance repPMSlot_persistent (l : Loc) (d : DSlot) :
    Persistent (repPMSlot (GF := GF) l .discard d) := by
  unfold repPMSlot; infer_instance

instance repProp_persistent (l : Loc) (p : Prop') :
    Persistent (repProp (GF := GF) l .discard p) := by
  unfold repProp; infer_instance

instance repDecSlot_persistent (l : Loc) (d : DSlot) :
    Persistent (repDecSlot (GF := GF) l .discard d) := by
  unfold repDecSlot; infer_instance

instance repDRSingle_persistent (l : Loc) (m : GoString) :
    Persistent (repDRSingle (GF := GF) l .discard m) := by
  unfold repDRSingle; infer_instance

instance repDRBatch_persistent (l : Loc) (b : Batch) :
    Persistent (repDRBatch (GF := GF) l .discard b) := by
  unfold repDRBatch; infer_instance

instance repDResp_persistent (l : Loc) (bs : List Batch) :
    Persistent (repDResp (GF := GF) l .discard bs) := by
  unfold repDResp; infer_instance

instance propRep_persistent (γ : QNames) (x : ProposerMessage_Proposal) (v : pure.Val) :
    Persistent (propRep (GF := GF) γ x v) := by
  unfold propRep; infer_instance

instance dsRep_persistent (γ : QNames) (sl : GoSlice) (ds : List DSlot) :
    Persistent (dsRep (GF := GF) γ sl ds) := by
  unfold dsRep; infer_instance

instance rpRep_persistent (l : Loc) (v : pure.Val) : Persistent (rpRep (GF := GF) l v) := by
  unfold rpRep; infer_instance

instance rrVal_persistent (x : RecorderResponse) (st : RecSt) :
    Persistent (rrVal (GF := GF) x st) := by
  unfold rrVal; infer_instance

instance repCSingle_persistent (l : Loc) (m : GoString) :
    Persistent (repCSingle (GF := GF) l .discard m) := by
  unfold repCSingle; infer_instance

instance repCBVal_persistent (x : raxos.proto.client.ClientBatch) (b : Batch) :
    Persistent (repCBVal (GF := GF) x .discard b) := by
  unfold repCBVal; infer_instance

instance batchesP_persistent (γ : QNames) (vs : List raxos.proto.client.ClientBatch)
    (bs : List Batch) : Persistent (batchesP (GF := GF) γ vs bs) := by
  unfold batchesP; infer_instance

instance decidedSlotsP_persistent (γ : QNames) (a b c : GoSlice) :
    Persistent (decidedSlotsP (GF := GF) γ a b c) := by
  unfold decidedSlotsP; infer_instance

instance decisionP_persistent (γ : QNames) (v : Decision) :
    Persistent (decisionP (GF := GF) γ v) := by
  unfold decisionP; infer_instance

instance fetchReqP_persistent (v : FetchRequest) :
    Persistent (fetchReqP (GF := GF) v) := by
  unfold fetchReqP; infer_instance

instance fetchRespP_persistent (γ : QNames) (v : FetchResposne) :
    Persistent (fetchRespP (GF := GF) γ v) := by
  unfold fetchRespP; infer_instance

instance proposeReqP_persistent (γ : QNames) (me : Int) (v : ProposeRequest) :
    Persistent (proposeReqP (GF := GF) γ me v) := by
  unfold proposeReqP; infer_instance

instance peersP_persistent (γ : QNames) (n : Nat) (sl : GoSlice) :
    Persistent (peersP (GF := GF) γ n sl) := by
  unfold peersP; infer_instance

end defs

end prop

end Perennial.raxos
