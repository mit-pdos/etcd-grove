/-
The executor's view of the representation: `ownRep`'s instances with the `Index`/`Lowlink` of
the instances the current search visited (`ownInstT`), the row pointers fixed by a map `P`
(`repInstsX`: the executor never writes `InstanceSpace`, so a pointer read once is the slot's
pointer for the whole pass), and a bookkeeping whose held proposals are replied up to a point
(`ownLbF`, the per-command loop).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.epaxos.EpBase
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.epaxos.ExecModel

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net github_com.imdea_software.swiftpaxos_epaxos.kvs
open model epaxosProof BigSepL

attribute [local instance] GooseGlobalGS.gooseInvGS

variable [GooseExts]

section heap
variable [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [go.Semantics]
variable [epaxos.Assumptions] [HasExt netExt] [π : NetProtoGS]
variable [state.Assumptions] [github_com.emirpasic.gods.maps.treemap.Assumptions] [TH : TreemapHyp GF]

/-- `ownLb` with a per-proposal `executed` flag (the per-command loop replies to proposal `k`
at command `k`). -/
def ownLbF (γ : EpNames) (i : Nat) (f : Nat → Bool) (lbp : Loc) (lb : LbRec) :
    IProp GF :=
  iprop(∃ (y : epaxos.LeaderBookkeeping) (gs prs : List Loc),
    lbp ↦ y ∗
    ⌜y.ballot' = lb.ballot ∧ y.allEqual' = lb.allEqual ∧ y.preAcceptOKs' = lb.preAcceptOKs ∧
      y.acceptOKs' = lb.acceptOKs ∧ y.nacks' = lb.nacks ∧ y.preparing' = lb.preparing ∧
      y.tryingToPreAccept' = lb.tryingToPreAccept ∧ y.lastTriedBallot' = lb.lastTriedBallot ∧
      y.status' = lb.status ∧ y.seq' = lb.seq ∧ y.leaderResponded' = lb.leaderResponded ∧
      y.preAcceptsSent' = lb.preAcceptsSent⌝ ∗
    (match lb.clientProposals with
      | none => iprop(⌜y.clientProposals' = slice.nil⌝)
      | some ps => iprop(⌜y.clientProposals' ≠ slice.nil ∧ gs.length = ps.length⌝ ∗
          y.clientProposals' ↦*□ gs ∗
          [∗list] k ↦ g ∈ gs, propHeld γ i (f k) g (ps.getD k default))) ∗
    cmdsRep y.cmds' lb.cmds ∗
    (if lbDepsOwned lb then iprop(y.deps' ↦* lb.deps)
      else iprop(∃ dq : DFrac, y.deps' ↦*{dq} lb.deps)) ∗
    (y.prepareReplies' ↦* prs ∗ ownSliceCap Loc y.prepareReplies' (DFrac.own 1)) ∗ ⌜prs.length = lb.prepareReplies.length⌝ ∗
    [∗list] k ↦ l ∈ prs, ownPReply l (lb.prepareReplies.getD k default))

theorem ownLb_F (γ : EpNames) (i : Nat) (b : Bool) (lbp : Loc) (lb : LbRec) :
    ownLb (GF := GF) γ i b lbp lb = ownLbF γ i (fun _ => b) lbp lb := rfl

/-- `Index`/`Lowlink` as the search has them: `none`, not visited in this pass (`Index = 0`
unless executed); `some (a, b)`, visited with `Index = a`, `Lowlink = b`. -/
def ixOk (y : epaxos.Instance) (w : InstRec) : Option (Nat × Nat) → Prop
  | none => w.status ≠ stEXECUTED → y.Index' = W64 0
  | some (a, b) => y.Index' = W64 a ∧ y.Lowlink' = W64 b

/-- `ownInst` with the search's `Index`/`Lowlink` and per-proposal flags. -/
def ownInstG (γ : EpNames) (i : Nat) (x : InstId) (p : Loc) (w : InstRec)
    (il : Option (Nat × Nat)) (f : Nat → Bool) : IProp GF :=
  iprop(∃ y : epaxos.Instance,
    p ↦ y ∗
    ⌜y.bal' = w.bal ∧ y.vbal' = w.vbal ∧ y.Status' = w.status ∧ y.Seq' = w.seq ∧ ixOk y w il⌝ ∗
    y.id' ↦□ epaxos.instanceId.mk (W32 x.q) (W32 x.i) ∗
    cmdsRep y.Cmds' w.cmds ∗
    (∃ dq : DFrac, y.Deps' ↦*{dq} w.deps) ∗
    (match w.lb with
      | none => iprop(⌜y.lb' = null⌝)
      | some lb => iprop(⌜y.lb' ≠ null⌝ ∗ ownLbF γ i f y.lb' lb)))

def ownInstT (γ : EpNames) (i : Nat) (x : InstId) (p : Loc) (w : InstRec)
    (il : Option (Nat × Nat)) : IProp GF :=
  ownInstG γ i x p w il (fun _ => decide (w.status = stEXECUTED))

theorem ownInst_T (γ : EpNames) (i : Nat) (x : InstId) (p : Loc) (w : InstRec) :
    ownInst (GF := GF) γ i x p w = ownInstT γ i x p w none := rfl

/-- An executed instance forgets its search state. -/
theorem ownInstT_forget (γ : EpNames) (i : Nat) (x : InstId) (p : Loc) (w : InstRec)
    (il : Option (Nat × Nat)) (h : w.status = stEXECUTED) :
    ownInstT (GF := GF) γ i x p w il ⊢ ownInstT γ i x p w none := by
  unfold ownInstT ownInstG
  iintro ⟨%y, Hp, %Hy, Hrest⟩
  iexists y; iframe Hp Hrest
  ipureintro
  exact ⟨Hy.1, Hy.2.1, Hy.2.2.1, Hy.2.2.2.1, fun hn => absurd h hn⟩

/-- Slot `x`'s image: `nil` for no instance. -/
def slotT (γ : EpNames) (i : Nat) (x : InstId) (p : Loc) :
    Option InstRec → Option (Nat × Nat) → IProp GF
  | none, _ => iprop(⌜p = null⌝)
  | some w, il => ownInstT γ i x p w il

/-- The pointer of slot `x` under the rows' pointer lists `F`. -/
def ptrOf (F : Nat → List Loc) (x : InstId) : Loc := (F x.q).getD x.i null

theorem ptrOf_get (F : Nat → List Loc) (x : InstId) (hF : (F x.q).length = MAX_INSTANCE)
    (h : x.i < MAX_INSTANCE) : (F x.q)[x.i]? = some (ptrOf F x) := by
  unfold ptrOf List.getD
  rw [List.getElem?_eq_getElem (by rw [hF]; exact h)]; rfl

/-- `InstanceSpace`'s rows with pointer lists `F`, slot `x` holding `inst x` with search state
`ix x`. -/
def repInstsX (γ : EpNames) (i : Nat) (r : Loc) (F : Nat → List Loc)
    (inst : InstId → Option InstRec) (ix : InstId → Option (Nat × Nat)) : IProp GF :=
  iprop(∃ (iss : GoSlice) (rows : List GoSlice),
    efld r go!"InstanceSpace" ↦□ iss ∗ iss ↦*□ rows ∗ ⌜rows.length = nR⌝ ∗
    [∗list] q ↦ row ∈ rows, row ↦* F q ∗ ⌜(F q).length = MAX_INSTANCE⌝ ∗
      [∗list] n ↦ p ∈ F q, slotT γ i ⟨q, n⟩ p (inst ⟨q, n⟩) (ix ⟨q, n⟩))

/-! ## From and to `repInsts` -/

theorem bigSepL_exists_funX {A B : Type} [Inhabited B] :
    ∀ {Φ : Nat → A → B → IProp GF} (l : List A), ([∗list] k ↦ a ∈ l, ∃ b, Φ k a b) ⊢
      ∃ F : Nat → B, [∗list] k ↦ a ∈ l, Φ k a (F k)
  | _, [] => by
    iintro -
    iexists (fun _ => default)
    iapply bigSepL_nil.2
    iempintro
  | Φ, a :: l => by
    refine (bigSepL_cons).1.trans ?_
    iintro ⟨⟨%b, H0⟩, Hl⟩
    ihave ⟨%F, Hl⟩ := bigSepL_exists_funX (Φ := fun k a b => Φ (k+1) a b) l $$ Hl
    iexists (fun k => if k = 0 then b else F (k - 1))
    iapply bigSepL_cons.2
    have e : (fun k x => Φ (k + 1) x (if k + 1 = 0 then b else F (k + 1 - 1))) =
        (fun k x => Φ (k + 1) x (F k)) := by funext k x; simp
    rw [e]
    iframe

theorem ownRowI_slot (γ : EpNames) (i q : Nat) (row : GoSlice)
    (inst : InstId → Option InstRec) :
    ownRowI (GF := GF) γ i q row inst ⊣⊢ ∃ ptrs : List Loc, row ↦* ptrs ∗ ⌜ptrs.length = MAX_INSTANCE⌝ ∗
      [∗list] n ↦ p ∈ ptrs, slotT γ i ⟨q, n⟩ p (inst ⟨q, n⟩) none := by
  unfold ownRowI
  constructor
  · iintro ⟨%ptrs, Hr, %Hl, Hps⟩
    iexists ptrs; iframe Hr
    isplitr
    · ipureintro; exact Hl
    iapply (bigSepL_mono ?_) $$ Hps
    intro n p _
    rcases inst ⟨q, n⟩ with _ | w <;> exact .rfl
  · iintro ⟨%ptrs, Hr, %Hl, Hps⟩
    iexists ptrs; iframe Hr
    isplitr
    · ipureintro; exact Hl
    iapply (bigSepL_mono ?_) $$ Hps
    intro n p _
    rcases inst ⟨q, n⟩ with _ | w <;> exact .rfl

/-- The executor's view of `repInsts` (no instance visited). -/
theorem repInsts_toX (γ : EpNames) (i : Nat) (r : Loc) (inst : InstId → Option InstRec) :
    repInsts (GF := GF) γ i r inst ⊢ ∃ F, repInstsX γ i r F inst (fun _ => none) := by
  unfold repInsts
  iintro ⟨%iss, %rows, #Hiss, #Hrows, %Hlen, Hrs⟩
  ihave Hrs : ([∗list] q ↦ row ∈ rows, ∃ ptrs : List Loc, row ↦* ptrs ∗
      ⌜ptrs.length = MAX_INSTANCE⌝ ∗ [∗list] n ↦ p ∈ ptrs, slotT γ i ⟨q, n⟩ p (inst ⟨q, n⟩) none)
      $$ [Hrs]
  · iapply (bigSepL_mono ?_) $$ Hrs
    intro k row _
    exact (ownRowI_slot γ i k row inst).1
  ihave ⟨%F, Hrs⟩ := bigSepL_exists_funX (B := List Loc) (Φ := fun q row ptrs =>
      iprop(row ↦* ptrs ∗ ⌜ptrs.length = MAX_INSTANCE⌝ ∗ [∗list] n ↦ p ∈ ptrs,
        slotT γ i ⟨q, n⟩ p (inst ⟨q, n⟩) none)) rows $$ Hrs
  iexists F
  unfold repInstsX
  iexists iss, rows
  iframe Hiss Hrows
  isplitr
  · ipureintro; exact Hlen
  iexact Hrs

theorem slotT_forget (γ : EpNames) (i : Nat) (x : InstId) (p : Loc) (o : Option InstRec)
    (il : Option (Nat × Nat)) (h : il ≠ none → ∃ w, o = some w ∧ w.status = stEXECUTED) :
    slotT (GF := GF) γ i x p o il ⊢ slotT γ i x p o none := by
  rcases o with _ | w
  · exact .rfl
  · rcases il with _ | a
    · exact .rfl
    · obtain ⟨w', hw', hs⟩ := h (by simp)
      cases hw'
      exact ownInstT_forget γ i x p w _ hs

/-- Back to `repInsts` once every visited instance is executed. -/
theorem repInstsX_toRep (γ : EpNames) (i : Nat) (r : Loc) (F : Nat → List Loc)
    (inst : InstId → Option InstRec) (ix : InstId → Option (Nat × Nat))
    (h : ∀ x, ix x ≠ none → ∃ w, inst x = some w ∧ w.status = stEXECUTED) :
    repInstsX (GF := GF) γ i r F inst ix ⊢ repInsts γ i r inst := by
  unfold repInstsX repInsts
  iintro ⟨%iss, %rows, #Hiss, #Hrows, %Hlen, Hrs⟩
  iexists iss, rows
  iframe Hiss Hrows
  isplitr
  · ipureintro; exact Hlen
  iapply (bigSepL_mono ?_) $$ Hrs
  intro k row _
  iintro ⟨Hrow, %Hl, Hps⟩
  iapply (ownRowI_slot γ i k row inst).2
  iexists F k
  isplitl [Hrow]
  · iexact Hrow
  isplitr
  · ipureintro; exact Hl
  iapply (bigSepL_mono ?_) $$ Hps
  intro n p _
  exact slotT_forget γ i ⟨k, n⟩ p _ _ (h ⟨k, n⟩)

/-- Open slot `x` (its row's pointers too); close it with any image and search state. -/
theorem repInstsX_acc (γ : EpNames) (i : Nat) (r : Loc) (F : Nat → List Loc)
    (inst : InstId → Option InstRec) (ix : InstId → Option (Nat × Nat))
    (x : InstId) (hq : x.q < nR) (hn : x.i < MAX_INSTANCE) :
    repInstsX (GF := GF) γ i r F inst ix ⊢ ∃ (iss : GoSlice) (rows : List GoSlice) (row : GoSlice),
      efld r go!"InstanceSpace" ↦□ iss ∗ iss ↦*□ rows ∗ ⌜rows[x.q]? = some row⌝ ∗
      row ↦* F x.q ∗ ⌜(F x.q)[x.i]? = some (ptrOf F x)⌝ ∗
      slotT γ i x (ptrOf F x) (inst x) (ix x) ∗
      (∀ (o : Option InstRec) (il : Option (Nat × Nat)), row ↦* F x.q -∗
        slotT γ i x (ptrOf F x) o il -∗ repInstsX γ i r F (upd inst x o) (upd ix x il)) := by
  obtain ⟨q, n⟩ := x
  dsimp only at hq hn ⊢
  unfold repInstsX
  iintro ⟨%iss, %rows, #Hiss, #Hrows, %Hlen, Hrs⟩
  obtain ⟨row, Hrow⟩ : ∃ row, rows[q]? = some row :=
    ⟨rows[q]'(by omega), List.getElem?_eq_getElem (by omega)⟩
  icases bigSepL_set_acc' Hrow $$ Hrs with ⟨⟨Hr, %Hl, Hps⟩, Hclose⟩
  have Hp : (F q)[n]? = some (ptrOf F ⟨q, n⟩) := ptrOf_get F ⟨q, n⟩ Hl hn
  icases bigSepL_set_acc' Hp $$ Hps with ⟨Hx, Hpclose⟩
  iexists iss, rows, row
  iframe Hiss Hrows
  isplitr
  · ipureintro; exact Hrow
  isplitl [Hr]
  · iexact Hr
  isplitr
  · ipureintro; exact Hp
  isplitl [Hx]
  · iexact Hx
  iintro %o %il Hr Hx
  ihave Hps := Hpclose $$ %(fun k z => slotT γ i ⟨q, k⟩ z (upd inst ⟨q, n⟩ o ⟨q, k⟩)
      (upd ix ⟨q, n⟩ il ⟨q, k⟩)) %(ptrOf F ⟨q, n⟩) [] [Hx]
  · ipureintro
    intro k hk
    funext z
    simp only [upd, InstId.mk.injEq, true_and, hk, if_false]
  · simp only [upd, if_true]; iexact Hx
  have hset : (F q).set n (ptrOf F ⟨q, n⟩) = F q := by
    have := List.getElem?_eq_some_iff.mp Hp
    rw [← this.2]; exact List.set_getElem_self this.1
  rw [hset]
  ihave Hrs := Hclose $$ %(fun q' row => iprop(row ↦* F q' ∗ ⌜(F q').length = MAX_INSTANCE⌝ ∗
      [∗list] n' ↦ p ∈ F q', slotT γ i ⟨q', n'⟩ p (upd inst ⟨q, n⟩ o ⟨q', n'⟩)
        (upd ix ⟨q, n⟩ il ⟨q', n'⟩))) %row [] [Hr Hps]
  · ipureintro
    intro k hk
    funext row'
    congr 1; congr 1; congr 1
    funext k' z
    simp only [upd, InstId.mk.injEq, hk, _root_.false_and, if_false]
  · isplitl [Hr]
    · iexact Hr
    isplitr
    · ipureintro; exact Hl
    iexact Hps
  iexists iss, rows
  iframe Hiss Hrows
  isplitr
  · ipureintro; exact Hlen
  have hset' : rows.set q row = rows := by
    have := List.getElem?_eq_some_iff.mp Hrow
    rw [← this.2]; exact List.set_getElem_self this.1
  rw [hset']
  iexact Hrs

end heap
