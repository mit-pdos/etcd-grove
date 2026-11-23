/-
The handlers' shared notions (package-internal): the run loop's persistent context `hdCtx`, the
lock-invariant shape a handler ends in (`repDone`), the pure facts the handler specs take
(`RepWf`, `OutsWf`), and the rows of `InstanceSpace` with an arbitrary per-slot predicate
(`repInstsP`), which lets a handler hold a slot opened while a callee reads the other slots
(`updateAttributes` reads `InstanceSpace[q][d].Seq`, possibly of the opened slot itself).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.epaxos.EpBase

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net github_com.imdea_software.swiftpaxos_epaxos.kvs
open model epaxosProof

attribute [local instance] GooseGlobalGS.gooseInvGS

/-! ## Pure facts -/

/-- What the handler specs take of the replica's state (the run loop has them: `Inv.wf`'s ids,
`ep_peerOrder`'s order, fixed before the run loop handles anything). -/
structure RepWf (i : Nat) (σ : RState) (ord : List w32) : Prop where
  id : σ.id = i
  hi : i < nR
  po : σ.peerOrder = ord.map (fun x => sint.nat x)

/-- Every message an output list sends or broadcasts is encodable (`SendMsg`'s `m.wf`; from the
model: commands' values shorter than `2^16`, see `notes/prove-handlers.md`). -/
def OutsWf (outs : List Out) : Prop :=
  ∀ o ∈ outs, match o with
    | .send _ m => m.wf
    | .bcast b => b.m.wf
    | _ => True

/-- The conflicts map and the per-row last SCAN / last PUT point to existing instances (`Inv.wf`,
`InvAux.classWf`): `updateAttributes` dereferences `InstanceSpace[q][d]` (stage 2, review
T1-2). -/
def ConfWf (σ : RState) : Prop :=
  (∀ q k pr, σ.conflicts q k = some pr → q < nR ∧
    (0 ≤ zz pr.last → σ.inst ⟨q, toN pr.last⟩ ≠ none) ∧
    (0 ≤ zz pr.lastWrite → σ.inst ⟨q, toN pr.lastWrite⟩ ≠ none)) ∧
  (∀ q < nR, (0 ≤ zz (σ.lastScan q) → σ.inst ⟨q, toN (σ.lastScan q)⟩ ≠ none) ∧
    (0 ≤ zz (σ.lastPut q) → σ.inst ⟨q, toN (σ.lastPut q)⟩ ≠ none) ∧
    -1 ≤ zz (σ.lastScan q) ∧ -1 ≤ zz (σ.lastPut q))

/-- `ConfWf` after one slot is set (the maps and the row arrays unchanged). -/
theorem confWf_upd (σ : RState) (x : InstId) (w : InstRec) (h : ConfWf σ) (σ' : RState)
    (hc : σ'.conflicts = σ.conflicts) (hi : σ'.inst = upd σ.inst x (some w))
    (hs : σ'.lastScan = σ.lastScan) (hp : σ'.lastPut = σ.lastPut) : ConfWf σ' := by
  refine ⟨fun q k pr hk => ?_, fun q hq => ?_⟩
  · rw [hc] at hk
    obtain ⟨h1, h2, h3⟩ := h.1 q k pr hk
    refine ⟨h1, fun hz => ?_, fun hz => ?_⟩
    · rw [hi]; unfold upd; split
      · simp
      · exact h2 hz
    · rw [hi]; unfold upd; split
      · simp
      · exact h3 hz
  · obtain ⟨h1, h2, h3, h4⟩ := h.2 q hq
    rw [hs, hp]
    refine ⟨fun hz => ?_, fun hz => ?_, h3, h4⟩
    · rw [hi]; unfold upd; split
      · simp
      · exact h1 hz
    · rw [hi]; unfold upd; split
      · simp
      · exact h2 hz

/-- An output list with no send and no broadcast (ghost events, re-proposals, replies). -/
def NoSends (outs : List Out) : Prop :=
  ∀ o ∈ outs, (∀ t m, o ≠ .send t m) ∧ ∀ b, o ≠ .bcast b

theorem sendsTo_noSends (outs : List Out) (h : NoSends outs) (to : Nat) : sendsTo outs to = [] := by
  unfold sendsTo
  rw [List.filterMap_eq_nil_iff]
  intro o ho
  rcases o with ⟨t, m⟩ | b | _ | _ | _
  · exact absurd rfl ((h _ ho).1 t m)
  · exact absurd rfl ((h _ ho).2 b)
  all_goals rfl

theorem pendOf_noSends (outs : List Out) (h : NoSends outs) : pendOf outs = none := by
  unfold pendOf
  suffices ∀ acc, (∀ o ∈ outs, (∀ t m, o ≠ .send t m) ∧ ∀ b, o ≠ .bcast b) →
      outs.foldl (fun acc o => match o with | .bcast b => b.norm | _ => acc) acc = acc from
    this none h
  clear h
  induction outs with
  | nil => intro acc _; rfl
  | cons o os ih =>
    intro acc h'
    simp only [List.foldl_cons]
    rcases o with ⟨t, m⟩ | b | _ | _ | _
    · exact absurd rfl ((h' _ List.mem_cons_self).1 t m)
    · exact absurd rfl ((h' _ List.mem_cons_self).2 b)
    all_goals exact ih _ (fun o ho => h' o (List.mem_cons_of_mem _ ho))

@[simp] theorem bumpRecvBallot_inst (σ : RState) (b : w32) :
    (bumpRecvBallot σ b).inst = σ.inst := by unfold bumpRecvBallot; split <;> rfl
@[simp] theorem bumpRecvBallot_crt (σ : RState) (b : w32) :
    (bumpRecvBallot σ b).crtInstance = σ.crtInstance := by unfold bumpRecvBallot; split <;> rfl
@[simp] theorem bumpRecvBallot_cut (σ : RState) (b : w32) :
    (bumpRecvBallot σ b).committedUpTo = σ.committedUpTo := by unfold bumpRecvBallot; split <;> rfl
@[simp] theorem bumpRecvBallot_eut (σ : RState) (b : w32) :
    (bumpRecvBallot σ b).execedUpTo = σ.execedUpTo := by unfold bumpRecvBallot; split <;> rfl
@[simp] theorem bumpRecvBallot_conf (σ : RState) (b : w32) :
    (bumpRecvBallot σ b).conflicts = σ.conflicts := by unfold bumpRecvBallot; split <;> rfl
@[simp] theorem bumpRecvBallot_msk (σ : RState) (b : w32) :
    (bumpRecvBallot σ b).maxSeqPerKey = σ.maxSeqPerKey := by unfold bumpRecvBallot; split <;> rfl
@[simp] theorem bumpRecvBallot_maxSeq (σ : RState) (b : w32) :
    (bumpRecvBallot σ b).maxSeq = σ.maxSeq := by unfold bumpRecvBallot; split <;> rfl
@[simp] theorem bumpRecvBallot_leader (σ : RState) (b : w32) :
    (bumpRecvBallot σ b).isLeader = σ.isLeader := by unfold bumpRecvBallot; split <;> rfl
@[simp] theorem bumpRecvBallot_store (σ : RState) (b : w32) :
    (bumpRecvBallot σ b).store = σ.store := by unfold bumpRecvBallot; split <;> rfl
@[simp] theorem bumpRecvBallot_po (σ : RState) (b : w32) :
    (bumpRecvBallot σ b).peerOrder = σ.peerOrder := by unfold bumpRecvBallot; split <;> rfl
@[simp] theorem bumpRecvBallot_id (σ : RState) (b : w32) :
    (bumpRecvBallot σ b).id = σ.id := by unfold bumpRecvBallot; split <;> rfl
@[simp] theorem bumpRecvBallot_lastScan (σ : RState) (b : w32) :
    (bumpRecvBallot σ b).lastScan = σ.lastScan := by unfold bumpRecvBallot; split <;> rfl
@[simp] theorem bumpRecvBallot_lastPut (σ : RState) (b : w32) :
    (bumpRecvBallot σ b).lastPut = σ.lastPut := by unfold bumpRecvBallot; split <;> rfl

/-- `P` at `x`, `Q` elsewhere unchanged. -/
def updP {α : Type} (P : InstId → α) (x : InstId) (a : α) : InstId → α :=
  fun y => if y = x then a else P y

section heap
variable [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [go.Semantics]
variable [epaxos.Assumptions] [HasExt netExt] [π : NetProtoGS]
variable [state.Assumptions] [github_com.emirpasic.gods.maps.treemap.Assumptions] [TH : TreemapHyp GF]

/-! ## The context -/

/-- What a handler reads and never writes (persistent): the packages' initialization, the
framework handle (`SendMsg`, `alive`, `r.M`), the protocol's read-only fields, the protocol
invariant (the broadcasts' ghost steps), and `PreferredPeerOrder` (`ord`). -/
def hdCtx (γ : EpNames) (i : Nat) (r rr : Loc) (L : List GoString) (p : FwPtrs)
    (Rext : IProp GF) (ord : List w32) : IProp GF :=
  iprop(pkgInit_epaxos ∗ pkgInit_replica ∗ efld r go!"Replica" ↦□ rr ∗
    isReplicaFw γ rr i L p Rext ∗ epROFields r ∗ inv protoN (epInv γ) ∗ prefOrder rr i L ord)

instance hdCtx_persistent (γ : EpNames) (i : Nat) (r rr : Loc) (L : List GoString) (p : FwPtrs)
    (Rext : IProp GF) (ord : List w32) : Persistent (hdCtx γ i r rr L p Rext ord) := by
  unfold hdCtx epROFields prefOrder; infer_instance

theorem hdCtx_ord (γ : EpNames) (i : Nat) (r rr : Loc) (L : List GoString) (p : FwPtrs)
    (Rext : IProp GF) (ord : List w32) :
    hdCtx γ i r rr L p Rext ord ⊢ ⌜∀ o ∈ ord, 0 ≤ sint.Z o⌝ := by
  unfold hdCtx prefOrder
  iintro ⟨-, -, -, -, -, -, %po, -, -, %H⟩
  ipureintro; exact H.2.2

/-- Replica `i`'s outboxes, all empty. -/
def outboxesNil (γ : EpNames) (i : Nat) : IProp GF :=
  iprop([∗list] to ∈ List.range nR, outboxFrag γ i to [])

/-- What a handler leaves (the instance lock's invariant's first part): some state, in the heap
and the ghost fragment, idle. -/
def repDone (γ : EpNames) (i : Nat) (r : Loc) : IProp GF :=
  iprop(∃ σ : RState, ownRep γ i r σ ∗ repFrag γ i σ ∗ repIdle γ i)

/-- The outputs of a handler that sends nothing leave the replica idle. -/
theorem outsOk_idle (γ : EpNames) (i : Nat) (outs : List Out) (h : NoSends outs) :
    outsOk (GF := GF) γ i outs ⊢ repIdle γ i := by
  unfold outsOk repIdle
  iintro ⟨Hob, Hp, Hc, -⟩
  rw [pendOf_noSends _ h]
  iframe Hp Hc
  have e : (fun _ to => outboxFrag (GF := GF) γ i to (sendsTo outs to)) =
      (fun (_ : Nat) to => outboxFrag γ i to []) := by
    funext _ to; rw [sendsTo_noSends _ h]
  simp only [e]
  iexact Hob

/-- A leading ghost event changes no resource of the outputs. -/
theorem outsOk_cons_ev (γ : EpNames) (i : Nat) (e : Event) (outs : List Out) :
    outsOk (GF := GF) γ i (Out.ev e :: outs) ⊢ outsOk γ i outs := by
  unfold outsOk
  have h1 : ∀ to, sendsTo (Out.ev e :: outs) to = sendsTo outs to := fun to => rfl
  have h2 : pendOf (Out.ev e :: outs) = pendOf outs := rfl
  simp only [h1, h2]
  iintro ⟨Hob, Hp, Hc, -, Hl⟩
  iframe

theorem outsWf_tail (o : Out) (outs : List Out) (h : OutsWf (o :: outs)) : OutsWf outs :=
  fun x hx => h x (List.mem_cons_of_mem _ hx)

/-- A handler's outputs whose only send is its last broadcast `b`: the outboxes are empty, the
pending broadcast is `b.norm`. -/
theorem outsOk_bcast (γ : EpNames) (i : Nat) (evs : List Out) (b : Bcast) (h : NoSends evs) :
    outsOk (GF := GF) γ i (evs ++ [.bcast b]) ⊢ outboxesNil γ i ∗ pendFrag γ i b.norm ∗ curFrag γ i [] 0 := by
  unfold outsOk outboxesNil
  iintro ⟨Hob, Hp, Hc, -⟩
  have hp : pendOf (evs ++ [.bcast b]) = b.norm := by
    unfold pendOf; rw [List.foldl_append]; rfl
  rw [hp]
  iframe Hp Hc
  have e : (fun _ to => outboxFrag (GF := GF) γ i to (sendsTo (evs ++ [.bcast b]) to)) =
      (fun (_ : Nat) to => outboxFrag γ i to []) := by
    funext _ to
    have := sendsTo_noSends _ h to
    unfold sendsTo at this ⊢
    rw [List.filterMap_append, this]; rfl
  simp only [e]
  iexact Hob

/-! ## `InstanceSpace` with a per-slot predicate -/

/-- The rows of `InstanceSpace`, slot `x` with pointer `p` described by `P x p`. -/
def repInstsP (r : Loc) (P : InstId → Loc → IProp GF) : IProp GF :=
  iprop(∃ (iss : GoSlice) (rows : List GoSlice),
    efld r go!"InstanceSpace" ↦□ iss ∗ iss ↦*□ rows ∗ ⌜rows.length = nR⌝ ∗
    [∗list] q ↦ row ∈ rows, ∃ ptrs : List Loc, row ↦* ptrs ∗ ⌜ptrs.length = MAX_INSTANCE⌝ ∗
      [∗list] n ↦ pt ∈ ptrs, P ⟨q, n⟩ pt)

/-- The representation's rows are the per-slot rows with `instAt`. -/
theorem repInsts_P (γ : EpNames) (i : Nat) (r : Loc) (inst : InstId → Option InstRec) :
    repInsts (GF := GF) γ i r inst ⊣⊢ repInstsP r (fun x pt => instAt γ i x pt (inst x)) := by
  unfold repInsts repInstsP ownRowI
  have e : ∀ (q : Nat) (pt : Loc) (n : Nat), (match inst ⟨q, n⟩ with
      | none => iprop(⌜pt = null⌝)
      | some w => ownInst (GF := GF) γ i ⟨q, n⟩ pt w) = instAt γ i ⟨q, n⟩ pt (inst ⟨q, n⟩) := by
    intro q pt n; unfold instAt; rcases inst ⟨q, n⟩ <;> rfl
  simp only [e]
  exact .rfl

/-- Open slot `x`: its row's pointers, its pointer and predicate; close it with a new pointer
and a new predicate for the slot. -/
theorem repInstsP_acc (r : Loc) (P : InstId → Loc → IProp GF) (x : InstId)
    (hq : x.q < nR) (hn : x.i < MAX_INSTANCE) :
    repInstsP r P ⊢ ∃ (iss : GoSlice) (rows : List GoSlice) (row : GoSlice)
        (ptrs : List Loc) (pt : Loc),
      efld r go!"InstanceSpace" ↦□ iss ∗ iss ↦*□ rows ∗ ⌜rows[x.q]? = some row⌝ ∗
      row ↦* ptrs ∗ ⌜ptrs[x.i]? = some pt ∧ ptrs.length = MAX_INSTANCE⌝ ∗ P x pt ∗
      (∀ (pt' : Loc) (Q : Loc → IProp GF), row ↦* ptrs.set x.i pt' -∗ Q pt' -∗
        repInstsP r (updP P x Q)) := by
  obtain ⟨q, n⟩ := x
  dsimp only at hq hn ⊢
  unfold repInstsP
  iintro ⟨%iss, %rows, #Hiss, #Hrows, %Hlen, Hrs⟩
  obtain ⟨row, Hrow⟩ : ∃ row, rows[q]? = some row :=
    ⟨rows[q]'(by omega), List.getElem?_eq_getElem (by omega)⟩
  icases bigSepL_set_acc' Hrow $$ Hrs with ⟨Hr, Hclose⟩
  icases Hr with ⟨%ptrs, Hptrs, %Hplen, Hps⟩
  obtain ⟨pt, Hp⟩ : ∃ pt, ptrs[n]? = some pt :=
    ⟨ptrs[n]'(by omega), List.getElem?_eq_getElem (by omega)⟩
  icases bigSepL_set_acc' Hp $$ Hps with ⟨Hx, Hpclose⟩
  iexists iss, rows, row, ptrs, pt
  iframe Hiss Hrows Hptrs Hx
  isplitr
  · ipureintro; exact Hrow
  isplitr
  · ipureintro; exact ⟨Hp, Hplen⟩
  iintro %pt' %Q Hptrs HQ
  ihave Hps := Hpclose $$ %(fun k z => updP P ⟨q, n⟩ Q ⟨q, k⟩ z) %pt' [] [HQ]
  · ipureintro
    intro k hk
    funext z
    simp only [updP, InstId.mk.injEq, true_and, hk, if_false]
  · simp only [updP, if_true]; iexact HQ
  ihave Hrs := Hclose $$ %(fun q' row => iprop(∃ ptrs : List Loc, row ↦* ptrs ∗
      ⌜ptrs.length = MAX_INSTANCE⌝ ∗ [∗list] k ↦ pt ∈ ptrs, updP P ⟨q, n⟩ Q ⟨q', k⟩ pt)) %row []
      [Hptrs Hps]
  · ipureintro
    intro k hk
    funext row'
    congr 1; funext ptrs'; congr 1; congr 1; congr 1
    funext k' z
    simp only [updP, InstId.mk.injEq, hk, _root_.false_and, if_false]
  · iexists ptrs.set n pt'
    iframe Hptrs
    isplitr
    · ipureintro; simp [Hplen]
    iexact Hps
  iexists iss, rows
  iframe Hiss Hrows
  isplitr
  · ipureintro; exact Hlen
  have hset : rows.set q row = rows := by
    have := List.getElem?_eq_some_iff.mp Hrow
    rw [← this.2]; exact List.set_getElem_self this.1
  rw [hset]
  iexact Hrs

/-- A slot whose instance's `Seq` can be read (`updateAttributes`'s `InstanceSpace[q][d].Seq`)
and given back. -/
def SeqReadable (inst : InstId → Option InstRec) (P : InstId → Loc → IProp GF) : Prop :=
  ∀ x pt w, inst x = some w → P x pt ⊢
    ∃ y : epaxos.Instance, pt ↦ y ∗ ⌜y.Seq' = w.seq⌝ ∗ (pt ↦ y -∗ P x pt)

/-- The slot predicate of the representation. -/
abbrev instAtP (γ : EpNames) (i : Nat) (inst : InstId → Option InstRec) :
    InstId → Loc → IProp GF :=
  fun x pt => instAt γ i x pt (inst x)

theorem instAtP_seq (γ : EpNames) (i : Nat) (inst : InstId → Option InstRec) :
    SeqReadable inst (instAtP (GF := GF) γ i inst) := by
  intro x pt w hw
  simp only [instAtP, hw]
  unfold instAt ownInst
  iintro ⟨%y, Hy, %Hyf, Hrest⟩
  iexists y
  iframe Hy
  isplitr
  · ipureintro; exact Hyf.2.2.2.1
  iintro Hy
  iexists y
  iframe Hy Hrest
  ipureintro; exact Hyf

/-- A slot about to be overwritten: only its instance's `Seq` is kept (`startPhase1` reads it
through `updateAttributes`, then stores a new instance there). -/
def slotSeq (o : Option InstRec) (pt : Loc) : IProp GF :=
  match o with
  | none => iprop(⌜pt = null⌝)
  | some w => iprop(∃ y : epaxos.Instance, pt ↦ y ∗ ⌜y.Seq' = w.seq⌝)

theorem updP_seq (γ : EpNames) (i : Nat) (inst : InstId → Option InstRec) (x : InstId) :
    SeqReadable inst (updP (instAtP (GF := GF) γ i inst) x (slotSeq (inst x))) := by
  intro y pt w hw
  unfold updP
  by_cases hy : y = x
  · subst hy
    simp only [if_true, slotSeq, hw]
    iintro ⟨%z, Hz, %Hzs⟩
    iexists z
    iframe Hz
    isplitr
    · ipureintro; exact Hzs
    iintro Hz
    iexists z
    iframe Hz
    ipureintro; exact Hzs
  · simp only [hy, if_false]
    exact instAtP_seq γ i inst y pt w hw

/-- The pieces of `ownRep` other than the instances and the two bounds. -/
def ownRepRest (i : Nat) (r : Loc) (σ : RState) : IProp GF :=
  iprop(repRowArr r go!"crtInstance" σ.crtInstance ∗
    repRowArr r go!"CommittedUpTo" σ.committedUpTo ∗
    repRowArr r go!"ExecedUpTo" σ.execedUpTo ∗
    repConf r σ.conflicts ∗ repMsk r σ.maxSeqPerKey ∗
    efld r go!"maxSeq" ↦ σ.maxSeq ∗ efld r go!"IsLeader" ↦ σ.isLeader ∗
    efld r go!"maxRecvBallot" ↦ σ.maxRecvBallot ∗
    repStore r σ.store ∗ repPeer r i σ.peerOrder ∗
    repRowArr r go!"lastScan" σ.lastScan ∗ repRowArr r go!"lastPut" σ.lastPut)

/-- `lastScan`/`lastPut` together (a proof that unfolds `repRowArr` for another row array keeps
these two folded, as `updateConflicts`/`updateAttributes`' specs take them). -/
def clsArrs (r : Loc) (ls lp : Nat → w32) : IProp GF :=
  iprop(repRowArr r go!"lastScan" ls ∗ repRowArr r go!"lastPut" lp)

/-- `ownRep` with slot `x` about to be overwritten (`slotSeq`). -/
def ownRepHole (γ : EpNames) (i : Nat) (r : Loc) (σ : RState) (x : InstId) : IProp GF :=
  iprop(⌜instBounds σ.inst⌝ ∗ ⌜cutBounds σ.committedUpTo⌝ ∗
    repInstsP r (updP (instAtP γ i σ.inst) x (slotSeq (σ.inst x))) ∗ ownRepRest i r σ)

/-- The proposals slice `prs` handed to a new bookkeeping, with its held proposals (a new
instance is not executed). -/
def propsOwn (γ : EpNames) (i : Nat) (prs : GoSlice) : Option (List Proposal) → IProp GF
  | none => iprop(⌜prs = slice.nil⌝)
  | some ps => iprop(∃ gs : List Loc, ⌜prs ≠ slice.nil ∧ gs.length = ps.length⌝ ∗ prs ↦*□ gs ∗
      [∗list] k ↦ g ∈ gs, propHeld γ i false g (ps.getD k default))

theorem ownRep_of (γ : EpNames) (i : Nat) (r : Loc) (σ : RState) :
    ⌜instBounds σ.inst⌝ ∗ ⌜cutBounds σ.committedUpTo⌝ ∗ repInsts (GF := GF) γ i r σ.inst ∗
      ownRepRest i r σ ⊢ ownRep γ i r σ := by
  rw [ownRep_unseal]; unfold ownRepDef ownRepRest
  iintro ⟨%H1, %H2, H3, H4, H5, H6, H7, H8, H9, H10, H11, H12, H13, H14, H15⟩
  iframe; ipureintro; exact ⟨H1, H2⟩

theorem ownRep_open (γ : EpNames) (i : Nat) (r : Loc) (σ : RState) :
    ownRep (GF := GF) γ i r σ ⊢ ⌜instBounds σ.inst⌝ ∗ ⌜cutBounds σ.committedUpTo⌝ ∗ repInsts γ i r σ.inst ∗
      ownRepRest i r σ := by
  rw [ownRep_unseal]; unfold ownRepDef ownRepRest
  iintro ⟨%H1, %H2, H3, H4, H5, H6, H7, H8, H9, H10, H11, H12, H13, H14, H15⟩
  iframe; ipureintro; exact ⟨H1, H2⟩

/-- A handler that sent nothing ends with its step's state. -/
theorem repDone_of (γ : EpNames) (i : Nat) (r : Loc) (σ : RState) (outs : List Out)
    (h : NoSends outs) :
    ownRep (GF := GF) γ i r σ ∗ repFrag γ i σ ∗ outsOk γ i outs ⊢ repDone γ i r := by
  iintro ⟨Hr, Hf, Ho⟩
  ihave Hi := outsOk_idle (GF := GF) γ i outs h $$ Ho
  unfold repDone
  iexists σ
  iframe

/-- `ownRepRest` after `maxRecvBallot`'s update. -/
theorem ownRepRest_bump (i : Nat) (r : Loc) (σ : RState) (b : w32) :
    ownRepRest (GF := GF) i r σ ⊢ (efld r go!"maxRecvBallot" ↦ σ.maxRecvBallot) ∗
      (efld r go!"maxRecvBallot" ↦ (bumpRecvBallot σ b).maxRecvBallot -∗
        ownRepRest i r (bumpRecvBallot σ b)) := by
  unfold ownRepRest
  iintro ⟨H4, H5, H6, H7, H8, H9, H10, H11, H12, H13, H14, H15⟩
  iframe H11
  iintro H11
  simp only [bumpRecvBallot_crt, bumpRecvBallot_cut, bumpRecvBallot_eut, bumpRecvBallot_conf,
    bumpRecvBallot_msk, bumpRecvBallot_maxSeq, bumpRecvBallot_leader, bumpRecvBallot_store,
    bumpRecvBallot_po, bumpRecvBallot_lastScan, bumpRecvBallot_lastPut]
  iframe

theorem ownRepRest_setInst (i : Nat) (r : Loc) (σ : RState) (x : InstId) (w : InstRec) :
    ownRepRest (GF := GF) i r (σ.setInst x w) = ownRepRest i r σ := rfl

theorem ownRepRest_updC (i : Nat) (r : Loc) (σ : RState) (q : Nat) :
    ownRepRest (GF := GF) i r (updateCommitted σ q) =
      iprop(repRowArr r go!"crtInstance" σ.crtInstance ∗
        repRowArr r go!"CommittedUpTo" (updateCommitted σ q).committedUpTo ∗
        repRowArr r go!"ExecedUpTo" σ.execedUpTo ∗
        repConf r σ.conflicts ∗ repMsk r σ.maxSeqPerKey ∗
        efld r go!"maxSeq" ↦ σ.maxSeq ∗ efld r go!"IsLeader" ↦ σ.isLeader ∗
        efld r go!"maxRecvBallot" ↦ σ.maxRecvBallot ∗
        repStore r σ.store ∗ repPeer r i σ.peerOrder ∗
        repRowArr r go!"lastScan" σ.lastScan ∗ repRowArr r go!"lastPut" σ.lastPut) := rfl

/-- Hand a slot over to be overwritten (its instance's contents but `Seq` dropped). -/
theorem ownRep_hole (γ : EpNames) (i : Nat) (r : Loc) (σ : RState) (x : InstId)
    (hq : x.q < nR) (hn : x.i < MAX_INSTANCE) :
    ownRep (GF := GF) γ i r σ ⊢ ownRepHole γ i r σ x := by
  iintro Hr
  icases ownRep_open γ i r σ $$ Hr with ⟨%H1, %H2, Hi, Hrest⟩
  unfold ownRepHole
  iframe Hrest
  isplitr
  · ipureintro; exact H1
  isplitr
  · ipureintro; exact H2
  ihave Hi := (repInsts_P γ i r σ.inst).1 $$ Hi
  icases repInstsP_acc r _ x hq hn $$ Hi with
    ⟨%iss, %rows, %row, %ptrs, %pt, #Hiss, #Hrows, %Hrow, Hptrs, %Hpt, Hx, Hclose⟩
  have hset : ptrs.set x.i pt = ptrs := by
    have := List.getElem?_eq_some_iff.mp Hpt.1
    rw [← this.2]; exact List.set_getElem_self this.1
  ihave Hc := Hclose $$ %pt %(slotSeq (σ.inst x)) [Hptrs] [Hx]
  · rw [hset]; iexact Hptrs
  · unfold slotSeq instAt
    rcases σ.inst x with _ | w
    · iexact Hx
    · unfold ownInst
      icases Hx with ⟨%y, Hy, %Hyf, -⟩
      iexists y; iframe Hy; ipureintro; exact Hyf.2.2.2.1
  iexact Hc

theorem repInstsP_congr (r : Loc) (P Q : InstId → Loc → IProp GF) (h : P = Q) :
    repInstsP r P ⊢ repInstsP r Q := by rw [h]

end heap

end Perennial.github_com.imdea_software.swiftpaxos_epaxos
