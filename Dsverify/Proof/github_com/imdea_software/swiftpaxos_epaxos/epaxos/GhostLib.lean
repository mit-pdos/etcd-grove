/-
The epaxos package's ghost-state library (package-internal; `notes/prove-epaxos.md`, "Ghost
state"):

* `Pos.Countable` instances for the model's records (`InstId`, `Proposal`, `Bcast`, ...), what the
  standard ghost libraries store;
* an injective encoding of a replica's protocol state `RState` (not countable: it has functions
  with infinite domains) into the functions `Pos → DiscreteO Pos`, an OFE the universal camera
  codes (`discreteFunO pos (leibnizO pos)`): `encRS`;
* a fractional mono-list of `RState`s over that encoding (`rsAuth`, `rsLb`, `rsIdx`), the
  replicas' fragments (a copy of Perennial's `MonoList.lean` with `encRS` for `encodeO`);
* `allocFun` (finitely many names by index).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Interface.Client
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Model.Inv

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net github_com.imdea_software.swiftpaxos_epaxos.kvs
open CMRA MonoList

attribute [local instance] GooseGlobalGS.gooseInvGS

namespace model

/-! ## Countable instances -/

instance instId_countable : Pos.Countable InstId :=
  .ofInjective (fun x => Pos.Countable.encode (x.q, x.i)) (by
    intro a b h; have h' := Pos.encode_inj h; cases a; cases b; simp_all)

instance instPair_countable : Pos.Countable InstPair :=
  .ofInjective (fun x => Pos.Countable.encode (x.last, x.lastWrite)) (by
    intro a b h; have h' := Pos.encode_inj h; cases a; cases b; simp_all)

instance proposal_countable : Pos.Countable Proposal :=
  .ofInjective (fun x => Pos.Countable.encode (x.cid, x.cmd)) (by
    intro a b h; have h' := Pos.encode_inj h; cases a; cases b; simp_all)

instance preply_countable : Pos.Countable PReply :=
  .ofInjective (fun x => Pos.Countable.encode (Msg.prepareReply x.m, x.cmdsNil)) (by
    intro a b h; have h' := Pos.encode_inj h; cases a; cases b; simp_all)

def LbRec.tup (l : LbRec) :=
  (l.clientProposals, l.ballot, l.allEqual, l.preAcceptOKs, l.acceptOKs, l.nacks,
    l.prepareReplies, l.preparing, l.tryingToPreAccept, l.lastTriedBallot, l.cmds, l.status,
    l.seq, l.deps, l.leaderResponded, l.preAcceptsSent)

instance lbRec_countable : Pos.Countable LbRec :=
  .ofInjective (fun x => Pos.Countable.encode x.tup) (by
    intro a b h; have h' := Pos.encode_inj h; cases a; cases b; simp_all [LbRec.tup])

def InstRec.tup (w : InstRec) :=
  (w.cmds, w.bal, w.vbal, w.status, w.seq, w.deps, w.lb, w.id)

instance instRec_countable : Pos.Countable InstRec :=
  .ofInjective (fun x => Pos.Countable.encode x.tup) (by
    intro a b h; have h' := Pos.encode_inj h; cases a; cases b; simp_all [InstRec.tup])

instance bcast_countable : Pos.Countable Bcast :=
  .ofInjective (fun x => Pos.Countable.encode (x.x, x.m, x.peers, x.need, x.sent, x.trackPA)) (by
    intro a b h; have h' := Pos.encode_inj h; cases a; cases b; simp_all)

/-! ## `RState` as a function -/

/-- `RState`'s fields by a key `(field, a, b, k)`. -/
def RState.view (σ : RState) : Nat × Nat × Nat × w64 → Pos
  | (0, _, _, _) => Pos.Countable.encode σ.id
  | (1, _, _, _) => Pos.Countable.encode σ.peerOrder
  | (2, _, _, _) => Pos.Countable.encode σ.isLeader
  | (3, q, n, _) => Pos.Countable.encode (σ.inst ⟨q, n⟩)
  | (4, q, _, _) => Pos.Countable.encode (σ.crtInstance q)
  | (5, q, _, _) => Pos.Countable.encode (σ.committedUpTo q)
  | (6, q, _, _) => Pos.Countable.encode (σ.execedUpTo q)
  | (7, q, _, k) => Pos.Countable.encode (σ.conflicts q k)
  | (8, _, _, k) => Pos.Countable.encode (σ.maxSeqPerKey k)
  | (9, _, _, _) => Pos.Countable.encode σ.maxSeq
  | (10, _, _, _) => Pos.Countable.encode σ.maxRecvBallot
  | (11, _, _, k) => Pos.Countable.encode (σ.store k)
  | (12, q, _, _) => Pos.Countable.encode (σ.lastScan q)
  | (13, q, _, _) => Pos.Countable.encode (σ.lastPut q)
  | _ => 1

theorem RState.view_inj {σ σ' : RState} (h : σ.view = σ'.view) : σ = σ' := by
  have e : ∀ k, σ.view k = σ'.view k := fun k => congrFun h k
  cases σ; cases σ'
  simp only [RState.mk.injEq]
  refine ⟨Pos.encode_inj (e (0, 0, 0, 0)), Pos.encode_inj (e (1, 0, 0, 0)),
    Pos.encode_inj (e (2, 0, 0, 0)), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    Pos.encode_inj (e (9, 0, 0, 0)), Pos.encode_inj (e (10, 0, 0, 0)), ?_⟩
  · funext x; cases x with | mk q n => exact Pos.encode_inj (e (3, q, n, 0))
  · funext q; exact Pos.encode_inj (e (4, q, 0, 0))
  · funext q; exact Pos.encode_inj (e (5, q, 0, 0))
  · funext q; exact Pos.encode_inj (e (6, q, 0, 0))
  · funext q k; exact Pos.encode_inj (e (7, q, 0, k))
  · funext q; exact Pos.encode_inj (e (12, q, 0, 0))
  · funext q; exact Pos.encode_inj (e (13, q, 0, 0))
  · funext k; exact Pos.encode_inj (e (8, 0, 0, k))
  · funext k; exact Pos.encode_inj (e (11, 0, 0, k))

end model

open model

/-- A function on a countable domain as a function on `Pos`. -/
def encFun {D : Type} [Pos.Countable D] (f : D → Pos) : Pos → DiscreteO Pos :=
  fun p => ⟨@dite _ (∃ d : D, Pos.Countable.encode d = p) (Classical.propDecidable _)
    (fun h => f (Classical.choose h)) (fun _ => 1)⟩

theorem encFun_inj {D : Type} [Pos.Countable D] {f g : D → Pos} (H : encFun f = encFun g) :
    f = g := by
  funext d
  have e := congrArg DiscreteO.car (congrFun H (Pos.Countable.encode d))
  have hx : ∃ d' : D, Pos.Countable.encode d' = Pos.Countable.encode d := ⟨d, rfl⟩
  simp only [encFun] at e
  rw [dif_pos hx, dif_pos hx] at e
  have hc : Classical.choose hx = d := Pos.encode_inj (Classical.choose_spec hx)
  rwa [hc] at e

/-- A replica's state, encoded. -/
def encRS (σ : RState) : Pos → DiscreteO Pos := encFun σ.view

theorem encRS_inj {σ σ' : RState} (h : encRS σ = encRS σ') : σ = σ' :=
  RState.view_inj (encFun_inj h)

theorem map_encRS_inj : ∀ {l1 l2 : List RState}, l1.map encRS = l2.map encRS → l1 = l2
  | [], [], _ => rfl
  | [], _ :: _, h => nomatch h
  | _ :: _, [], h => nomatch h
  | _ :: _, _ :: _, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    rw [encRS_inj h.1, map_encRS_inj h.2]

theorem map_encRS_prefix {l1 l2 : List RState} (h : l1.map encRS <+: l2.map encRS) :
    l1 <+: l2 := by
  obtain ⟨t, ht⟩ := h
  obtain ⟨a, b, rfl, ha, _⟩ := List.map_eq_append_iff.mp ht.symm
  exact ⟨b, by rw [map_encRS_inj ha]⟩

theorem prefix_getElem?' {A : Type} {l1 l2 : List A} {i : Nat} {a : A} (h : l1 <+: l2)
    (hi : l1[i]? = some a) : l2[i]? = some a := by
  obtain ⟨t, rfl⟩ := h
  grind

section ghost
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [G : GooseGlobalGS .hasLC GF] [π : NetProtoGS]

/-! ## A fractional mono-list of replica states -/

def rsAuth (γ : GName) (q : Qp) (l : List RState) : IProp GF :=
  own γ (MonoList.auth (DFrac.own q) (l.map encRS))

def rsLb (γ : GName) (l : List RState) : IProp GF :=
  own γ (MonoList.lb (l.map encRS))

def rsIdx (γ : GName) (i : Nat) (a : RState) : IProp GF :=
  iprop(∃ l : List RState, ⌜l[i]? = some a⌝ ∗ rsLb γ l)

instance rsAuth_timeless (γ : GName) (q : Qp) (l : List RState) : Timeless (rsAuth (GF := GF) γ q l) := by
  unfold rsAuth; infer_instance
instance rsLb_timeless (γ : GName) (l : List RState) : Timeless (rsLb (GF := GF) γ l) := by
  unfold rsLb; infer_instance
instance rsLb_persistent (γ : GName) (l : List RState) : Persistent (rsLb (GF := GF) γ l) := by
  unfold rsLb; infer_instance
instance rsIdx_timeless (γ : GName) (i : Nat) (a : RState) : Timeless (rsIdx (GF := GF) γ i a) := by
  unfold rsIdx; infer_instance
instance rsIdx_persistent (γ : GName) (i : Nat) (a : RState) : Persistent (rsIdx (GF := GF) γ i a) := by
  unfold rsIdx; infer_instance

theorem rsAuth_op (γ : GName) (p q : Qp) (l : List RState) :
    rsAuth (GF := GF) γ (p + q) l ⊣⊢ rsAuth γ p l ∗ rsAuth γ q l := by
  unfold rsAuth
  rw [← (own_op γ _ _).to_eq]
  exact (congrArg (own γ) (auth_dfrac_op (.own p) (.own q) _)).to_bi

theorem rsAuth_agree (γ : GName) (q1 q2 : Qp) (l1 l2 : List RState) :
    rsAuth (GF := GF) γ q1 l1 -∗ rsAuth γ q2 l2 -∗ ⌜q1 + q2 ≤ 1 ∧ l1 = l2⌝ := by
  unfold rsAuth
  iintro H1 H2
  icombine H1 H2 gives %Hvalid
  ipureintro
  obtain ⟨hdq, hl⟩ := (auth_dfrac_op_valid ..).mp Hvalid
  exact ⟨hdq, map_encRS_inj hl⟩

theorem rsAuth_lb_valid (γ : GName) (q : Qp) (l1 l2 : List RState) :
    rsAuth (GF := GF) γ q l1 -∗ rsLb γ l2 -∗ ⌜l2 <+: l1⌝ := by
  unfold rsAuth rsLb
  iintro H1 H2
  icombine H1 H2 gives %Hvalid
  ipureintro
  obtain ⟨_, hpre⟩ := (both_dfrac_valid ..).mp Hvalid
  exact map_encRS_prefix hpre

theorem rsAuth_idx_lookup (γ : GName) (q : Qp) (l : List RState) (i : Nat) (a : RState) :
    rsAuth (GF := GF) γ q l -∗ rsIdx γ i a -∗ ⌜l[i]? = some a⌝ := by
  unfold rsIdx
  iintro H1 H2
  icases H2 with ⟨%l1, %Hl1, H2⟩
  icases rsAuth_lb_valid γ q l l1 $$ H1 H2 with %Hpre
  ipureintro
  exact prefix_getElem?' Hpre Hl1

theorem rsLb_get (γ : GName) (q : Qp) (l : List RState) : rsAuth (GF := GF) γ q l ⊢ rsLb γ l := by
  unfold rsAuth rsLb
  exact own_mono γ _ _ (included ..)

theorem rsIdx_get (γ : GName) (q : Qp) (l : List RState) (i : Nat) (a : RState)
    (h : l[i]? = some a) : rsAuth (GF := GF) γ q l ⊢ rsAuth γ q l ∗ rsIdx γ i a := by
  iintro H
  ihave #Hlb := rsLb_get γ q l $$ H
  iframe H
  unfold rsIdx
  iexists l
  iframe Hlb %h

theorem rsAuth_alloc (l : List RState) : ⊢ |==> ∃ γ, rsAuth (GF := GF) γ 1 l := by
  unfold rsAuth
  imod own_alloc (●ML (l.map encRS) • ◯ML (l.map encRS))
    ((both_valid ..).mpr List.prefix_rfl) with ⟨%γ, H⟩
  imodintro
  iexists γ
  icases (own_op γ _ _).1 $$ H with ⟨$, -⟩

theorem rsAuth_update_app (γ : GName) (l : List RState) (l' : List RState) :
    rsAuth (GF := GF) γ 1 l ==∗ rsAuth γ 1 (l ++ l') := by
  unfold rsAuth
  iintro H
  iapply own_update γ _ _ (update _ ((List.prefix_append l l').map _)) $$ H

/-! ## Finitely many names by index -/

theorem allocFun {B : Type} (b0 : B) (R : Nat → B → IProp GF)
    (h : ∀ i, ⊢ |==> ∃ b, R i b) : ∀ (l : List Nat), l.Nodup →
    ⊢ |==> ∃ g : Nat → B, [∗list] i ∈ l, R i (g i)
  | [], _ => by
    iapply bupd_intro
    iexists (fun _ => b0)
    iapply BigSepL.bigSepL_nil.2
    iempintro
  | a :: l, hl => by
    have ha : a ∉ l := (List.nodup_cons.mp hl).1
    imod allocFun b0 R h l (List.nodup_cons.mp hl).2 with ⟨%g, H⟩
    imod h a with ⟨%b, Hb⟩
    imodintro
    iexists (fun j => if j = a then b else g j)
    iapply BigSepL.bigSepL_cons.2
    isplitl [Hb]
    · simp only [ite_true]; iexact Hb
    · iapply BigSepL.bigSepL_mono ?_ $$ H
      intro _ j hj
      have hj' : j ≠ a := fun e => ha (e ▸ List.mem_of_getElem? hj)
      simp only [if_neg hj']
      exact .rfl

end ghost

end Perennial.github_com.imdea_software.swiftpaxos_epaxos
