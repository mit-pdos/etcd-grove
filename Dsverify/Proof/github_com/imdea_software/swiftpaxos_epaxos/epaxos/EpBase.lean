/-
The epaxos proofs' shared definitions and the representation's access lemmas.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Interface.EpaxosRep
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Interface.ReplicaSpec
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Interface.Misc
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.epaxos.BigOpExtra
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.epaxos.ModelFacts

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net github_com.imdea_software.swiftpaxos_epaxos.kvs
open model epaxosProof

attribute [local instance] GooseGlobalGS.gooseInvGS

/-! ## Pure helpers -/

theorem slt_iff {n : Nat} (a b : BitVec n) : a.slt b = true ↔ a.toInt < b.toInt := by
  simp [BitVec.slt]

theorem sle_iff {n : Nat} (a b : BitVec n) : a.sle b = true ↔ a.toInt ≤ b.toInt := by
  simp [BitVec.sle]

theorem stGe_iff (a b : w8) : stGe a b = true ↔ sint.Z b ≤ sint.Z a := sle_iff b a

theorem map_range_upd {β : Type} (f : Nat → β) (q N : Nat) (v : β) (hq : q < N) :
    (List.range N).map (upd f q v) = ((List.range N).map f).set q v := by
  apply List.ext_getElem
  · simp
  · intro k h1 h2
    simp only [List.getElem_map, List.getElem_range, List.getElem_set, upd]
    by_cases hk : k = q
    · subst hk; simp
    · simp [hk, Ne.symm hk]

theorem bumpCrt_crt_true (σ : RState) (q : Nat) (n : w32)
    (h : sint.Z (σ.crtInstance q) < sint.Z n) :
    (bumpCrt σ q n).crtInstance = upd σ.crtInstance q n := by
  unfold bumpCrt; rw [if_pos ((slt_iff _ _).mpr h)]

theorem bumpCrt_crt_false (σ : RState) (q : Nat) (n : w32)
    (h : ¬ sint.Z (σ.crtInstance q) < sint.Z n) :
    (bumpCrt σ q n).crtInstance = σ.crtInstance := by
  unfold bumpCrt; rw [if_neg (fun h' => h ((slt_iff _ _).mp h'))]

theorem bumpRecvBallot_true (σ : RState) (b : w32) (h : sint.Z σ.maxRecvBallot < sint.Z b) :
    bumpRecvBallot σ b = { σ with maxRecvBallot := b } := by
  unfold bumpRecvBallot; rw [if_pos ((slt_iff _ _).mpr h)]

theorem bumpRecvBallot_false (σ : RState) (b : w32) (h : ¬ sint.Z σ.maxRecvBallot < sint.Z b) :
    bumpRecvBallot σ b = σ := by
  unfold bumpRecvBallot; rw [if_neg (fun h' => h ((slt_iff _ _).mp h'))]

@[simp] theorem bumpCrt_maxRecvBallot (σ : RState) (q : Nat) (n : w32) :
    (bumpCrt σ q n).maxRecvBallot = σ.maxRecvBallot := by
  unfold bumpCrt; split <;> rfl

theorem instBounds_upd (f : InstId → Option InstRec) (x : InstId) (o : Option InstRec)
    (hf : instBounds f) (hq : x.q < nR) (hi : x.i + 1 < MAX_INSTANCE) :
    instBounds (upd f x o) := by
  intro y hy
  unfold upd
  by_cases h : y = x
  · subst h; omega
  · simp only [h, if_false]; exact hf y hy

theorem bumpRecvBallot_bumpCrt_mrb (σ : RState) (q : Nat) (n b : w32) :
    (bumpRecvBallot (bumpCrt σ q n) b).maxRecvBallot = (bumpRecvBallot σ b).maxRecvBallot := by
  unfold bumpRecvBallot bumpCrt; split <;> split <;> simp_all

section heap
variable [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [go.Semantics]
variable [epaxos.Assumptions] [HasExt netExt] [π : NetProtoGS]
variable [state.Assumptions] [github_com.emirpasic.gods.maps.treemap.Assumptions] [TH : TreemapHyp GF]

/-- `(*state.Command).String()` (needed by `handleCommit`'s re-proposal log line): the interface's
`state.Command.String.spec` (HUB-REQUEST epaxos-3; stage 2: a SCAN with at least 8 bytes of
value, as a client's `cmdOf` gives it). -/
def CmdStringSpec : Prop :=
  ∀ (c : Loc) (dq : DFrac) (cv : state.Command) (wc : WCmd),
  (wc.op = opSCAN → 8 ≤ wc.val.length) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.imdea_software.swiftpaxos_epaxos.state ∗
      c ↦{dq} cv ∗ cmdOk cv wc }}
    (App (Val (c @!! go.GoType.PointerType state.Command.ty @!! go!"String")) (Val #()))
  {{ (s : GoString), RET #s; c ↦{dq} cv }}

theorem ownCmds_open (sl : GoSlice) (cs : List WCmd) (dq : DFrac) :
    ownCmds (GF := GF) sl cs dq ⊢ ∃ vs : List state.Command, sl ↦*{dq} vs ∗ ⌜vs.length = cs.length⌝ ∗
      [∗list] j ↦ c ∈ vs, ∃ wc, ⌜cs[j]? = some wc⌝ ∗ cmdOk c wc := by
  unfold ownCmds; exact .rfl

theorem ownCmds_close (sl : GoSlice) (cs : List WCmd) (dq : DFrac) (vs : List state.Command) :
    sl ↦*{dq} vs ∗ ⌜vs.length = cs.length⌝ ∗
      ([∗list] j ↦ c ∈ vs, ∃ wc, ⌜cs[j]? = some wc⌝ ∗ cmdOk (GF := GF) c wc) ⊢ ownCmds sl cs dq := by
  unfold ownCmds; iintro H; iexists vs; iexact H

instance ownCmds_discard_persistent (sl : GoSlice) (cs : List WCmd) :
    Persistent (ownCmds (GF := GF) sl cs DFrac.discard) := by
  unfold ownCmds; infer_instance

theorem ownCmds_persist (sl : GoSlice) (cs : List WCmd) (dq : DFrac) :
    ownCmds (GF := GF) sl cs dq ⊢ |==> ownCmds sl cs DFrac.discard := by
  iintro H
  icases ownCmds_open _ _ _ $$ H with ⟨%vs, Hs, %Hl, Hc⟩
  imod ownSlice_persist $$ Hs with Hs
  imodintro
  iapply ownCmds_close _ _ _ vs
  iframe Hs Hc; ipureintro; exact Hl

theorem ownCmds_nonnil (sl : GoSlice) (cs : List WCmd) (dq : DFrac) (h : cs ≠ []) :
    ownCmds (GF := GF) sl cs dq ⊢ ⌜sl ≠ slice.nil⌝ := by
  iintro H
  icases ownCmds_open _ _ _ $$ H with ⟨%vs, Hs, %Hl, -⟩
  ihave %Hlen := ownSlice_len _ _ _ $$ Hs
  ipureintro
  intro hn; subst hn
  have : vs.length = 0 := by have := Hlen.1; simp [slice.nil] at this; rw [this]; rfl
  apply h; rw [← List.length_eq_zero_iff]; omega

instance prCmds_persistent (sl : GoSlice) (cnil : Bool) (cs : List WCmd) :
    Persistent (prCmds (GF := GF) sl cnil cs) := by
  cases cnil <;> unfold prCmds <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;>
    infer_instance

/-- A record's command slice as a stored reply's (`cmdsNil` iff no commands). -/
theorem prCmds_of_cmdsRep (sl : GoSlice) (o : Option (List WCmd)) :
    cmdsRep (GF := GF) sl o ⊢ prCmds sl (decide (o = none)) (o.getD []) := by
  cases o with
  | none => unfold cmdsRep prCmds; simp
  | some cs =>
    unfold cmdsRep prCmds
    simp only [reduceCtorEq, decide_false, Bool.false_eq_true, ite_false, Option.getD_some]
    iintro ⟨-, H⟩; iexact H

/-- A stored reply with commands (not `cmdsNil`, a non-empty list) as a record's command slice. -/
theorem cmdsRep_of_prCmds (sl : GoSlice) (cnil : Bool) (cs : List WCmd)
    (h : cnil = false → cs ≠ []) :
    prCmds (GF := GF) sl cnil cs ⊢ cmdsRep sl (if cnil then none else some cs) := by
  cases cnil with
  | true => unfold prCmds cmdsRep; simp
  | false =>
    unfold prCmds cmdsRep
    simp only [Bool.false_eq_true, ite_false]
    iintro #H
    ihave %Hnn := ownCmds_nonnil _ _ _ (h rfl) $$ H
    iframe H; ipureintro; exact Hnn

/-- `Durable` is false (an unfold of `isReplicaFw`: no law gives `fwFrozen`; see
`notes/prove-epaxos.md`). -/
theorem isReplicaFw_durable (γ : EpNames) (rr : Loc) (i : Nat) (L : List GoString) (p : FwPtrs)
    (Rext : IProp GF) :
    isReplicaFw γ rr i L p Rext ⊢ fld rr go!"Durable" ↦□ false := by
  rw [isReplicaFw_unseal]; unfold isReplicaFwDef
  iintro ⟨-, #Hfz, -⟩
  ihave ⟨-, $⟩ := fwFrozen_fields _ _ _ _ $$ Hfz

/-- The read-only part of a held proposal (for its log line). -/
theorem propHeld_ro (γ : EpNames) (i : Nat) (b : Bool) (g : Loc) (p : Proposal) :
    propHeld (GF := GF) γ i b g p ⊢ propHeld γ i b g p ∗ ∃ (pp w mu : Loc) (proxy : Bool) (addr : GoString)
      (c : w32) (cv : state.Command) (wc : WCmd),
      g ↦□ replica.defs.GPropose.mk pp w mu proxy addr ∗
      pp ↦□ replica.defs.Propose.mk (W32 0) c cv (W64 0) ∗ cmdOk cv wc ∗
      ⌜wc.op = opSCAN → 8 ≤ wc.val.length⌝ := by
  unfold propHeld
  iintro ⟨%pp, %w, %mu, %proxy, %addr, %c, %inp, %cv, #Hg, #Hpp, #Hok, Hrest⟩
  isplitl [Hrest]
  · iexists pp, w, mu, proxy, addr, c, inp, cv; iframe Hg Hpp Hok Hrest
  · iexists pp, w, mu, proxy, addr, W32 (uint.Z c), cv, cmdOf inp; iframe Hg Hpp Hok
    ipureintro
    intro h
    cases inp with
    | get k => exact absurd h (by simp only [cmdOf, opGET, opSCAN]; decide)
    | put k v => exact absurd h (by simp only [cmdOf, opPUT, opSCAN]; decide)
    | scan k n => simp only [cmdOf, u64Le_length]; omega

/-- A held proposal of a non-executed instance and its re-proposal token make a `ProposeChan`
proposal. -/
theorem propHeld_proposal (γ : EpNames) (i : Nat) (g : Loc) (p : Proposal) :
    propHeld (GF := GF) γ i false g p ∗ inChan γ i p ⊢ proposal γ i g := by
  unfold propHeld proposal
  iintro ⟨⟨%pp, %w, %mu, %proxy, %addr, %c, %inp, %cv, #Hg, #Hpp, #Hok, #Hcc, %Hcmd, #Hcw, Htok⟩,
    Hin⟩
  iexists pp, w, mu, proxy, addr, p.cid, c, inp, cv
  simp only [Bool.false_eq_true, if_false]
  iframe Hg Hpp Hok Hcc Hcw Htok
  iright
  rw [← Hcmd]
  iexact Hin

/-- The image of the pointer `p` at slot `x`: `nil` for no instance. -/
def instAt (γ : EpNames) (i : Nat) (x : InstId) (p : Loc) : Option InstRec → IProp GF
  | none => iprop(⌜p = null⌝)
  | some w => ownInst γ i x p w

/-- Open slot `x` of the rows: its row's pointers, the slot's pointer and image; close it with a
new pointer and image (the other slots unchanged). -/
theorem repInsts_acc (γ : EpNames) (i : Nat) (r : Loc) (inst : InstId → Option InstRec)
    (x : InstId) (hq : x.q < nR) (hn : x.i < MAX_INSTANCE) :
    repInsts (GF := GF) γ i r inst ⊢ ∃ (iss : GoSlice) (rows : List GoSlice) (row : GoSlice)
        (ptrs : List Loc) (p : Loc),
      efld r go!"InstanceSpace" ↦□ iss ∗ iss ↦*□ rows ∗ ⌜rows[x.q]? = some row⌝ ∗
      row ↦* ptrs ∗ ⌜ptrs[x.i]? = some p ∧ ptrs.length = MAX_INSTANCE⌝ ∗
      instAt γ i x p (inst x) ∗
      (∀ (p' : Loc) (o : Option InstRec), row ↦* ptrs.set x.i p' -∗ instAt γ i x p' o -∗
        repInsts γ i r (upd inst x o)) := by
  obtain ⟨q, n⟩ := x
  dsimp only at hq hn ⊢
  unfold repInsts
  iintro ⟨%iss, %rows, #Hiss, #Hrows, %Hlen, Hrs⟩
  obtain ⟨row, Hrow⟩ : ∃ row, rows[q]? = some row :=
    ⟨rows[q]'(by omega), List.getElem?_eq_getElem (by omega)⟩
  icases bigSepL_set_acc' Hrow $$ Hrs with ⟨Hr, Hclose⟩
  unfold ownRowI
  icases Hr with ⟨%ptrs, Hptrs, %Hplen, Hps⟩
  obtain ⟨p, Hp⟩ : ∃ p, ptrs[n]? = some p :=
    ⟨ptrs[n]'(by omega), List.getElem?_eq_getElem (by omega)⟩
  icases bigSepL_set_acc' Hp $$ Hps with ⟨Hx, Hpclose⟩
  iexists iss, rows, row, ptrs, p
  iframe Hiss Hrows Hptrs
  isplitr
  · ipureintro; exact Hrow
  isplitr
  · ipureintro; exact ⟨Hp, Hplen⟩
  isplitl [Hx]
  · unfold instAt
    rcases hx : inst ⟨q, n⟩ with _ | w <;> simp only [hx] <;> iexact Hx
  iintro %p' %o Hptrs Hx
  ihave Hps := Hpclose $$ %(fun k z => match upd inst ⟨q, n⟩ o ⟨q, k⟩ with
      | none => iprop(⌜z = null⌝)
      | some w => ownInst γ i ⟨q, k⟩ z w) %p' [] [Hx]
  · ipureintro
    intro k hk
    funext z
    simp only [upd, InstId.mk.injEq, true_and, hk, if_false]
    rcases inst ⟨q, k⟩ <;> rfl
  · unfold instAt
    rcases hx : o with _ | w <;> simp only [upd, if_true] <;> iexact Hx
  ihave Hrs := Hclose $$ %(fun q' row => ownRowI γ i q' row (upd inst ⟨q, n⟩ o)) %row [] [Hptrs Hps]
  · ipureintro
    intro k hk
    funext row'
    unfold ownRowI
    congr 1; funext ptrs'; congr 1; congr 1; congr 1
    funext k' z
    simp only [upd, InstId.mk.injEq, hk, _root_.false_and, if_false]
  · unfold ownRowI
    iexists ptrs.set n p'
    iframe Hptrs Hps
    ipureintro; simp [Hplen]
  iexists iss, rows
  iframe Hiss Hrows
  isplitr
  · ipureintro; exact Hlen
  have hset : rows.set q row = rows := by
    have := List.getElem?_eq_some_iff.mp Hrow
    rw [← this.2]; exact List.set_getElem_self this.1
  rw [hset]
  irevert Hrs
  unfold ownRowI
  iintro Hrs
  iexact Hrs

/-- A fresh `newInstanceDefault(x.q, x.i)`. -/
theorem ownInst_default (γ : EpNames) (i : Nat) (x : InstId) (p idp : Loc) (t : w64) :
    p ↦ epaxos.Instance.mk slice.nil (W32 (-1)) (W32 (-1)) stNONE (W32 (-1)) slice.nil null
        (W64 0) (W64 0) interface.nil t idp ∗
      idp ↦□ epaxos.instanceId.mk (W32 x.q) (W32 x.i) ⊢
    ownInst (GF := GF) γ i x p (newInstanceDefault x) := by
  iintro ⟨Hp, #Hid⟩
  unfold ownInst newInstanceDefault cmdsRep
  iexists _
  iframe Hp Hid
  isplitr
  · ipureintro; simp [stNONE, stEXECUTED]
  isplitr
  · ipureintro; rfl
  isplitr
  · iexists (DFrac.own 1)
    iapply ownSlice_nil
  · ipureintro; rfl

end heap

end Perennial.github_com.imdea_software.swiftpaxos_epaxos
