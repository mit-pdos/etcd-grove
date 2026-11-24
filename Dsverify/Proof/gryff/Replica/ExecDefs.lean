/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/Replica/ExecDefs.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

The executor's resources (G2: the replica's lock).

* `XS`: the executor's search state as ghost state (`ρ.xs`, a ghost variable): the executed instances
  in order, each instance's `Index` and `Lowlink`. The lock invariant holds half (the heap's fields
  agree with it), the executor the other half: the run loop cannot change an instance's `Index`,
  `Lowlink` or executed status while the executor waits with the lock released.
* `ρ.ptrs`: each instance's pointer (a ghost map with persistent elements: an `InstanceSpace` slot,
  once set, keeps its pointer).
* `instOwn γ xs n p`: instance `n`'s struct at `p`; committed or executed, it holds its committed
  attributes (`instIs`, U4's `insts`) in its fields (`attrsMatch`).
* `lockInvExec`: the lock invariant's part the executor reads (the instance space, `crtInstance`).
* (Stage 1's `execFixed`, `execPriv`, `overwriteP` and the chain share `execOwn`/`execWit` of
  `Replica/ExecLaw.lean` were removed: stage-1 relics, not reached by `goal_spec`.)
-/
module

public import Dsverify.Proof.gryff.Replica.ExecModel
public import Dsverify.Proof.gryff.Replica.Base
public import Perennial.Golang.Theory.Chan.Idioms.Bag
public import Perennial.Proof.sync

@[expose] public section

noncomputable section

namespace Perennial.gryff.replica

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode proto

/-- The executor's search state: executed instances (in order), `Index`, `Lowlink`. -/
abbrev XS := List Node × GMap Node Nat × GMap Node Nat

def XS.numF (xs : XS) (n : Node) : Nat := (xs.2.1.lookup n).getD 0
def XS.lowF (xs : XS) (n : Node) : Nat := (xs.2.2.lookup n).getD 0
/-- The pure model's state of `xs` with stack `S` and next index `idx`. -/
def XS.toT (xs : XS) (S : List Node) (idx : Nat) : TState := ⟨xs.1, S, xs.numF, xs.lowF, idx⟩

/-- Set an instance's `Index` and `Lowlink`. -/
def XS.setNL (xs : XS) (n : Node) (num low : Nat) : XS :=
  (xs.1, GMap.insert n num xs.2.1, GMap.insert n low xs.2.2)
/-- Set an instance's `Lowlink`. -/
def XS.setLow (xs : XS) (n : Node) (low : Nat) : XS := (xs.1, xs.2.1, GMap.insert n low xs.2.2)

theorem XS.numF_setNL (xs : XS) (n m : Node) (a b : Nat) :
    (xs.setNL n a b).numF m = if n = m then a else xs.numF m := by
  simp only [XS.setNL, XS.numF, GMap.lookup_insert_eq_iff]; split <;> rfl
theorem XS.lowF_setNL (xs : XS) (n m : Node) (a b : Nat) :
    (xs.setNL n a b).lowF m = if n = m then b else xs.lowF m := by
  simp only [XS.setNL, XS.lowF, GMap.lookup_insert_eq_iff]; split <;> rfl
theorem XS.numF_setLow (xs : XS) (n m : Node) (b : Nat) :
    (xs.setLow n b).numF m = xs.numF m := rfl
theorem XS.lowF_setLow (xs : XS) (n m : Node) (b : Nat) :
    (xs.setLow n b).lowF m = if n = m then b else xs.lowF m := by
  simp only [XS.setLow, XS.lowF, GMap.lookup_insert_eq_iff]; split <;> rfl

theorem XS.visit_toT (xs : XS) (S : List Node) (idx : Nat) (vn : Node) :
    (xs.toT S idx).visit vn = (xs.setNL vn idx idx).toT (S ++ [vn]) (idx + 1) := by
  simp only [TState.visit, XS.toT]
  congr 1 <;> funext m <;> simp only [upd, XS.numF_setNL, XS.lowF_setNL] <;>
    by_cases h : m = vn
  all_goals first | (subst h; simp) | (have h' : vn ≠ m := fun e => h e.symm; simp [h, h'])

theorem XS.setLow_toT (xs : XS) (S : List Node) (idx : Nat) (vn : Node) (b : Nat) :
    { xs.toT S idx with low := upd (xs.toT S idx).low vn b } = (xs.setLow vn b).toT S idx := by
  simp only [XS.toT]
  congr 1; funext m; simp only [upd, XS.lowF_setLow]
  by_cases h : m = vn
  · subst h; simp
  · have h' : vn ≠ m := fun e => h e.symm; simp [h, h']

/-- A replica's own ghost names (allocated by `NewReplica`). -/
structure ReplNames where
  xs : GName
  ptrs : GName
  cm : GName
  ch : ChanNames

/-- `epaxosproto`'s statuses (`int8`). -/
def stCommitted : w8 := W8 4
def stExecuted : w8 := W8 5

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

open gryff.src

instance instIs_persistent' (γ : ProtoNames) (n : Int × Int) (a : InstAttrs) :
    Persistent (instIs (GF := GF) γ n a) := by unfold instIs; infer_instance
instance tagValIs_persistent' (γ : ProtoNames) (t : PTag) (v : w64) :
    Persistent (tagValIs (GF := GF) γ t v) := by unfold tagValIs; infer_instance
instance storeLb_persistent' (γ : ProtoNames) (k : Nat) (t : PTag) :
    Persistent (storeLb (GF := GF) γ k t) := by unfold storeLb; infer_instance

/-- A Go tag as the model's. -/
def tagOfGo (t : gryffproto.Tag) : PTag := (sint.Z t.Ts', sint.Z t.Cid', sint.Z t.Rmwc')
/-- A Go value and tag as the model's. -/
def vtOfGo (vt : gryffproto.ValTag) : Int × PTag := (sint.Z vt.V', tagOfGo vt.T')

/-- Instance `iv`'s fields hold the committed attributes `a`; `c` is its one command. -/
def attrsMatch (a : InstAttrs) (iv : gryff.Instance) (c : state.Command) : Prop :=
  c.K' = W64 0 ∧ sint.Z c.OldValue' = a.old ∧ sint.Z c.V' = a.new ∧ sint.Z iv.Seq' = a.seq ∧
    a.deps = (iv.Deps'.arr.take 3).map (fun d => sint.Z d) ∧ iv.Deps'.arr.length = 5 ∧
    (∀ d ∈ a.deps, -1 ≤ d ∧ d < 2 * 1024 * 1024) ∧ a.base = vtOfGo iv.Base'

/-- A leader's bookkeeping (nil at the other replicas). -/
def lbOwn (l : Loc) : IProp GF :=
  iprop(⌜l = Loc.null⌝ ∨ ∃ lbv : gryff.LeaderBookkeeping, l ↦ lbv)

/-- Instance `n`'s committed status: not committed (`ca = none`), or committed with attributes
`a` (`ca = some a`, recorded in the replica's ghost map `ρ.cm`), held in its fields. -/
def cmOwn (γ : ProtoNames) (n : Node) (ca : Option InstAttrs) (iv : gryff.Instance) : IProp GF :=
  match ca with
  | none => iprop(⌜iv.Status' ≠ stCommitted ∧ iv.Status' ≠ stExecuted⌝)
  | some a => iprop(⌜iv.Status' = stCommitted ∨ iv.Status' = stExecuted⌝ ∗ instIs γ n a ∗
      ∃ c : state.Command, iv.Cmds' ↦* [c] ∗ ⌜attrsMatch a iv c⌝)

/-- `cmOwn` reads only the status, the commands and the committed attributes' fields. -/
theorem cmOwn_congr (γ : ProtoNames) (n : Node) (ca : Option InstAttrs) (iv iv' : gryff.Instance)
    (hs : iv'.Status' = iv.Status') (hc : iv'.Cmds' = iv.Cmds') (hq : iv'.Seq' = iv.Seq')
    (hd : iv'.Deps' = iv.Deps') (hb : iv'.Base' = iv.Base') :
    cmOwn (GF := GF) γ n ca iv ⊢ cmOwn γ n ca iv' := by
  cases ca with
  | none => simp only [cmOwn]; rw [hs]
  | some a =>
    simp only [cmOwn, attrsMatch]; rw [hs, hc, hq, hd, hb]

/-- Instance `n`'s struct at `p` (`ca`: its committed attributes, if committed). -/
def instOwn (γ : ProtoNames) (xs : XS) (ca : Option InstAttrs) (n : Node) (p : Loc) : IProp GF :=
  iprop(∃ iv : gryff.Instance, p ↦ iv ∗
    ⌜sint.Z iv.Leader' = n.1 ∧ sint.Z iv.Slot' = n.2 ∧ sint.Z iv.Index' = xs.numF n ∧
      sint.Z iv.Lowlink' = xs.lowF n ∧ (iv.Status' = stExecuted ↔ n ∈ xs.1)⌝ ∗
    cmOwn γ n ca iv ∗ lbOwn iv.lb')

theorem instOwn_open (γ : ProtoNames) (xs : XS) (ca : Option InstAttrs) (n : Node) (p : Loc) :
    instOwn (GF := GF) γ xs ca n p ⊣⊢ ∃ iv : gryff.Instance, p ↦ iv ∗
      ⌜sint.Z iv.Leader' = n.1 ∧ sint.Z iv.Slot' = n.2 ∧ sint.Z iv.Index' = xs.numF n ∧
        sint.Z iv.Lowlink' = xs.lowF n ∧ (iv.Status' = stExecuted ↔ n ∈ xs.1)⌝ ∗
      cmOwn γ n ca iv ∗ lbOwn iv.lb' := .rfl

/-- The number of slots of each replica's row of the instance space. -/
def nSlots : Nat := 2 * 1024 * 1024

/-- Replica `q`'s row of the instance space: its pointers, the non-nil ones those of `M`. -/
def rowOwn (M : GMap Node Loc) (q : Nat) (s : GoSlice) : IProp GF :=
  iprop(∃ ptrs : List Loc, s ↦* ptrs ∗
    ⌜ptrs.length = nSlots ∧ ∀ (i : Nat) (p : Loc), ptrs[i]? = some p →
      M.lookup ((q : Int), (i : Int)) = (if p = Loc.null then none else some p)⌝)

theorem rows_acc (M : GMap Node Loc) (isp : List GoSlice) (q : Nat) (sq : GoSlice)
    (h : isp[q]? = some sq) :
    ([∗list] q ↦ s ∈ isp, rowOwn (GF := GF) M q s) ⊢
      rowOwn M q sq ∗ (rowOwn M q sq -∗ [∗list] q ↦ s ∈ isp, rowOwn M q s) := by
  iintro H
  icases (BigSepL.bigSepL_lookup_acc h).1 $$ H with ⟨Hq, Hclose⟩
  iframe Hq
  iintro Hq
  ihave H := Hclose $$ %sq Hq
  obtain ⟨hlt, hq⟩ := List.getElem?_eq_some_iff.1 h
  rw [show isp.set q sq = isp by rw [← hq]; exact List.set_getElem_self hlt]
  iexact H

theorem rowOwn_open (M : GMap Node Loc) (q : Nat) (s : GoSlice) :
    rowOwn (GF := GF) M q s ⊣⊢ ∃ ptrs : List Loc, s ↦* ptrs ∗
      ⌜ptrs.length = nSlots ∧ ∀ (i : Nat) (p : Loc), ptrs[i]? = some p →
        M.lookup ((q : Int), (i : Int)) = (if p = Loc.null then none else some p)⌝ := .rfl

/-- The executor's part of the lock invariant at search state `xs`: the instance space (rows
`isp`, the instances `M`), the committed ones (`CM`, permanent), `crtInstance`. -/
def liAt (γ : ProtoNames) (ρ : ReplNames) (isp : List GoSlice) (crt : GoSlice) (xs : XS) :
    IProp GF :=
  iprop(∃ (M : GMap Node Loc) (CM : GMap Node InstAttrs) (crtv : List w32),
    ghostVar ρ.xs (1 : Qp).half xs ∗ ghostMapAuth ρ.ptrs 1 M ∗
    ([∗map] n ↦ p ∈ M, ghostMapElem ρ.ptrs n DFrac.discard p) ∗
    ghostMapAuth ρ.cm 1 CM ∗ ([∗map] n ↦ a ∈ CM, ghostMapElem ρ.cm n DFrac.discard a) ∗
    ([∗list] q ↦ s ∈ isp, rowOwn M q s) ∗
    ([∗map] n ↦ p ∈ M, instOwn γ xs (CM.lookup n) n p) ∗
    crt ↦* crtv ∗
    ⌜crtv.length = 3 ∧ (∀ n, (n ∈ xs.1 ∨ xs.numF n ≠ 0) → (M.lookup n).isSome) ∧
      (∀ n, (M.lookup n).isSome → inBox n) ∧ (∀ n, (CM.lookup n).isSome → (M.lookup n).isSome)⌝)

/-- The executor's part of the lock invariant. -/
def lockInvExec (γ : ProtoNames) (ρ : ReplNames) (isp : List GoSlice) (crt : GoSlice) :
    IProp GF :=
  iprop(∃ xs : XS, liAt γ ρ isp crt xs)

/-- `instOwn` depends on the search state only at its instance. -/
theorem instOwn_congr (γ : ProtoNames) (xs xs' : XS) (ca : Option InstAttrs) (n : Node) (p : Loc)
    (h1 : xs'.numF n = xs.numF n) (h2 : xs'.lowF n = xs.lowF n) (h3 : n ∈ xs'.1 ↔ n ∈ xs.1) :
    instOwn (GF := GF) γ xs ca n p ⊢ instOwn γ xs' ca n p := by
  unfold instOwn
  iintro ⟨%iv, Hp, %Hiv, Hc, Hlb⟩
  iexists iv
  iframe
  ipureintro
  rw [h1, h2, h3]; exact Hiv

/-- Take one instance's resources out of the instance space, and put them back after changing the
search state at that instance only. -/
theorem insts_acc (γ : ProtoNames) (xs : XS) (CM : GMap Node InstAttrs) (M : GMap Node Loc)
    (vn : Node) (v : Loc) (hM : M.lookup vn = some v) :
    ([∗map] n ↦ p ∈ M, instOwn (GF := GF) γ xs (CM.lookup n) n p) ⊢
      instOwn γ xs (CM.lookup vn) vn v ∗ ∀ xs' : XS, ⌜∀ n, n ≠ vn → xs'.numF n = xs.numF n ∧
          xs'.lowF n = xs.lowF n ∧ (n ∈ xs'.1 ↔ n ∈ xs.1)⌝ -∗
        instOwn γ xs' (CM.lookup vn) vn v -∗ [∗map] n ↦ p ∈ M, instOwn γ xs' (CM.lookup n) n p := by
  iintro H
  icases (BigSepM.bigSepM_delete (show get? M vn = some v from hM)).1 $$ H with ⟨Hv, Hrest⟩
  iframe Hv
  iintro %xs' %Hagree Hv'
  iapply (BigSepM.bigSepM_delete (show get? M vn = some v from hM)).2
  iframe Hv'
  iapply BigSepM.bigSepM_mono (fun {n p} hnp => ?_) $$ Hrest
  have hne : n ≠ vn := by
    intro e; subst e
    rw [LawfulPartialMap.get?_delete_eq rfl] at hnp; cases hnp
  obtain ⟨h1, h2, h3⟩ := Hagree n hne
  exact instOwn_congr γ xs xs' _ n p h1 h2 h3

/-- Take two distinct instances out, and put them back after changing the search state at the
first only. -/
theorem insts_acc2 (γ : ProtoNames) (xs : XS) (CM : GMap Node InstAttrs) (M : GMap Node Loc)
    (n1 n2 : Node) (p1 p2 : Loc) (h1 : M.lookup n1 = some p1) (h2 : M.lookup n2 = some p2)
    (hne : n1 ≠ n2) :
    ([∗map] n ↦ p ∈ M, instOwn (GF := GF) γ xs (CM.lookup n) n p) ⊢
      instOwn γ xs (CM.lookup n1) n1 p1 ∗ instOwn γ xs (CM.lookup n2) n2 p2 ∗
      ∀ xs' : XS, ⌜∀ n, n ≠ n1 → xs'.numF n = xs.numF n ∧
          xs'.lowF n = xs.lowF n ∧ (n ∈ xs'.1 ↔ n ∈ xs.1)⌝ -∗
        instOwn γ xs' (CM.lookup n1) n1 p1 -∗ instOwn γ xs (CM.lookup n2) n2 p2 -∗
        [∗map] n ↦ p ∈ M, instOwn γ xs' (CM.lookup n) n p := by
  iintro H
  have h2' : get? (delete M n1) n2 = some p2 := by
    rw [LawfulPartialMap.get?_delete_ne hne]; exact h2
  icases (BigSepM.bigSepM_delete (show get? M n1 = some p1 from h1)).1 $$ H with ⟨H1, Hrest⟩
  icases (BigSepM.bigSepM_delete h2').1 $$ Hrest with ⟨H2, Hrest⟩
  iframe H1 H2
  iintro %xs' %Hagree H1 H2
  iapply (BigSepM.bigSepM_delete (show get? M n1 = some p1 from h1)).2
  iframe H1
  iapply (BigSepM.bigSepM_delete h2').2
  isplitl [H2]
  · obtain ⟨a1, a2, a3⟩ := Hagree n2 (Ne.symm hne)
    iapply instOwn_congr γ xs xs' _ n2 p2 a1 a2 a3 $$ H2
  iapply BigSepM.bigSepM_mono (fun {n p} hnp => ?_) $$ Hrest
  have hn1 : n ≠ n1 := by
    intro e; subst e
    rw [LawfulPartialMap.get?_delete_ne (show n2 ≠ n from fun e => hne e.symm),
      LawfulPartialMap.get?_delete_eq rfl] at hnp; cases hnp
  obtain ⟨a1, a2, a3⟩ := Hagree n hn1
  exact instOwn_congr γ xs xs' _ n p a1 a2 a3

/-- The committed instances the executor knows: in the replica's committed map and in Gryff's
`insts`. -/
def knownC (γ : ProtoNames) (ρ : ReplNames) (C : GMap Node InstAttrs) : IProp GF :=
  iprop([∗map] n ↦ a ∈ C, ghostMapElem ρ.cm n DFrac.discard a ∗ instIs γ n a)

instance knownC_persistent (γ : ProtoNames) (ρ : ReplNames) (C : GMap Node InstAttrs) :
    Persistent (knownC (GF := GF) γ ρ C) := by unfold knownC; infer_instance

/-- The executor's known committed instances are in the replica's committed map. -/
theorem knownC_sub (γ : ProtoNames) (ρ : ReplNames) (C CM : GMap Node InstAttrs) :
    ⊢ knownC (GF := GF) γ ρ C -∗ ghostMapAuth ρ.cm 1 CM -∗ ⌜CSub C CM⌝ := by
  unfold knownC
  iintro #HC HCM
  ihave #HC' := BigSepM.bigSepM_mono (Ψ := fun n a => iprop(ghostMapElem ρ.cm n DFrac.discard a))
    (fun _ => sep_elim_left) $$ HC
  ihave %h := ghost_map_lookup_big C $$ HCM HC'
  ipureintro; exact h

/-- Adding a committed instance the executor learned. -/
theorem knownC_insert (γ : ProtoNames) (ρ : ReplNames) (C : GMap Node InstAttrs) (n : Node)
    (a : InstAttrs) (h : ∀ a', C.lookup n = some a' → a' = a) :
    knownC (GF := GF) γ ρ C ∗ ghostMapElem ρ.cm n DFrac.discard a ∗ instIs γ n a ⊢
      knownC γ ρ (GMap.insert n a C) := by
  unfold knownC
  iintro ⟨#HC, #Hn, #Hi⟩
  cases hn : C.lookup n with
  | some a' =>
    have := h a' hn; subst this
    rw [GMap.insert_id C n a' hn]
    iexact HC
  | none =>
    iapply (BigSepM.bigSepM_insert (show get? C n = none from hn)).2
    iframe #

/-- The stack's instances and their pointers. -/
def stackElems (ρ : ReplNames) (S : List Node) (ptrs : List Loc) : IProp GF :=
  iprop([∗list] i ↦ n ∈ S, ∃ p, ⌜ptrs[i]? = some p⌝ ∗ ghostMapElem ρ.ptrs n DFrac.discard p)

instance stackElems_persistent (ρ : ReplNames) (S : List Node) (ptrs : List Loc) :
    Persistent (stackElems (GF := GF) ρ S ptrs) := by unfold stackElems; infer_instance

theorem lockInvExec_open (γ : ProtoNames) (ρ : ReplNames) (isp : List GoSlice) (crt : GoSlice) :
    lockInvExec (GF := GF) γ ρ isp crt ⊣⊢ ∃ xs : XS, liAt γ ρ isp crt xs := .rfl

theorem knownC_open (γ : ProtoNames) (ρ : ReplNames) (C : GMap Node InstAttrs) :
    knownC (GF := GF) γ ρ C ⊣⊢
      [∗map] n ↦ a ∈ C, ghostMapElem ρ.cm n DFrac.discard a ∗ instIs γ n a := .rfl

/-- The package's `stack` holds the instances of `S` (bottom first). -/
def stackOwn (ρ : ReplNames) (S : List Node) : IProp GF :=
  iprop(∃ (s : GoSlice) (ptrs : List Loc), globalAddr gryff.stack ↦ s ∗ s ↦* ptrs ∗
    ownSliceCap Loc s (DFrac.own 1) ∗
    ⌜ptrs.length = S.length ∧ 0 < sint.Z s.cap ∧ sint.Z s.cap < 2 ^ 60⌝ ∗ stackElems ρ S ptrs)

theorem stackElems_push (ρ : ReplNames) (S : List Node) (ptrs : List Loc) (vn : Node) (v : Loc)
    (hlen : ptrs.length = S.length) :
    stackElems (GF := GF) ρ S ptrs ∗ ghostMapElem ρ.ptrs vn DFrac.discard v ⊢
      stackElems ρ (S ++ [vn]) (ptrs ++ [v]) := by
  unfold stackElems
  iintro ⟨HS, Hv⟩
  iapply BigSepL.bigSepL_snoc.2
  isplitl [HS]
  · iapply BigSepL.bigSepL_mono (fun {i n} hin => ?_) $$ HS
    iintro ⟨%p, %hp, Hp⟩
    iexists p; iframe Hp; ipureintro
    rw [List.getElem?_append_left (by have := (List.getElem?_eq_some_iff.1 hp).1; omega)]
    exact hp
  · iexists v; iframe Hv; ipureintro
    rw [List.getElem?_append_right (by omega), hlen, Nat.sub_self]; rfl

theorem stackOwn_intro (ρ : ReplNames) (S : List Node) (s : GoSlice) (ptrs : List Loc)
    (hlen : ptrs.length = S.length) (hcap : 0 < sint.Z s.cap ∧ sint.Z s.cap < 2 ^ 60) :
    globalAddr gryff.stack ↦ s ∗ s ↦* ptrs ∗ ownSliceCap Loc s (DFrac.own 1) ∗
      stackElems (GF := GF) ρ S ptrs ⊢ stackOwn ρ S := by
  unfold stackOwn
  iintro ⟨Hg, Hs, Hc, HS⟩
  iexists s, ptrs
  iframe
  ipureintro; exact ⟨hlen, hcap⟩

/-- `ExecedUpTo`: every instance up to it is executed. -/
def euOwn (euS : GoSlice) (X : List Node) : IProp GF :=
  iprop(∃ euv : List w32, euS ↦* euv ∗ ⌜euv.length = 3 ∧ ∀ (q : Nat) (e : w32), euv[q]? = some e →
    -1 ≤ sint.Z e ∧ ∀ i : Int, 0 ≤ i → i ≤ sint.Z e → ((q : Int), i) ∈ X⌝)

theorem stackOwn_open (ρ : ReplNames) (S : List Node) :
    stackOwn (GF := GF) ρ S ⊣⊢ ∃ (s : GoSlice) (ptrs : List Loc), globalAddr gryff.stack ↦ s ∗
      s ↦* ptrs ∗ ownSliceCap Loc s (DFrac.own 1) ∗
      ⌜ptrs.length = S.length ∧ 0 < sint.Z s.cap ∧ sint.Z s.cap < 2 ^ 60⌝ ∗
      stackElems ρ S ptrs := .rfl

theorem euOwn_open (euS : GoSlice) (X : List Node) :
    euOwn (GF := GF) euS X ⊣⊢ ∃ euv : List w32, euS ↦* euv ∗
      ⌜euv.length = 3 ∧ ∀ (q : Nat) (e : w32), euv[q]? = some e →
        -1 ≤ sint.Z e ∧ ∀ i : Int, 0 ≤ i → i ≤ sint.Z e → ((q : Int), i) ∈ X⌝ := .rfl

/-- `PrevValTag`: the last result of the executed RMWs, at key 0. -/
def pvtOwn (pvt : Loc) (ents : List ExecEntry) : IProp GF :=
  iprop(∃ pm : GMap w64 gryffproto.ValTag, pvt ↦$ pm ∗
    ⌜(∀ kk, kk ≠ W64 0 → pm.lookup kk = none) ∧ (pm.lookup (W64 0)).map vtOfGo = lastRes ents⌝)

end defs

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [gryff_sem : gryff.src.gryff.Assumptions]

open gryff.src

set_option goose.wp.extras true

/-- Reading one of an instance's deps (`v.Deps[q]`). -/
theorem wp_load_inst_dep (p : Loc) (iv : gryff.Instance) (j : Int) (d : w32) (hj : 0 ≤ j)
    (hd : iv.Deps'.arr[j.toNat]? = some d) :
    {{ (p ↦ iv : IProp GF) }}
      (App (Val (GoInstruction (GoLoad go.int32)))
        (Val #(arrayIndexRef w32 j (p.[gryff.Instance, go!"Deps"]))))
    {{ RET #d; p ↦ iv }} := by
  wp_start as Hp
  icases typedPointsto_not_null_dup _ _ _ $$ Hp with ⟨Hp, %Hnn⟩
  iStructNamed Hp
  icases array_acc _ j _ 5 iv.Deps' d hj hd $$ Deps with ⟨Hd, Hclose⟩
  wp_apply IntoValTyped.wp_load (t := go.int32) _ _ _ $$ Hd as Hd
  ihave Deps := Hclose $$ %d Hd
  rw [list_set_getElem?_self _ _ _ hd] at *
  iapply HΦ
  iapply typedPointsto_combine _ _ _ Hnn
  simp only [TypedPointsto.typedPointstoDef]
  iFrameNamed

end lemmas

end Perennial.gryff.replica
