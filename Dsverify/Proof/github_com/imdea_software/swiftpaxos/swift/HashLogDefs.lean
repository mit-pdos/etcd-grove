/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/HashLogDefs.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
`HashLog` (swift/dpath.go) as a pure record and its representation predicate (internal to the
replica group; not frozen).

* `HL`: `synced` (the highest synced sequence number, `-1` none), `base` (the path whose hash is
  `syncedHash`, `[]` while `synced < 0`), `pending` (the pending commands' ids, in the linked
  list's order), `upd` (`pendingUpd`: an id's saved update, a sequence number, a hash and the
  path the hash is of).
* `ownHashLog l σ`: the `*HashLog` at `l` is `σ`: its struct, the two maps, the doubly linked
  list of pending nodes (`dseg`), and the hash facts: `syncedHash` is the start-marked hash of
  `base` (`startHash`, Proof/swift/ChainHash.lean) once `synced ≥ 0`; `hash` is the start-marked
  hash of `base ++ pending` while `pending` is not empty; each saved update's hash is of its path.
* `dseg ns p n`: the nodes `ns` (locations and ids) linked in order, the first's `previous`
  `p`, the last's `next` `n`.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.HashLeafDefs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.HashLogKey

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

namespace swift.hlog

/-- A saved update (`pendingUpd`'s entry): its sequence number, its hash, the path hashed. -/
structure UpdE where
  seq : w64
  hash : sp.Hash
  path : List sp.CmdId

/-- A `HashLog`'s state (see the file header). -/
structure HL where
  synced : w64
  base : List sp.CmdId
  pending : List sp.CmdId
  upd : sp.CmdId → Option UpdE

/-- A fresh log (`NewHashLog`). -/
def HL.init : HL := ⟨W64 (-1), [], [], fun _ => none⟩

/-- The first node's location, or `d`. -/
def firstL (ns : List (Loc × swift.CommandId)) (d : Loc) : Loc := (ns.head?.map Prod.fst).getD d
/-- The last node's location, or `d`. -/
def lastL (ns : List (Loc × swift.CommandId)) (d : Loc) : Loc :=
  (ns.getLast?.map Prod.fst).getD d

@[simp] theorem firstL_nil (d : Loc) : firstL [] d = d := rfl
@[simp] theorem firstL_cons (p : Loc × swift.CommandId) (r) (d : Loc) : firstL (p :: r) d = p.1 :=
  rfl
@[simp] theorem lastL_nil (d : Loc) : lastL [] d = d := rfl
theorem lastL_cons (p : Loc × swift.CommandId) (r) (d : Loc) : lastL (p :: r) d = lastL r p.1 := by
  unfold lastL
  rw [List.getLast?_cons]
  cases r.getLast? <;> simp
theorem firstL_append (A B : List (Loc × swift.CommandId)) (d : Loc) :
    firstL (A ++ B) d = firstL A (firstL B d) := by
  cases A <;> simp
theorem lastL_append (A B : List (Loc × swift.CommandId)) (d : Loc) :
    lastL (A ++ B) d = lastL B (lastL A d) := by
  unfold lastL
  rw [List.getLast?_append]
  cases hB : B.getLast? <;> simp
@[simp] theorem lastL_snoc (A : List (Loc × swift.CommandId)) (p : Loc × swift.CommandId)
    (d : Loc) : lastL (A ++ [p]) d = p.1 := by
  simp [lastL]

theorem firstL_mem (ns : List (Loc × swift.CommandId)) (d : Loc) (h : ns ≠ []) :
    firstL ns d ∈ ns.map Prod.fst := by
  obtain ⟨p, r, rfl⟩ := List.exists_cons_of_ne_nil h; simp

theorem lastL_mem (ns : List (Loc × swift.CommandId)) (d : Loc) (h : ns ≠ []) :
    lastL ns d ∈ ns.map Prod.fst := by
  obtain ⟨A, p, rfl⟩ := (sp.eq_nil_or_snoc ns).resolve_left h; simp

/-- The pending list's tail pointer: nil when empty, nil or the node with one node, the last node
with two or more. -/
def tailOk (ns : List (Loc × swift.CommandId)) (tail : Loc) : Prop :=
  (ns = [] → tail = null) ∧ (ns.length = 1 → tail = null ∨ tail = lastL ns null) ∧
    (2 ≤ ns.length → tail = lastL ns null)

theorem tailOk_last (ns : List (Loc × swift.CommandId)) (h : ns ≠ []) :
    tailOk ns (lastL ns null) :=
  ⟨fun h0 => absurd h0 h, fun _ => Or.inr rfl, fun _ => rfl⟩

/-- The id map of the nodes. -/
def lookupN (ns : List (Loc × swift.CommandId)) (k : swift.CommandId) : Option Loc :=
  (ns.find? (fun p => decide (p.2 = k))).map Prod.fst

theorem lookupN_snoc (ns : List (Loc × swift.CommandId)) (a : Loc) (x : swift.CommandId)
    (hx : x ∉ ns.map Prod.snd) (k : swift.CommandId) :
    lookupN (ns ++ [(a, x)]) k = if k = x then some a else lookupN ns k := by
  unfold lookupN
  rw [List.find?_append]
  by_cases hk : k = x
  · subst hk
    have : ns.find? (fun p => decide (p.2 = k)) = none := by
      rw [List.find?_eq_none]; intro p hp hpk
      exact hx (List.mem_map.mpr ⟨p, hp, by simpa using hpk⟩)
    simp [this]
  · simp only [if_neg hk]
    cases h : ns.find? (fun p => decide (p.2 = k)) with
    | some p => simp
    | none => simp [List.find?, Ne.symm hk]

theorem ids_of_pending (ns : List (Loc × swift.CommandId)) (pend : List sp.CmdId)
    (h : ns.map (fun p => toCmdId p.2) = pend) (x : swift.CommandId) (hx : toCmdId x ∉ pend) :
    x ∉ ns.map Prod.snd := by
  intro hm; apply hx; rw [← h]
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hm
  exact List.mem_map.mpr ⟨p, hp, rfl⟩

theorem lookupN_some (ns : List (Loc × swift.CommandId)) (k : swift.CommandId) (a : Loc)
    (h : lookupN ns k = some a) : ∃ A B, ns = A ++ (a, k) :: B := by
  unfold lookupN at h
  cases hf : ns.find? (fun p => decide (p.2 = k)) with
  | none => simp [hf] at h
  | some p =>
    simp only [hf, Option.map_some, Option.some.injEq] at h
    have hm := List.mem_of_find?_eq_some hf
    have hk := List.find?_some hf
    simp only [decide_eq_true_eq] at hk
    obtain ⟨A, B, hAB⟩ := List.append_of_mem hm
    refine ⟨A, B, ?_⟩
    rw [hAB]; obtain ⟨p1, p2⟩ := p; simp only at h hk; subst h hk; rfl

theorem lookupN_none (ns : List (Loc × swift.CommandId)) (k : swift.CommandId)
    (h : lookupN ns k = none) : k ∉ ns.map Prod.snd := by
  unfold lookupN at h
  intro hm
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hm
  have : (ns.find? (fun q => decide (q.2 = p.2))).isSome := by
    rw [List.find?_isSome]; exact ⟨p, hp, by simp⟩
  cases hf : ns.find? (fun q => decide (q.2 = p.2)) with
  | none => simp [hf] at this
  | some q => simp [hf] at h

theorem lookupN_remove (A B : List (Loc × swift.CommandId)) (a : Loc) (x : swift.CommandId)
    (hnd : ((A ++ (a, x) :: B).map Prod.snd).Nodup) (k : swift.CommandId) :
    lookupN (A ++ B) k = if k = x then none else lookupN (A ++ (a, x) :: B) k := by
  have hA : x ∉ A.map Prod.snd := by
    intro h; simp only [List.map_append, List.map_cons] at hnd
    exact (List.nodup_append.mp hnd).2.2 x h x (by simp) rfl
  have hB : x ∉ B.map Prod.snd := by
    intro h; simp only [List.map_append, List.map_cons] at hnd
    exact (List.nodup_cons.mp (List.nodup_append.mp hnd).2.1).1 h
  unfold lookupN
  by_cases hk : k = x
  · subst hk; simp only [if_pos rfl]
    rw [List.find?_append]
    have e1 : A.find? (fun p => decide (p.2 = k)) = none := by
      rw [List.find?_eq_none]; intro p hp hpk
      exact hA (List.mem_map.mpr ⟨p, hp, by simpa using hpk⟩)
    have e2 : B.find? (fun p => decide (p.2 = k)) = none := by
      rw [List.find?_eq_none]; intro p hp hpk
      exact hB (List.mem_map.mpr ⟨p, hp, by simpa using hpk⟩)
    simp [e1, e2]
  · simp only [if_neg hk, List.find?_append, List.find?_cons]
    have : decide (x = k) = false := by simp [Ne.symm hk]
    simp [this]

theorem nodup_of_map {α β : Type} (f : α → β) (l : List α) (h : (l.map f).Nodup) : l.Nodup := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.nodup_cons] at h ⊢
    exact ⟨fun ha => h.1 (List.mem_map_of_mem ha), ih h.2⟩

theorem erase_mid {α β : Type} [DecidableEq β] (f : α → β) (A B : List α) (p : α)
    (hA : f p ∉ A.map f) : ((A ++ p :: B).map f).erase (f p) = (A ++ B).map f := by
  simp only [List.map_append, List.map_cons]
  rw [List.erase_append_right _ hA, List.erase_cons_head]

section defs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics]
variable [swift.Assumptions]

/-- The nodes `ns` linked in order, the first's `previous` `p`, the last's `next` `n`. -/
def dseg : List (Loc × swift.CommandId) → Loc → Loc → IProp netDistGF
  | [], _, _ => iprop(True)
  | (l, x) :: r, p, n => iprop(⌜l ≠ null⌝ ∗ l ↦ swift.HashNode.mk x (firstL r n) p ∗ dseg r l n)

/-- The saved updates: each entry's (read-only) struct and hash slice, the hash of its path. -/
def updsOk (σ : HL) (upds : GMap swift.CommandId Loc) : IProp netDistGF :=
  iprop(⌜∀ k, (upds !! k).isSome = (σ.upd (toCmdId k)).isSome⌝ ∗
    □ ∀ (k : swift.CommandId) (u : Loc), ⌜upds !! k = some u⌝ -∗
      ∃ (e : UpdE) (sl : GoSlice), ⌜σ.upd (toCmdId k) = some e ∧ e.hash.length = 32⌝ ∗
        u ↦□ swift.UpdateEntry.mk sl e.seq ∗
        sl ↦*□ [swift.SHash.mk (GoArray.mk e.hash)] ∗ sp.startHash e.path e.hash)

instance updsOk_persistent (σ : HL) (upds : GMap swift.CommandId Loc) :
    Persistent (updsOk σ upds) := by unfold updsOk; infer_instance

/-- `syncedHash` is the hash of `base` once `synced ≥ 0`. -/
def syncOk (σ : HL) (sh : sp.Hash) : IProp netDistGF :=
  if 0 ≤ sint.Z σ.synced then sp.startHash σ.base sh else iprop(⌜σ.base = []⌝)

/-- `hash` is the hash of `base ++ pending` while some command is pending. -/
def hashOk (σ : HL) (h : sp.Hash) : IProp netDistGF :=
  iprop(⌜σ.pending = []⌝ ∨ sp.startHash (σ.base ++ σ.pending) h)

instance syncOk_persistent (σ : HL) (sh : sp.Hash) : Persistent (syncOk σ sh) := by
  unfold syncOk; split <;> infer_instance
instance hashOk_persistent (σ : HL) (h : sp.Hash) : Persistent (hashOk σ h) := by
  unfold hashOk; infer_instance

/-- The `*HashLog` at `l` is `σ` (see the file header). -/
def ownHashLog (l : Loc) (σ : HL) : IProp netDistGF :=
  iprop(∃ (sh h : GoArray w8 32) (head tail nm um : Loc) (ns : List (Loc × swift.CommandId))
      (nodes upds : GMap swift.CommandId Loc),
    l ↦ swift.HashLog.mk σ.synced (swift.SHash.mk sh) head tail (swift.SHash.mk h) nm um ∗
    nm ↦$ nodes ∗ um ↦$ upds ∗ dseg ns null null ∗ updsOk σ upds ∗
    ⌜sh.arr.length = 32 ∧ h.arr.length = 32 ∧ -1 ≤ sint.Z σ.synced ∧
      ns.map (fun p => toCmdId p.2) = σ.pending ∧ (ns.map Prod.fst).Nodup ∧
      σ.pending.Nodup ∧ head = firstL ns null ∧ tailOk ns tail ∧
      ∀ k, nodes !! k = lookupN ns k⌝ ∗
    syncOk σ sh.arr ∗ hashOk σ h.arr)

/-- `ownHashLog`'s introduction from its parts. -/
theorem ownHashLog_intro (l : Loc) (σ : HL) (sh h : GoArray w8 32) (head tail nm um : Loc)
    (ns : List (Loc × swift.CommandId)) (nodes upds : GMap swift.CommandId Loc)
    (hp : sh.arr.length = 32 ∧ h.arr.length = 32 ∧ -1 ≤ sint.Z σ.synced ∧
      ns.map (fun p => toCmdId p.2) = σ.pending ∧ (ns.map Prod.fst).Nodup ∧
      σ.pending.Nodup ∧ head = firstL ns null ∧ tailOk ns tail ∧
      ∀ k, nodes !! k = lookupN ns k) :
    l ↦ swift.HashLog.mk σ.synced (swift.SHash.mk sh) head tail (swift.SHash.mk h) nm um ∗
      nm ↦$ nodes ∗ um ↦$ upds ∗ dseg ns null null ∗ updsOk σ upds ∗ syncOk σ sh.arr ∗
      hashOk σ h.arr ⊢ ownHashLog l σ := by
  iintro ⟨Hl, Hnm, Hum, Hns, Hu, Hs, Hh⟩
  unfold ownHashLog
  iexists sh, h, head, tail, nm, um, ns, nodes, upds
  iframe; ipureintro; exact hp

/-- Clearing the saved update of `x` (`delete(pendingUpd, x)`). -/
def HL.clearUpd (σ : HL) (x : sp.CmdId) : HL :=
  { σ with upd := fun y => if y = x then none else σ.upd y }

@[simp] theorem HL.clearUpd_synced (σ : HL) (x : sp.CmdId) : (σ.clearUpd x).synced = σ.synced := rfl
@[simp] theorem HL.clearUpd_base (σ : HL) (x : sp.CmdId) : (σ.clearUpd x).base = σ.base := rfl
@[simp] theorem HL.clearUpd_pending (σ : HL) (x : sp.CmdId) :
    (σ.clearUpd x).pending = σ.pending := rfl

theorem updsOk_delete (σ : HL) (upds : GMap swift.CommandId Loc) (x : swift.CommandId) :
    updsOk σ upds ⊢ updsOk (σ.clearUpd (toCmdId x)) (GMap.delete x upds) := by
  unfold updsOk
  iintro ⟨%Hk, #H⟩
  isplitr
  · ipureintro; intro k
    by_cases hk : k = x
    · subst hk; simp [HL.clearUpd]
    · have : toCmdId k ≠ toCmdId x := fun e => hk (by
        have := congrArg ofCmdId e; simpa using this)
      simp only [HL.clearUpd, GMap.lookup_delete_ne _ (Ne.symm hk), if_neg this]; exact Hk k
  imodintro
  iintro %k %u %Hu
  by_cases hk : k = x
  · subst hk; rw [GMap.lookup_delete] at Hu; cases Hu
  · have : toCmdId k ≠ toCmdId x := fun e => hk (by
      have := congrArg ofCmdId e; simpa using this)
    rw [GMap.lookup_delete_ne _ (Ne.symm hk)] at Hu
    ihave ⟨%e, %sl, %He, H1, H2, H3⟩ := H $$ %k %u %Hu
    iexists e, sl; iframe H1 H2 H3; ipureintro
    simp only [HL.clearUpd, if_neg this]; exact He

theorem syncOk_clearUpd (σ : HL) (x : sp.CmdId) (sh : sp.Hash) :
    syncOk (σ.clearUpd x) sh = syncOk σ sh := rfl
theorem hashOk_clearUpd (σ : HL) (x : sp.CmdId) (h : sp.Hash) :
    hashOk (σ.clearUpd x) h = hashOk σ h := rfl

/-- The recomputation's accumulator (`update`'s loop): after the nodes `D`, `initial` is
`syncedHash` (and `started` whether `synced ≥ 0`) if `D` is empty, else the start-marked hash of
`base ++ D`. -/
def accOk (σ : HL) (sh : sp.Hash) (D : List sp.CmdId) (ini : sp.Hash) (st : Bool) :
    IProp netDistGF :=
  if D = [] then iprop(⌜ini = sh ∧ st = decide (0 ≤ sint.Z σ.synced)⌝)
  else iprop(⌜st = true⌝ ∗ sp.startHash (σ.base ++ D) ini)

instance accOk_persistent (σ : HL) (sh : sp.Hash) (D : List sp.CmdId) (ini : sp.Hash) (st : Bool) :
    Persistent (accOk σ sh D ini st) := by
  unfold accOk; split <;> infer_instance

/-- One round of the recomputation (`chain`). -/
theorem accOk_step (σ : HL) (sh : sp.Hash) (D : List sp.CmdId) (ini h' : sp.Hash) (st : Bool)
    (x : sp.CmdId) :
    syncOk σ sh ∗ accOk σ sh D ini st ∗ sp.hashOf ((if st then ini else []) ++ sp.encCmdId x) h' ⊢
      accOk σ sh (D ++ [x]) h' true := by
  unfold accOk
  rw [ite_cond_eq_false _ _ (eq_false (show ¬ (D ++ [x] = []) by simp))]
  by_cases hD : D = []
  · subst hD
    rw [ite_cond_eq_true _ _ (eq_true (rfl : ([] : List sp.CmdId) = []))]
    iintro ⟨Hs, ⟨%Hi, %Hst⟩, Hh⟩
    subst Hi Hst
    isplitr
    · ipureintro; rfl
    rw [List.nil_append]
    unfold syncOk
    by_cases hs : 0 ≤ sint.Z σ.synced
    · rw [if_pos hs, decide_eq_true hs]
      simp only [↓reduceIte]
      iapply sp.startHash_snoc; iframe
    · rw [if_neg hs, decide_eq_false hs]
      simp only [Bool.false_eq_true, ↓reduceIte, List.nil_append]
      icases Hs with %Hb
      rw [Hb, List.nil_append]
      iapply sp.startHash_single; iexact Hh
  · rw [ite_cond_eq_false _ _ (eq_false hD)]
    iintro ⟨-, ⟨%Hst, Ha⟩, Hh⟩
    subst Hst
    isplitr
    · ipureintro; rfl
    simp only [↓reduceIte]
    rw [← List.append_assoc]
    iapply sp.startHash_snoc; iframe

/-- The recomputation's result: `hash` for the pending list `D`. -/
theorem accOk_done (σ : HL) (sh : sp.Hash) (ini : sp.Hash) (st : Bool) :
    accOk σ sh σ.pending ini st ⊢ hashOk σ ini := by
  unfold accOk hashOk
  by_cases hD : σ.pending = []
  · rw [if_pos hD]; iintro -; ileft; ipureintro; exact hD
  · rw [if_neg hD]; iintro ⟨-, H⟩; iright; iexact H

/-! ## `dseg` laws -/

theorem dseg_nil (p n : Loc) : dseg [] p n = iprop(True) := rfl
theorem dseg_cons (l : Loc) (x : swift.CommandId) (r : List (Loc × swift.CommandId)) (p n : Loc) :
    dseg ((l, x) :: r) p n =
      iprop(⌜l ≠ null⌝ ∗ l ↦ swift.HashNode.mk x (firstL r n) p ∗ dseg r l n) := rfl

theorem dseg_app (A B : List (Loc × swift.CommandId)) (p n : Loc) :
    dseg (A ++ B) p n ⊣⊢ dseg A p (firstL B n) ∗ dseg B (lastL A p) n := by
  induction A generalizing p with
  | nil =>
    simp only [List.nil_append, lastL_nil, dseg_nil]
    exact ⟨by iintro H; iframe H, by iintro ⟨-, H⟩; iexact H⟩
  | cons q A ih =>
    obtain ⟨l, x⟩ := q
    simp only [List.cons_append, dseg_cons]
    rw [lastL_cons, firstL_append]
    constructor
    · iintro ⟨%Hl, Hn, H⟩
      ihave ⟨HA, HB⟩ := (ih l).1 $$ H
      iframe HB; iframe HA Hn; ipureintro; exact Hl
    · iintro ⟨⟨%Hl, Hn, HA⟩, HB⟩
      iframe Hn; isplitr
      · ipureintro; exact Hl
      iapply (ih l).2; iframe

theorem dseg_one (l : Loc) (x : swift.CommandId) (p n : Loc) :
    dseg [(l, x)] p n ⊣⊢ ⌜l ≠ null⌝ ∗ l ↦ swift.HashNode.mk x n p := by
  rw [dseg_cons, dseg_nil, firstL_nil]
  exact ⟨by iintro ⟨%H, Hn, -⟩; iframe Hn; ipureintro; exact H,
    by iintro ⟨%H, Hn⟩; iframe Hn; ipureintro; exact H⟩

/-- A node in the middle: its neighbours' pointers to it. -/
theorem dseg_mid (A B : List (Loc × swift.CommandId)) (l : Loc) (x : swift.CommandId)
    (p n : Loc) :
    dseg (A ++ (l, x) :: B) p n ⊣⊢
      dseg A p l ∗ (⌜l ≠ null⌝ ∗ l ↦ swift.HashNode.mk x (firstL B n) (lastL A p) ∗
        dseg B l n) := by
  have h := dseg_app A ((l, x) :: B) p n
  rw [firstL_cons, dseg_cons] at h
  exact h

theorem loc_def_ent (a v : Loc) (dq : DFrac) :
    (typedPointstoDef (GF := netDistGF) a v dq) ⊢ heapPointsto a dq #v := .rfl

/-- Two full points-tos of a node at one location: impossible. -/
theorem hashNode_excl (a : Loc) (v w : swift.HashNode) :
    (a ↦ v : IProp netDistGF) ∗ a ↦ w ⊢ False := by
  iintro ⟨H1, H2⟩
  iStructNamedSuffix H1 "1"
  iStructNamedSuffix H2 "2"
  icases typedPointsto_split _ _ _ $$ next1 with N1
  icases typedPointsto_split _ _ _ $$ next2 with N2
  ihave N1' : (heapPointsto (structFieldRef swift.HashNode go!"next" a) (DFrac.own 1) #v.next' : IProp netDistGF) $$ [N1]
  · iapply loc_def_ent; iexact N1
  ihave N2' : (heapPointsto (structFieldRef swift.HashNode go!"next" a) (DFrac.own 1) #w.next' : IProp netDistGF) $$ [N2]
  · iapply loc_def_ent; iexact N2
  icombine N1' N2' gives %Hv
  exfalso; have := DFrac.valid_own_op Hv.1; simp at this

/-- A fresh node is none of a segment's. -/
theorem dseg_fresh (a : Loc) (v : swift.HashNode) (ns : List (Loc × swift.CommandId)) (p n : Loc) :
    (a ↦ v : IProp netDistGF) ∗ dseg ns p n ⊢ a ↦ v ∗ dseg ns p n ∗ ⌜a ∉ ns.map Prod.fst⌝ := by
  induction ns generalizing p with
  | nil => iintro ⟨H, D⟩; iframe H D; ipureintro; simp
  | cons q r ih =>
    obtain ⟨l, x⟩ := q
    rw [dseg_cons]
    iintro ⟨H, %Hl, Hn, D⟩
    ihave ⟨H, D, %Hr⟩ := ih l $$ [$H $D]
    by_cases hal : a = l
    · subst hal; iexfalso; iapply hashNode_excl $$ [$H $Hn]
    iframe H Hn D; isplitr
    · ipureintro; exact Hl
    ipureintro; simp only [List.map_cons, List.mem_cons, not_or]; exact ⟨hal, Hr⟩

/-- The nodes are non-null. -/
theorem dseg_nonnull (ns : List (Loc × swift.CommandId)) (p n : Loc) :
    dseg ns p n ⊢ dseg ns p n ∗ ⌜null ∉ ns.map Prod.fst⌝ := by
  induction ns generalizing p with
  | nil => iintro H; iframe H; ipureintro; simp
  | cons q r ih =>
    obtain ⟨l, x⟩ := q
    rw [dseg_cons]
    iintro ⟨%Hl, Hn, H⟩
    ihave ⟨H, %Hr⟩ := ih l $$ H
    iframe Hn H; isplitr
    · ipureintro; exact Hl
    ipureintro; simp only [List.map_cons, List.mem_cons, not_or]; exact ⟨Ne.symm Hl, Hr⟩

end defs

end swift.hlog

end Perennial.github_com.imdea_software.swiftpaxos
