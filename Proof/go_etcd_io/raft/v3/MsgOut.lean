/-
**The objects a `Ready` hands out** (raft-entsize §2 step 3, 2026-11-09).

- `snapUf l st`: a `MsgSnap`'s top-level unknown fields are none (persistent): the `pbMsg` of the
  literal `maybeSendSnapshot` builds (`msgOwn_lit_uf`), which `raft.send` takes and the outbox keeps
  beside the message (`msgQ`), so that the content a `Ready` hands out can pin them
  (`msgPtsC_msgPtsCC_uf`: a message's content form may take its `pbMsg` from anywhere).
- `outObjR γ m c`, `outEntR γ e c`: persistent elements of the cluster's monotone set of the objects
  handed out (`RaftNames.out`, its authority in `raftOutInv`, part of the commit invariant), at the
  content they were handed out with. A message's element is keyed by its own fields and its
  responses' pointers (`outKey`): what the size law reads of it (`msgSizeOk` requires no responses).
  Raft's `Ready` proofs insert them (`raftOutInv_insert`, internal, `MsgOutIns.lean`).
- `msgOutR γ l dq st`: a message handed out at `dq` holding `st`, at a content `c` raft pinned
  (`sentOk`: its snapshot's conf state without unknown fields, a `MsgSnap` without top-level unknown
  fields), with its element `outObjR γ l c`.
-/
module

public import Proof.go_etcd_io.raft.v3.PbContentOwn
public import Proof.go_etcd_io.raft.v3.PbSized
public import Proof.go_etcd_io.raft.v3.Protocol.GhostState

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

/-! ## Countable contents (the set's keys) -/

section countable
variable [GooseExts]

instance EntryC.countable : Pos.Countable EntryC :=
  .ofInjective (fun c => Pos.Countable.encode (c.term, c.index, c.type, c.data, c.uf))
    (fun a b h => by
      have h := Pos.encode_inj h
      cases a; cases b
      simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h
      rfl)

instance CSC.countable : Pos.Countable CSC :=
  .ofInjective (fun c => Pos.Countable.encode
      (c.voters, c.learners, c.votersOutgoing, c.learnersNext, c.autoLeave, c.uf))
    (fun a b h => by
      have h := Pos.encode_inj h
      cases a; cases b
      simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := h
      rfl)

instance SnapMetaC.countable : Pos.Countable SnapMetaC :=
  .ofInjective (fun c => Pos.Countable.encode (c.confState, c.index, c.term, c.uf))
    (fun a b h => by
      have h := Pos.encode_inj h
      cases a; cases b
      simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h
      rfl)

instance SnapC.countable : Pos.Countable SnapC :=
  .ofInjective (fun c => Pos.Countable.encode (c.data, c.metadata, c.uf))
    (fun a b h => by
      have h := Pos.encode_inj h
      cases a; cases b
      simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      rfl)

instance MsgFC.countable : Pos.Countable MsgFC :=
  .ofInjective (fun c => Pos.Countable.encode
      ((c.type, c.to, c.frm, c.term, c.logTerm, c.index, c.entries),
       (c.commit, c.vote, c.snapshot, c.reject, c.rejectHint, c.context, c.uf)))
    (fun a b h => by
      have h := Pos.encode_inj h
      cases a; cases b
      simp only [Prod.mk.injEq] at h
      obtain ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩ := h
      rfl)

/-- **The handed-out set's key** of an object and its content: a message's own fields and its
responses' pointers (what the size law reads of it: `msgSizeOk` requires no responses, and reads
only the message's own fields), an entry's content. -/
def outKey : Sum (Loc × MsgC) (Loc × EntryC) → Sum (Loc × MsgFC × List Loc) (Loc × EntryC)
  | .inl (m, c) => .inl (m, c.f, c.resps.map Prod.fst)
  | .inr x => .inr x

end countable

/-! ## The size predicate (raft-entsize §1)

Measured over the byte content raft never changes (its scalar rewrites, `To`/`From`/`Term` on a
forward, an entry's `Term`/`Index` on append, a fresh header around an echoed `Context`, leave it
as it is), plus a framed sum over the entries; `msgSizeOk_size` (rafthttp, a later step) bounds
protobuf's size by it. -/

section size
variable [GooseExts]

/-- An optional snapshot's encoded size (`0` for none). -/
def optSnapSize : Option SnapC → Nat
  | none => 0
  | some s => snapSize s

/-- **A message's header bytes**: its `Context`, its own unknown fields and its `Snapshot` (a
non-snapshot message's included: raft forwards it whole). -/
def hdrBytes (c : MsgC) : Nat :=
  (c.f.context.getD []).length + c.f.uf.length + optSnapSize c.f.snapshot

/-- **A message's content is of bounded size**: no responses, its header bytes and each entry's
bytes at most `2^31` (`entBytesMax`), and its entries' framed sum at most `2^36`. -/
def msgSizeOk (c : MsgC) : Prop :=
  c.resps = [] ∧ hdrBytes c ≤ entBytesMax ∧ (∀ e ∈ c.f.entries, entBytes e ≤ entBytesMax) ∧
    (c.f.entries.map (fun e => entBytes e + 64)).sum ≤ 2 ^ 36

/-- **The size law's conclusion** of an element of the handed-out set: a message, unless a
`MsgSnap` (sent by `msgSnapC`, never through the stream writer), is `msgSizeOk`; an entry is
`entSizeOk`. -/
def outSizeOk : Sum (Loc × MsgC) (Loc × EntryC) → Prop
  | .inl (_, c) => c.model.msg.Type' ≠ MsgSnap → msgSizeOk c
  | .inr (_, e) => entSizeOk e

end size

/-! ## The predicates -/

section generic
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **A `MsgSnap`'s top-level unknown fields are none** (persistent; `emp`-like for any other type):
the `pbMsg` of the literal `maybeSendSnapshot` builds.

**The condition (etcd-grove-82, 2026-11-09).** The right disjunct is *the object's own* hidden-field
invariant, the one allocated at `maybeSendSnapshot`'s literal (`msgOwn_of_struct_uf`, through
`pbMsg_alloc` with `uf = []` from the fresh struct `l ↦ v`), never a second fact about an object
whose invariant could hold other unknown fields: `pbMsg T l uf` is an invariant owning `l`'s hidden
fields whole (`state`, `sizeCache`, `unknownFields ↦ us ∗ us ↦* uf`), and `pbMsg_alloc` is its only
producer, consuming that whole ownership, which exists only for a fresh struct; so an object has at
most one, and its `uf` is the object's. A received object (`stepIn`, `RawNode.Step`) already has its
invariant, at bytes no proof knows, inside `msgPtsC`'s existential: it can get only the left disjunct,
and `raft.send` takes the right one only for a `MsgSnap`, which raft builds only at that literal
(a received `MsgSnap` is restored, never re-sent). The content a `Ready` pins takes its `uf` from
this invariant (`msgOwn_snapUf_CC`, `msgPtsC_msgPtsCC_uf`), not from the message's `msgOwn`. -/
def snapUfT (l : Loc) (ty : w32) : IProp GF :=
  iprop(⌜ty ≠ MsgSnap⌝ ∨ pbMsg raftpb.Message l [])

instance snapUfT_persistent (l : Loc) (ty : w32) : Persistent (snapUfT (GF := GF) l ty) := by
  unfold snapUfT; infer_instance

/-- `snapUfT` at a message's type. -/
abbrev snapUf (l : Loc) (st : MsgSt) : IProp GF := snapUfT l st.msg.Type'

/-- **An element of the handed-out set** (persistent): the object and content `x`, by its key.
(out_size C2, the Scope's D1) It carries the size law's conclusion: in a cluster with a bound on
proposed data, `x` is of bounded size (`outSizeOk`), which raft's `Ready` proofs establish at
insertion (`raftOutInv_insert`). -/
def outSetR (γ : RaftNames) (x : Sum (Loc × MsgC) (Loc × EntryC)) : IProp GF :=
  iprop(ghostMapElem γ.out (Pos.Countable.encode (outKey x)) DFrac.discard () ∗
    ⌜∀ b, γ.maxData = some b → outSizeOk x⌝)

instance outSetR_persistent (γ : RaftNames) (x : Sum (Loc × MsgC) (Loc × EntryC)) :
    Persistent (outSetR (GF := GF) γ x) := by
  unfold outSetR; infer_instance

/-- The message `m` was handed out at the content `c`. -/
abbrev outObjR (γ : RaftNames) (m : Loc) (c : MsgC) : IProp GF := outSetR γ (.inl (m, c))

/-- The entry `e` was handed out at the content `c`. -/
abbrev outEntR (γ : RaftNames) (e : Loc) (c : EntryC) : IProp GF := outSetR γ (.inr (e, c))

/-- **The size law of the handed-out objects** (raft-entsize §2): in a cluster with a bound on
proposed data (`RaftNames.maxData = some b`), every object a `Ready` handed out, at the content it
was handed out with, is of bounded size (`outSizeOk`: a message but a `MsgSnap` `msgSizeOk`, an entry
`entSizeOk`).

**Proof** (out_size, 2026-11-12): by the element's definition (`outSetR` carries the fact). The
work is at insertion: `raftOutInv_insert` takes the fact (`Hsz`), which raft's two hand-outs derive
from its log and outbox invariants on objects (`entsROz`, `msgQC`).

**Why it is true of Go.** Raft builds its own messages with no unknown fields and no responses;
their entries are its log's entry objects, whose content comes from proposals (at most `b`, the
node API's `Propose`/`ReadIndex` premises), raft-internal constants, the storage (sized and cut by
the storage contract when the cluster bounds proposed data, `isStorage`) and stepped messages
(`msgSizeOk` by `stepIn_intro`'s and `RawNode.Step`'s premise); it re-emits received objects only
after changing their scalar fields, which the measure does not count (`hdrBytes`, `entBytes`), and
cuts a `MsgApp`'s entries at `MaxSizePerMsg ≤ entsCutMax` (the starters' premise) or sends one entry
(`entsCut`). Harness `H4`, `H5`, `H9′`: 0 violations over 26,471 non-snapshot messages, adversarial
snapshots included. A restarted node's storage entries are WAL-replayed: they are sized by the
server's restart contract (out_size's restart clause, P7), and a first start's storage is sized by
`bootOk`. `outObjR_size`/`outEntR_size` (and the node API's `Cluster.outObj_size`/
`Cluster.outEnt_size`) are derived from it. -/
theorem out_size (γ : RaftNames) (x : Sum (Loc × MsgC) (Loc × EntryC)) (b : Nat) :
    outSetR (GF := GF) γ x ⊢ ⌜γ.maxData = some b → outSizeOk x⌝ := by
  unfold outSetR
  iintro ⟨-, %H⟩
  ipureintro
  exact H b

/-- **A handed-out message is of bounded size** (derived from `out_size`), unless a `MsgSnap`. -/
theorem outObjR_size (γ : RaftNames) (m : Loc) (c : MsgC) (b : Nat) :
    outObjR (GF := GF) γ m c ⊢ ⌜γ.maxData = some b → c.model.msg.Type' ≠ MsgSnap → msgSizeOk c⌝ :=
  out_size γ (.inl (m, c)) b

/-- **A handed-out entry is of bounded size** (derived from `out_size`). -/
theorem outEntR_size (γ : RaftNames) (e : Loc) (c : EntryC) (b : Nat) :
    outEntR (GF := GF) γ e c ⊢ ⌜γ.maxData = some b → entSizeOk c⌝ :=
  out_size γ (.inr (e, c)) b

theorem snapUfT_ne (l : Loc) (ty : w32) (h : ty ≠ MsgSnap) : ⊢ snapUfT (GF := GF) l ty := by
  unfold snapUfT; ileft; ipureintro; exact h

/-- `snapUf` reads only the type. -/
theorem snapUf_congr (l : Loc) (st st' : MsgSt) (h : st'.msg.Type' = st.msg.Type') :
    snapUf (GF := GF) l st ⊢ snapUf l st' := by
  unfold snapUf; rw [h]

end generic

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **What raft pins of a message's content**: its snapshot's conf state, if any, without unknown
fields (as `msgPtsC` holds it, `csUfNil`), and a `MsgSnap` without top-level unknown fields (the
literal `maybeSendSnapshot` builds). -/
def MsgC.sentOk (c : MsgC) : Prop := c.csUfNil ∧ (c.f.msgM.Type' = MsgSnap → c.f.uf = [])

/-- **A message handed out**, owned at `dq` (its entries and `Context` frozen, no capacity: as
`msgOwn`), holding `st`, at the content `c` raft pinned (`sentOk`), with its element of the
handed-out set. -/
def msgOutR (γ : RaftNames) (l : Loc) (dq : DFrac) (st : MsgSt) : IProp GF :=
  iprop(∃ c : MsgC, msgPtsCC l dq DFrac.discard false c ∗ ⌜c.model = st ∧ c.sentOk⌝ ∗ outObjR γ l c)

end defs

/-! ## Laws -/

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **A message's content form may take its `pbMsg` from anywhere**: today's message with a `pbMsg`
of its object at `uf0` is an object at a content whose own unknown fields are `uf0`. -/
theorem msgPtsC_msgPtsCC_uf (l : Loc) (dq dqe : DFrac) (cap : Bool) (st : MsgSt) (uf0 : List w8) :
    msgPtsC (GF := GF) l dq dqe cap st ∗ pbMsg raftpb.Message l uf0 ⊢
      ∃ c : MsgC, msgPtsCC l dq dqe cap c ∗ ⌜c.model = st ∧ c.csUfNil ∧ c.f.uf = uf0⌝ := by
  iintro ⟨H, #Hp⟩
  icases msgPtsC_msgPtsCC l dq dqe cap st $$ H with ⟨%c, Hc, %Hm⟩
  obtain ⟨Hmod, Hcs⟩ := Hm
  iexists MsgC.mk { c.f with uf := uf0 } c.resps
  isplitl [Hc]
  · unfold msgPtsCC
    icases Hc with ⟨%pty, %pto, %pfr, %pte, %plt, %pix, %pco, %pvo, %prj, %prh, %es, %els, %ps, %cs,
      %rsl, %Hnn, HTy, #cTy, HTo, #cTo, HFr, #cFr, HTe, #cTe, HLt, #cLt, HIx, #cIx, HCo, #cCo,
      HVo, #cVo, HRj, #cRj, HRh, #cRh, HEs, Hes, #Hents, Hcap, HSn, Hsn, HCx, #Hcx, HRs, Hrs, -⟩
    simp only [MsgC.f, MsgC.resps]
    iexists pty, pto, pfr, pte, plt, pix, pco, pvo, prj, prh, es, els, ps, cs, rsl
    isplitr
    · ipureintro; exact Hnn
    iframe
    iframe cTy cTo cFr cTe cLt cIx cCo cVo cRj cRh Hents Hcx Hp
  · ipureintro
    refine ⟨?_, ?_, rfl⟩
    · rw [← Hmod]; cases c; rfl
    · cases c; exact Hcs

/-- A handed-out message is owned as today's `msgOwn`. -/
theorem msgOutR_msgOwn (γ : RaftNames) (l : Loc) (dq : DFrac) (st : MsgSt) :
    msgOutR (GF := GF) γ l dq st ⊢ msgOwn l dq st := by
  unfold msgOutR
  iintro ⟨%c, Hc, %Hm, -⟩
  obtain ⟨Hmod, Hok, -⟩ := Hm
  rw [← Hmod]
  simp only [msgOwn, msgPts]
  iapply msgPtsCC_msgPtsC l dq DFrac.discard false c Hok $$ Hc

/-- **The `MsgSnap` law**: a handed-out `MsgSnap` has no top-level unknown fields. -/
theorem msgOutR_snap (γ : RaftNames) (l : Loc) (dq : DFrac) (st : MsgSt) :
    msgOutR (GF := GF) γ l dq st ⊢
      ∃ c : MsgC, msgPtsCC l dq DFrac.discard false c ∗ outObjR γ l c ∗
        ⌜c.model = st ∧ c.csUfNil ∧ (st.msg.Type' = MsgSnap → c.f.uf = [])⌝ := by
  unfold msgOutR
  iintro ⟨%c, Hc, %Hm, #Ho⟩
  obtain ⟨Hmod, Hcs, Hsn⟩ := Hm
  iexists c
  iframe Hc Ho
  ipureintro
  refine ⟨Hmod, Hcs, fun h => Hsn ?_⟩
  rw [← Hmod] at h; exact h

/-- An owned message with its `snapUf` is an object at a content raft pins (`sentOk`). -/
theorem msgOwn_snapUf_CC (l : Loc) (dq : DFrac) (st : MsgSt) :
    msgOwn (GF := GF) l dq st ∗ snapUf l st ⊢
      ∃ c : MsgC, msgPtsCC l dq DFrac.discard false c ∗ ⌜c.model = st ∧ c.sentOk⌝ := by
  iintro ⟨H, Hu⟩
  unfold snapUf snapUfT
  icases Hu with (%Hne | #Hp)
  · simp only [msgOwn, msgPts]
    icases msgPtsC_msgPtsCC l dq DFrac.discard false st $$ H with ⟨%c, Hc, %Hm⟩
    iexists c
    iframe Hc
    ipureintro
    refine ⟨Hm.1, Hm.2, fun h => absurd (by rw [← Hm.1]; exact h) Hne⟩
  · simp only [msgOwn, msgPts]
    icases msgPtsC_msgPtsCC_uf l dq DFrac.discard false st [] $$ [H Hp] with ⟨%c, Hc, %Hm⟩
    · iframe H Hp
    iexists c
    iframe Hc
    ipureintro
    exact ⟨Hm.1, Hm.2.1, fun _ => Hm.2.2⟩

end lemmas

/-! ### The size facts (raft-entsize §4, the receive row; out_size C3: moved here from rafthttp's
`Net.lean`, for raft's cut) -/

section sizePure
variable [GooseExts]

theorem varintSize_pos (n : Nat) : 1 ≤ varintSize n := by
  unfold varintSize
  rw [varintEnc]
  split <;> simp

theorem varintSize_le_succ : ∀ n : Nat, varintSize n ≤ n + 1 := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    unfold varintSize
    rw [varintEnc]
    split
    · simp
    · rename_i h
      simp only [List.length_cons]
      have := ih (n / 128) (by omega)
      unfold varintSize at this
      omega

theorem varintSize_le_of_lt : ∀ (k n : Nat), n < 2 ^ (7 * (k + 1)) → varintSize n ≤ k + 1 := by
  intro k
  induction k with
  | zero =>
    intro n h
    unfold varintSize
    rw [varintEnc, dite_eq_left_iff.2 (fun h' => absurd (by simpa using h) h')]
    simp
  | succ k ih =>
    intro n h
    unfold varintSize
    rw [varintEnc]
    split
    · simp
    · simp only [List.length_cons]
      have h2 : n / 128 < 2 ^ (7 * (k + 1)) := by
        rw [Nat.div_lt_iff_lt_mul (by decide)]
        have : 2 ^ (7 * (k + 1 + 1)) = 2 ^ (7 * (k + 1)) * 128 := by
          rw [show 7 * (k + 1 + 1) = 7 * (k + 1) + 7 by omega, Nat.pow_add]
        omega
      have := ih (n / 128) h2
      unfold varintSize at this
      omega

theorem varintSize_le_ten (n : Nat) (h : n < 2 ^ 64) : varintSize n ≤ 10 :=
  varintSize_le_of_lt 9 n (by
    have : (2 : Nat) ^ 64 ≤ 2 ^ (7 * (9 + 1)) := Nat.pow_le_pow_right (by decide) (by decide)
    omega)

theorem optW64Size_le (o : Option w64) : optW64Size o ≤ 11 := by
  rcases o with _ | v
  · simp [optW64Size, optVarintSize]
  · simp only [optW64Size, optVarintSize, Option.map_some]
    have := varintSize_le_ten (uint.Z v).toNat (by word)
    omega

theorem optVarintSize_le_type {T : Type} (o : Option T) (f : T → w64) :
    optVarintSize (o.map fun t => (uint.Z (f t)).toNat) ≤ 11 := by
  rcases o with _ | v
  · simp [optVarintSize]
  · simp only [optVarintSize, Option.map_some]
    have := varintSize_le_ten (uint.Z (f v)).toNat (by word)
    omega

theorem nat_le_sum_of_mem' {l : List Nat} {a : Nat} (h : a ∈ l) : a ≤ l.sum := by
  induction l with
  | nil => simp at h
  | cons x xs ih =>
    simp only [List.sum_cons]
    rcases List.mem_cons.1 h with rfl | h
    · omega
    · have := ih h; omega

theorem lenSize_ge (n : Nat) : n + 2 ≤ lenSize n := by
  have := varintSize_pos n; unfold lenSize; omega

theorem lenSize_le (n : Nat) : lenSize n ≤ 2 * n + 2 := by
  have := varintSize_le_succ n; unfold lenSize; omega

theorem sum_map_le_sum_map {α : Type} (l : List α) (f g : α → Nat) (h : ∀ x ∈ l, f x ≤ g x) :
    (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons]
    have h1 := h x List.mem_cons_self
    have h2 := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
    omega

theorem sum_map_mul {α : Type} (l : List α) (f : α → Nat) (k : Nat) :
    (l.map fun x => k * f x).sum = k * (l.map f).sum := by
  induction l with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons, List.sum_cons, ih, Nat.mul_add]

theorem entBytes_le_entrySize (e : EntryC) : entBytes e ≤ entrySize e := by
  unfold entBytes entrySize
  rcases e.data with _ | bs
  · simp
  · simp only [Option.getD_some]; omega

theorem entrySize_le_entBytes (e : EntryC) : entrySize e ≤ 2 * entBytes e + 35 := by
  have h2 := optW64Size_le e.term
  have h3 := optW64Size_le e.index
  unfold optW64Size at h2 h3
  unfold entBytes entrySize
  generalize hT : optVarintSize (Option.map _ e.type) = T
  have h1 : T ≤ 11 := by
    rw [← hT]
    rcases e.type with _ | ty
    · simp [optVarintSize]
    · simp only [Option.map_some, optVarintSize]
      exact Nat.le_trans (Nat.add_le_add_left (varintSize_le_ten _ (by word)) 1) (by omega)
  revert h1 h2 h3
  generalize e.data = d
  rcases d with _ | bs
  · simp only [Option.getD_none, List.length_nil]; intros; omega
  · have := varintSize_le_succ bs.length
    simp only [Option.getD_some]; intros; omega

theorem optBytesSize_ge (o : Option (List w8)) : (o.getD []).length ≤ optBytesSize o := by
  rcases o with _ | bs
  · simp [optBytesSize]
  · simp only [optBytesSize, Option.getD_some]; have := lenSize_ge bs.length; omega

theorem optBytesSize_le (o : Option (List w8)) : optBytesSize o ≤ 2 * (o.getD []).length + 2 := by
  rcases o with _ | bs
  · simp [optBytesSize]
  · simp only [optBytesSize, Option.getD_some]; exact lenSize_le _

/-- **A content of size at most `2^30` without responses is of bounded size** (raft-entsize §4: what
the message stream's decoder gives, `D1` under `readBytesLimit`). Each entry costs at least two bytes
of the size, so the entries' framed sum stays below `32 · 2^30`. -/
theorem msgSizeOk_of_size (c : MsgC) (hs : msgSize c ≤ 2 ^ 30) (hr : c.resps = []) :
    msgSizeOk c := by
  cases c with
  | mk f rs =>
  simp only [MsgC.resps] at hr
  subst hr
  have hsz : f.size ≤ 2 ^ 30 := by simpa [msgSize, respsSize] using hs
  have hent : (f.entries.map fun e => lenSize (entrySize e)).sum ≤ f.size := by
    unfold MsgFC.size; omega
  have hctx := optBytesSize_ge f.context
  refine ⟨rfl, ?_, ?_, ?_⟩ <;> try simp only [entBytesMax]
  · simp only [hdrBytes, MsgC.f]
    revert hsz
    unfold MsgFC.size
    generalize f.snapshot = sn
    rcases sn with _ | s
    · simp only [optSnapSize]; intro; omega
    · have := lenSize_ge (snapSize s)
      simp only [optSnapSize]; intro; omega
  · intro e he
    simp only [MsgC.f] at he
    have h1 : lenSize (entrySize e) ≤ (f.entries.map fun e => lenSize (entrySize e)).sum :=
      nat_le_sum_of_mem' (List.mem_map.2 ⟨e, he, rfl⟩)
    have := entBytes_le_entrySize e
    have := lenSize_ge (entrySize e)
    omega
  · simp only [MsgC.f]
    have h1 : (f.entries.map fun e => entBytes e + 64).sum ≤
        (f.entries.map fun e => 32 * lenSize (entrySize e)).sum :=
      sum_map_le_sum_map _ _ _ (fun e _ => by
        have := entBytes_le_entrySize e; have := lenSize_ge (entrySize e); omega)
    rw [sum_map_mul] at h1
    omega

/-- **A content of bounded size is below `2^47` bytes** (raft-entsize §4: the encoders' bound from
the size law; at most `2^38 + 2^34`). -/
theorem msgSize_lt_of_ok (c : MsgC) (h : msgSizeOk c) : msgSize c < 2 ^ 47 := by
  cases c with
  | mk f rs =>
  obtain ⟨hr, hh, he, hs⟩ := h
  simp only [entBytesMax] at hh he
  simp only [MsgC.resps] at hr
  subst hr
  simp only [msgSize, respsSize, Nat.add_zero]
  simp only [hdrBytes, MsgC.f] at hh he hs
  have hent : (f.entries.map fun e => lenSize (entrySize e)).sum ≤
      (f.entries.map fun e => 4 * (entBytes e + 64)).sum :=
    sum_map_le_sum_map _ _ _ (fun e _ => by
      have := lenSize_le (entrySize e); have := entrySize_le_entBytes e; omega)
  rw [sum_map_mul] at hent
  have hctx := optBytesSize_le f.context
  have := optW64Size_le f.to; have := optW64Size_le f.frm; have := optW64Size_le f.term
  have := optW64Size_le f.logTerm; have := optW64Size_le f.index; have := optW64Size_le f.commit
  have := optW64Size_le f.vote; have := optW64Size_le f.rejectHint
  have hb : optBoolSize f.reject ≤ 2 := by rcases f.reject with _ | _ <;> simp [optBoolSize]
  revert hh
  unfold MsgFC.size
  generalize hT : optVarintSize (Option.map _ f.type) = T
  have h1 : T ≤ 11 := by
    rw [← hT]
    rcases f.type with _ | ty
    · simp [optVarintSize]
    · simp only [Option.map_some, optVarintSize]
      exact Nat.le_trans (Nat.add_le_add_left (varintSize_le_ten _ (by word)) 1) (by omega)
  generalize f.snapshot = sn
  rcases sn with _ | s
  · simp only [optSnapSize]; intro; omega
  · have := lenSize_le (snapSize s)
    simp only [optSnapSize]; intro; omega

/-- (out_size C3) A sized entry's protobuf size is below `2^33`: what `limitSize`'s and `entsSize`'s
sums need to stay exact. -/
theorem entrySize_lt_of_ok (e : EntryC) (h : entSizeOk e) : entrySize e < 2 ^ 33 := by
  have := entrySize_le_entBytes e
  unfold entSizeOk entBytesMax at h
  omega

end sizePure

end EtcdGrove
end Perennial
