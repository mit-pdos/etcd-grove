/-
The pure vocabulary of conf-change messages (moved here from `InvConfChangeMsg.lean` on
2026-10-13, reconfiguration stage D, so that the protocol's ghost state can name it
without importing `Base`; see `InvConfChangeMsg.lean` for what each means):
`CCV1M`, `CCV2M`, the opaque decoders `ccDecodeV1`/`ccDecodeV2`, `CCMsg`; and (new)
`IsConfEnt` (an entry of type `EntryConfChange` or `EntryConfChangeV2`), `CCDecodes` (a
conf-change entry's bytes decode), `ccWantsLeave` (an empty `ConfChangeV2`: leave the joint
configuration) and `PropRepl` (a proposal's batch after `stepLeader`'s conf-change loop:
each entry kept, or a conf-change entry replaced by the empty normal entry).
-/
module

public import Perennial.Proof.ProofPrelude
public import Proof.go_etcd_io.raft.v3.PbModel

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace Perennial
namespace EtcdGrove

open go_etcd_io.raft.v3

/-- The content of a legacy `raftpb.ConfChange` (`raft.pb.go`: `ID`, `Type`, `NodeID`,
`Context`). -/
structure CCV1M [FfiSyntax] where
  type : raftpb.ConfChangeType
  nodeId : w64
  context : List w8
  id : w64

/-- The content of a `raftpb.ConfChangeV2` (`raft.pb.go`: `Transition`, `Changes`,
`Context`). -/
structure CCV2M [FfiSyntax] where
  transition : raftpb.ConfChangeTransition
  changes : List ConfChangeSingleM
  context : List w8

/-- What protobuf-go's `proto.Unmarshal` makes of `bs` into a `*ConfChange` (raft v3.7; until the
retarget, gogoproto's generated `(*ConfChange).Unmarshal`): the decoded content (the getters'
values), or `none` where it returns an error. Opaque: the trust-boundary specs of
`proto.Marshal`/`proto.Unmarshal` (`Spec/google_golang_org/protobuf/proto/{Marshal,Unmarshal}ConfChange.lean`)
are what is known of it. -/
opaque ccDecodeV1 [FfiSyntax] : List w8 → Option CCV1M

/-- What protobuf-go's `proto.Unmarshal` makes of `bs` into a `*ConfChangeV2` (until the
retarget, gogoproto's generated `(*ConfChangeV2).Unmarshal`); `none` where it returns an error.
Opaque, as `ccDecodeV1`. -/
opaque ccDecodeV2 [FfiSyntax] : List w8 → Option CCV2M

/-- A conf change as `MarshalConfChange` sees it: a legacy `ConfChange` or a `ConfChangeV2`. -/
inductive CCMsg [FfiSyntax] where
  | v1 : CCV1M → CCMsg
  | v2 : CCV2M → CCMsg

section pure
variable [FfiSyntax]

/-- A configuration-change entry (2026-10-13): `EntryConfChange` (1) or
`EntryConfChangeV2` (2), what `hasUnappliedConfChanges` and `stepLeader`'s proposal loop
look for. -/
def IsConfEnt (e : EntryM) : Prop := e.Type' = W32 1 ∨ e.Type' = W32 2

instance (e : EntryM) : Decidable (IsConfEnt e) := by
  unfold IsConfEnt; infer_instance

/-- The bytes of an entry of type `ty` decode as the conf change its type says
(2026-10-13): `stepLeader` `Unmarshal`s a proposed conf-change entry's data and panics if
that fails. -/
def CCDecodes (ty : w32) (bs : List w8) : Prop :=
  (ty = W32 1 → ∃ m, ccDecodeV1 bs = some m) ∧ (ty = W32 2 → ∃ m, ccDecodeV2 bs = some m)

/-- `len(cc.AsV2().Changes) == 0`, `stepLeader`'s `wantsLeaveJoint`: a `ConfChange`'s
`AsV2` has its one change, a `ConfChangeV2` is its own. -/
def ccWantsLeave : CCMsg → Bool
  | .v1 _ => false
  | .v2 m => m.changes.isEmpty

/-- A proposal's batch `es'` after `stepLeader`'s conf-change loop, from the proposed `es`
(2026-10-13): each entry kept, or a conf-change entry replaced by the empty normal entry
`pb.Entry{Type: EntryNormal}` (the zero `Entry`), as the loop does to a refused one. The
model's `Step.propose` appends such a batch. -/
def PropRepl (es es' : List EntryM) : Prop :=
  List.Forall₂ (fun e e' => e' = e ∨ (IsConfEnt e ∧ e' = zero_val EntryM)) es es'

theorem PropRepl.refl (es : List EntryM) : PropRepl es es := by
  induction es with
  | nil => exact List.Forall₂.nil
  | cons e es ih => exact List.Forall₂.cons (Or.inl rfl) ih

theorem PropRepl.length {es es' : List EntryM} (H : PropRepl es es') :
    es'.length = es.length := (List.Forall₂.length_eq H).symm

/-! ### `stepLeader`'s conf-change loop (2026-10-13)

For each entry of a proposal, with `cs` its decoded conf change (`none` for an entry that
is not one): a conf change is refused -- replaced by the empty normal entry -- when one is
already pending (`pendingConfIndex > applied`) or its `wantsLeaveJoint` disagrees with
`joint`, whether the configuration in use is joint (`alreadyJoint`): a request to leave
outside a joint configuration, or a change inside one (since 2026-10-14, reconfiguration
stage A3; `joint` defaults to `false`, the only case until then); otherwise it is accepted and `pendingConfIndex` moves to its index-to-be,
`lastIndex() + i + 1`. `propConfStep` is one iteration (the entries so far, whose length
is `i`, and `pendingConfIndex`), `propConf` the loop. -/

def propConfStep (joint : Bool) (applied li : w64) (acc : List EntryM × w64)
    (x : EntryM × Option CCMsg) : List EntryM × w64 :=
  match x.2 with
  | none => (acc.1 ++ [x.1], acc.2)
  | some c =>
    if uint.Z applied < uint.Z acc.2 ∨ ccWantsLeave c ≠ joint then
      (acc.1 ++ [zero_val EntryM], acc.2)
    else (acc.1 ++ [x.1], li + W64 (acc.1.length : Int) + W64 1)

def propConf (applied li pci : w64) (ents : List EntryM) (cs : List (Option CCMsg))
    (joint : Bool := false) : List EntryM × w64 :=
  (ents.zip cs).foldl (propConfStep joint applied li) ([], pci)

/-- The decoded conf changes of a batch: one per entry, present exactly for the
conf-change entries. -/
def CCTypesOk (ents : List EntryM) (cs : List (Option CCMsg)) : Prop :=
  List.Forall₂ (fun e (o : Option CCMsg) => o.isSome = decide (IsConfEnt e)) ents cs

theorem forall₂_app {α β : Type _} {R : α → β → Prop} {a1 a2 : List α} {b1 b2 : List β}
    (H1 : List.Forall₂ R a1 b1) (H2 : List.Forall₂ R a2 b2) :
    List.Forall₂ R (a1 ++ a2) (b1 ++ b2) := by
  induction H1 with
  | nil => simpa using H2
  | cons h _ ih => exact List.Forall₂.cons h ih

theorem cctypes_mem {ents : List EntryM} {cs : List (Option CCMsg)}
    (H : CCTypesOk ents cs) : ∀ x ∈ ents.zip cs, x.2.isSome = true → IsConfEnt x.1 := by
  induction H with
  | nil => intro x hx; simp at hx
  | cons Hh _ ih =>
    intro x hx Hs
    simp only [List.zip_cons_cons, List.mem_cons] at hx
    rcases hx with rfl | hx
    · simp only at Hs ⊢; rw [Hh] at Hs; exact of_decide_eq_true Hs
    · exact ih x hx Hs

theorem propConf_foldl_repl {joint : Bool} (applied li : w64) (xs : List (EntryM × Option CCMsg))
    (Hxs : ∀ x ∈ xs, x.2.isSome = true → IsConfEnt x.1) :
    ∀ (pre : List EntryM) (acc : List EntryM × w64), PropRepl pre acc.1 →
      PropRepl (pre ++ xs.map Prod.fst) (xs.foldl (propConfStep joint applied li) acc).1 := by
  induction xs with
  | nil => intro pre acc H; simpa using H
  | cons x xs ih =>
    intro pre acc H
    simp only [List.foldl_cons, List.map_cons]
    rw [show pre ++ x.1 :: xs.map Prod.fst = (pre ++ [x.1]) ++ xs.map Prod.fst by simp]
    apply ih (fun y hy => Hxs y (List.mem_cons_of_mem _ hy))
    unfold propConfStep
    have Hfa : PropRepl [x.1] [x.1] := PropRepl.refl _
    rcases x with ⟨e, o⟩
    cases o with
    | none => exact forall₂_app H Hfa
    | some c =>
      simp only
      split
      · exact forall₂_app H
          (List.Forall₂.cons (Or.inr ⟨Hxs _ (List.mem_cons_self) rfl, rfl⟩) List.Forall₂.nil)
      · exact forall₂_app H Hfa

/-- The loop's batch is the proposal's, with refused conf changes replaced. -/
theorem propConf_repl {joint : Bool} (applied li pci : w64) (ents : List EntryM)
    (cs : List (Option CCMsg)) (H : CCTypesOk ents cs) :
    PropRepl ents (propConf applied li pci ents cs joint).1 := by
  have Hlen := List.Forall₂.length_eq H
  have Hfst : (ents.zip cs).map Prod.fst = ents := List.map_fst_zip (by omega)
  have := propConf_foldl_repl (joint := joint) applied li (ents.zip cs) (cctypes_mem H) [] ([], pci)
    List.Forall₂.nil
  rw [List.nil_append, Hfst] at this; exact this

theorem propConfStep_length {joint : Bool} (applied li : w64) (acc : List EntryM × w64)
    (x : EntryM × Option CCMsg) :
    (propConfStep joint applied li acc x).1.length = acc.1.length + 1 := by
  unfold propConfStep
  split
  · simp
  · split <;> simp

theorem foldl_propConfStep_length {joint : Bool} (applied li : w64)
    (xs : List (EntryM × Option CCMsg)) :
    ∀ acc, (xs.foldl (propConfStep joint applied li) acc).1.length = acc.1.length + xs.length := by
  induction xs with
  | nil => intro acc; simp
  | cons x xs ih =>
    intro acc
    simp only [List.foldl_cons, List.length_cons]
    rw [ih, propConfStep_length]; omega

theorem propConf_length {joint : Bool} (applied li pci : w64) (es : List EntryM)
    (cs : List (Option CCMsg)) :
    (propConf applied li pci es cs joint).1.length = min es.length cs.length := by
  unfold propConf
  rw [foldl_propConfStep_length]
  simp [List.length_zip]

/-- One more iteration of the loop. -/
theorem propConf_take_succ (joint : Bool) (applied li pci : w64) (es : List EntryM)
    (cs : List (Option CCMsg)) (k : Nat) (e : EntryM) (o : Option CCMsg)
    (He : es[k]? = some e) (Ho : cs[k]? = some o) :
    propConf applied li pci (es.take (k + 1)) (cs.take (k + 1)) joint =
      propConfStep joint applied li (propConf applied li pci (es.take k) (cs.take k) joint) (e, o) := by
  have Hk1 := (List.getElem?_eq_some_iff.mp He).1
  have Hk2 := (List.getElem?_eq_some_iff.mp Ho).1
  unfold propConf
  rw [List.take_add_one, List.take_add_one, He, Ho]
  simp only [Option.toList_some]
  rw [List.zip_append (by simp only [List.length_take]; omega), List.foldl_append]
  rfl

theorem propConf_take_zero {joint : Bool} (applied li pci : w64) (es : List EntryM)
    (cs : List (Option CCMsg)) :
    propConf applied li pci (es.take 0) (cs.take 0) joint = ([], pci) := rfl

/-! ### Whether the loop refused a conf change (raft PR #454, `ErrConfChangeRejected`)

etcd-io/raft#454 makes `stepLeader` return `ErrConfChangeRejected` (after appending and
broadcasting the batch) when its conf-change loop refused one of the batch's conf changes:
its `rejectedConfChange` flag, set at every refusal. `propConfRefuses` is whether one
iteration refuses (at the `pendingConfIndex` it starts at), `propConfRej` the flag after the
loop, `propConfRejStep` the loop with the flag carried along. -/

def propConfRefuses (joint : Bool) (applied pci : w64) (x : EntryM × Option CCMsg) : Bool :=
  match x.2 with
  | none => false
  | some c => decide (uint.Z applied < uint.Z pci ∨ ccWantsLeave c ≠ joint)

def propConfRejStep (joint : Bool) (applied li : w64) (acc : (List EntryM × w64) × Bool)
    (x : EntryM × Option CCMsg) : (List EntryM × w64) × Bool :=
  (propConfStep joint applied li acc.1 x, acc.2 || propConfRefuses joint applied acc.1.2 x)

def propConfRej (applied li pci : w64) (ents : List EntryM) (cs : List (Option CCMsg))
    (joint : Bool := false) : Bool :=
  ((ents.zip cs).foldl (propConfRejStep joint applied li) (([], pci), false)).2

theorem foldl_propConfRejStep_fst {joint : Bool} (applied li : w64)
    (xs : List (EntryM × Option CCMsg)) :
    ∀ (a : List EntryM × w64) (b : Bool),
      (xs.foldl (propConfRejStep joint applied li) (a, b)).1 =
        xs.foldl (propConfStep joint applied li) a := by
  induction xs with
  | nil => intro a b; rfl
  | cons x xs ih => intro a b; exact ih _ _

theorem foldl_propConfRejStep_snd {joint : Bool} (applied li : w64)
    (xs : List (EntryM × Option CCMsg)) :
    ∀ (a : List EntryM × w64) (b : Bool),
      (xs.foldl (propConfRejStep joint applied li) (a, b)).2 = true →
        b = true ∨ ∃ x ∈ xs, x.2.isSome = true := by
  induction xs with
  | nil => intro a b h; exact .inl h
  | cons x xs ih =>
    intro a b h
    rcases ih _ _ h with h1 | ⟨y, hy, hs⟩
    · simp only [Bool.or_eq_true] at h1
      rcases h1 with h1 | h1
      · exact .inl h1
      · right; refine ⟨x, List.mem_cons_self .., ?_⟩
        unfold propConfRefuses at h1
        cases hx : x.2 with
        | none => rw [hx] at h1; simp at h1
        | some _ => rfl
    · exact .inr ⟨y, List.mem_cons_of_mem _ hy, hs⟩

/-- One more iteration of the loop, for the flag. -/
theorem propConfRej_take_succ (joint : Bool) (applied li pci : w64) (es : List EntryM)
    (cs : List (Option CCMsg)) (k : Nat) (e : EntryM) (o : Option CCMsg)
    (He : es[k]? = some e) (Ho : cs[k]? = some o) :
    propConfRej applied li pci (es.take (k + 1)) (cs.take (k + 1)) joint =
      (propConfRej applied li pci (es.take k) (cs.take k) joint ||
        propConfRefuses joint applied (propConf applied li pci (es.take k) (cs.take k) joint).2
          (e, o)) := by
  have Hk1 := (List.getElem?_eq_some_iff.mp He).1
  have Hk2 := (List.getElem?_eq_some_iff.mp Ho).1
  unfold propConfRej propConf
  rw [List.take_add_one, List.take_add_one, He, Ho]
  simp only [Option.toList_some]
  rw [List.zip_append (by simp only [List.length_take]; omega), List.foldl_append]
  simp only [List.zip_cons_cons, List.zip_nil_right, List.foldl_cons, List.foldl_nil]
  rw [← foldl_propConfRejStep_fst applied li _ ([], pci) false]
  rfl

theorem propConfRej_take_zero {joint : Bool} (applied li pci : w64) (es : List EntryM)
    (cs : List (Option CCMsg)) :
    propConfRej applied li pci (es.take 0) (cs.take 0) joint = false := rfl

/-- A refusal is of a conf-change entry of the batch. -/
theorem propConfRej_conf {joint : Bool} (applied li pci : w64) (es : List EntryM)
    (cs : List (Option CCMsg)) (Hct : CCTypesOk es cs)
    (H : propConfRej applied li pci es cs joint = true) : ∃ e ∈ es, IsConfEnt e := by
  unfold propConfRej at H
  rcases foldl_propConfRejStep_snd applied li _ _ _ H with h | ⟨x, hx, hs⟩
  · exact absurd h (by decide)
  · exact ⟨x.1, (List.of_mem_zip hx).1, cctypes_mem Hct x hx hs⟩

end pure

/-! ### The pure part of `InvConfChangeMsg.lean` (moved here in the raft v3.7 retarget, stage R1)

`ccEntryType`, `CCData` and `enterJointOf` name no Go value; the model of applying a change
(`CCApply.lean`) reads `enterJointOf`, so they are here rather than with the codec's
ownership predicates. -/

section codec
variable [FfiSyntax]

/-- The `EntryType` of an entry carrying a conf change (`MarshalConfChange`): `nil` and a
`ConfChangeV2` are `EntryConfChangeV2` (2), a `ConfChange` is `EntryConfChange` (1). -/
def ccEntryType : Option CCMsg → raftpb.EntryType
  | some (.v1 _) => W32 1
  | _ => W32 2

/-- The bytes `bs` carry the conf change `o` (`MarshalConfChange`'s data): for a
`ConfChange`, bytes `ccDecodeV1` decodes back to it; for a `ConfChangeV2`, `ccDecodeV2`;
for `nil`, nothing (the data slice is `nil`). -/
def CCData : Option CCMsg → List w8 → Prop
  | none, bs => bs = []
  | some (.v1 m), bs => ccDecodeV1 bs = some m
  | some (.v2 m), bs => ccDecodeV2 bs = some m

end codec

/-- `ConfChangeV2.EnterJoint`'s answer `(autoLeave, ok)` (`raftpb/confchange.go:82`) for a
transition `t` and a number `n` of changes: joint consensus when the transition is not `Auto`
or there is more than one change, left automatically unless the transition is
`JointExplicit`; `none` where it panics (joint consensus with a transition other than the
three defined ones). -/
def enterJointOf (t : w32) (n : Nat) : Option (Bool × Bool) :=
  if t ≠ W32 0 ∨ 1 < n then
    if t = W32 0 ∨ t = W32 1 then some (true, true)
    else if t = W32 2 then some (false, true)
    else none
  else some (false, false)

end EtcdGrove
end Perennial
