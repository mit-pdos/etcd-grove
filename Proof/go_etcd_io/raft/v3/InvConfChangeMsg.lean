/-
`raftpb`'s conf-change messages (`ConfChange`, `ConfChangeV2`) as pure values, their wire
encoding, and the vocabulary of `Spec/go_etcd_io/raft/v3/raftpb/{ConfChange,ConfChangeV2}__*`,
`MarshalConfChange` and `confChangeToMsg` (Lean-first, 2026-10-13; reconfiguration, stage 0).

* `CCV1M`, `CCV2M`: a message's content, every slice as its list (a record of pure values,
  `notes/decisions.md`, "Predicate indices"); `ownCCV1`/`ownCCV2` relate a Go value to it.
  The changes of a `CCV2M` are `List raftpb.ConfChangeSingle`, the list `InvConfchange.lean`'s
  model (`applyM`, `simpleM`, `enterJointM`) takes.
* `ccDecodeV1`/`ccDecodeV2`: what gogoproto's `Unmarshal` makes of a byte string, `none` when it
  returns an error. Opaque: they *are* Go's decoders, named, and the trust-boundary axioms
  (`Proof/go_etcd_io/raft/v3/raftpb/ConfChange{,V2}__{Marshal,Unmarshal}.lean`) say that
  `Unmarshal` computes them and that `Marshal` produces bytes they decode back. There is no
  pure encoder: `Marshal`'s output is not a function of the content (a `nil` `Context` is
  omitted, an empty non-`nil` one is encoded as an empty field; `CCV2M` does not tell them
  apart), so the round trip is stated as `Marshal`'s postcondition, `ccDecode bs = some m`,
  rather than as a law `ccDecode (ccEncode m) = some m` about an encoder that does not exist.
* `CCMsg`, `ownCCI`: a `ConfChangeI` interface value holding a `ConfChange` or a
  `ConfChangeV2` (or `nil`), as `MarshalConfChange` and `confChangeToMsg` take it.
* `enterJointOf`: `ConfChangeV2.EnterJoint`'s answer, `none` where it panics.
-/
module

public import Proof.go_etcd_io.raft.v3.Base
public import Proof.go_etcd_io.raft.v3.CCModel

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

/-! `CCV1M`, `CCV2M`, `ccDecodeV1`, `ccDecodeV2` and `CCMsg` are in `CCModel.lean` (since
2026-10-13). -/

/-- The `EntryType` of an entry carrying a conf change (`MarshalConfChange`): `nil` and a
`ConfChangeV2` are `EntryConfChangeV2` (2), a `ConfChange` is `EntryConfChange` (1). -/
def ccEntryType [FfiSyntax] : Option CCMsg → raftpb.EntryType
  | some (.v1 _) => W32 1
  | _ => W32 2

/-- The bytes `bs` carry the conf change `o` (`MarshalConfChange`'s data): for a
`ConfChange`, bytes `ccDecodeV1` decodes back to it; for a `ConfChangeV2`, `ccDecodeV2`;
for `nil`, nothing (the data slice is `nil`). -/
def CCData [FfiSyntax] : Option CCMsg → List w8 → Prop
  | none, bs => bs = []
  | some (.v1 m), bs => ccDecodeV1 bs = some m
  | some (.v2 m), bs => ccDecodeV2 bs = some m

/-- The entry `confChangeToMsg` proposes for the conf change `o` with data `data`:
`pb.Entry{Type: typ, Data: data}`. -/
def ccEntry [FfiSyntax] (o : Option CCMsg) (data : GoSlice) : raftpb.Entry :=
  { (zero_val raftpb.Entry) with Type' := ccEntryType o, Data' := data }

/-- The message `confChangeToMsg` builds around the entries slice `ents`:
`pb.Message{Type: MsgProp, Entries: ents}` (`MsgProp` is 2). -/
def ccPropMsg [FfiSyntax] (ents : GoSlice) : raftpb.Message :=
  { Type' := W32 2, To' := 0, From' := 0, Term' := 0, LogTerm' := 0, Index' := 0,
    Entries' := ents, Commit' := 0, Vote' := 0, Snapshot' := null, Reject' := false,
    RejectHint' := 0, Context' := slice.nil, Responses' := slice.nil }

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

section own
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- The `ConfChange` value `v` holds `m`, its `Context` owned at `dq`. -/
def ownCCV1 (v : raftpb.ConfChange) (dq : DFrac) (m : CCV1M) : IProp GF :=
  iprop(⌜v.Type' = m.type ∧ v.NodeId' = m.nodeId ∧ v.Id' = m.id⌝ ∗ v.Context' ↦*{dq} m.context)

/-- The `ConfChangeV2` value `v` holds `m`, its two slices owned at `dq`. -/
def ownCCV2 (v : raftpb.ConfChangeV2) (dq : DFrac) (m : CCV2M) : IProp GF :=
  iprop(⌜v.Transition' = m.transition⌝ ∗ v.Changes' ↦*{dq} m.changes ∗
    v.Context' ↦*{dq} m.context)

/-- The `ConfChangeI` interface value `c` holds `o`: `nil` (`none`), or a `ConfChange` or
`ConfChangeV2` *value* (not a pointer: the dynamic types `MarshalConfChange`'s specs cover)
holding the content, its slices owned at `dq`. -/
def ownCCI (c : GoInterface) (dq : DFrac) : Option CCMsg → IProp GF
  | none => iprop(⌜c = interface.nil⌝)
  | some (.v1 m) => iprop(∃ v : raftpb.ConfChange,
      ⌜c = interface.mkOk raftpb.ConfChange.ty #v⌝ ∗ ownCCV1 v dq m)
  | some (.v2 m) => iprop(∃ v : raftpb.ConfChangeV2,
      ⌜c = interface.mkOk raftpb.ConfChangeV2.ty #v⌝ ∗ ownCCV2 v dq m)

/-- What `stepLeader`'s proposal loop needs of an entry `e` of a proposal, with `o` its
decoded conf change (2026-10-13): none for an entry that is not a conf change; for one,
its data slice holds (read-only) bytes that decode to `o` as its type says. (`Unmarshal`
panics if decoding fails, so the proposer has to provide the bytes; `confChangeToMsg`'s
`CCData`.) -/
def ccEntOk (e : raftpb.Entry) : Option CCMsg → IProp GF
  | none => iprop(⌜¬ IsConfEnt e⌝)
  | some (.v1 m) => iprop(⌜e.Type' = W32 1⌝ ∗ ∃ bs, e.Data' ↦*□ bs ∗ ⌜ccDecodeV1 bs = some m⌝)
  | some (.v2 m) => iprop(⌜e.Type' = W32 2⌝ ∗ ∃ bs, e.Data' ↦*□ bs ∗ ⌜ccDecodeV2 bs = some m⌝)

/-- `ccEntOk` of every entry of a batch, with the decoded conf changes `cs`. -/
def ccEntsOk (ents : List raftpb.Entry) (cs : List (Option CCMsg)) : IProp GF :=
  [∗list] e;o ∈ ents;cs, ccEntOk e o

instance ccEntOk_persistent (e : raftpb.Entry) (o : Option CCMsg) :
    Persistent (ccEntOk (GF := GF) e o) := by
  rcases o with _ | (m | m) <;> unfold ccEntOk <;> infer_instance

instance ccEntsOk_persistent (ents : List raftpb.Entry) (cs : List (Option CCMsg)) :
    Persistent (ccEntsOk (GF := GF) ents cs) := by
  unfold ccEntsOk; infer_instance

theorem ccEntOk_type (e : raftpb.Entry) (o : Option CCMsg) :
    ccEntOk (GF := GF) e o ⊢ ⌜o.isSome = decide (IsConfEnt e)⌝ := by
  rcases o with _ | (m | m) <;> unfold ccEntOk
  · iintro %H; ipureintro; simp [H]
  · iintro ⟨%H, -⟩; ipureintro; simp [IsConfEnt, H]
  · iintro ⟨%H, -⟩; ipureintro; simp [IsConfEnt, H]

theorem ccEntsOk_types (ents : List raftpb.Entry) (cs : List (Option CCMsg)) :
    ccEntsOk (GF := GF) ents cs ⊢ ⌜CCTypesOk ents cs⌝ := by
  unfold ccEntsOk CCTypesOk
  induction ents generalizing cs with
  | nil =>
    cases cs with
    | nil => iintro _; ipureintro; exact List.Forall₂.nil
    | cons c cs =>
      iintro H
      ihave %Hl := BigSepL2.bigSepL2_length $$ H
      simp at Hl
  | cons e ents ih =>
    cases cs with
    | nil =>
      iintro H
      ihave %Hl := BigSepL2.bigSepL2_length $$ H
      simp at Hl
    | cons c cs =>
      iintro H
      icases (BigSepL2.bigSepL2_cons (Φ := fun _ e o => ccEntOk (GF := GF) e o)).1 $$ H with ⟨He, Hr⟩
      ihave %H1 := ccEntOk_type e c $$ He
      ihave %H2 := ih cs $$ Hr
      ipureintro
      exact List.Forall₂.cons H1 H2

/-- A batch of normal entries needs nothing. -/
theorem ccEntsOk_normal (ents : List raftpb.Entry) (H : ∀ e ∈ ents, e.Type' = W32 0) :
    ⊢ ccEntsOk (GF := GF) ents (ents.map fun _ => none) := by
  unfold ccEntsOk
  induction ents with
  | nil =>
    simp only [List.map_nil]
    iapply (BigSepL2.bigSepL2_nil (Φ := fun _ e o => ccEntOk (GF := GF) e o)).2; iempintro
  | cons e ents ih =>
    simp only [List.map_cons]
    iapply (BigSepL2.bigSepL2_cons (Φ := fun _ e o => ccEntOk (GF := GF) e o)).2
    isplitl
    · unfold ccEntOk
      ipureintro
      have He := H e List.mem_cons_self
      unfold IsConfEnt; rw [He]
      rintro (h | h) <;> revert h <;> word
    · iapply ih (fun e' h => H e' (List.mem_cons_of_mem _ h))

end own

end EtcdGrove
end Perennial
