/-
`raftpb`'s conf-change entries as `stepLeader`'s proposal loop reads them (raft v3.7 retarget,
stage R4): `ccEntOk`/`ccEntsOk`, an entry of a proposal against its decoded conf change.

Until stage R4 this file also held the conf-change messages' Goose values and their ownership
(`ownCCV1`, `ownCCV2`, `ownCCI`), the value builders of `ProposeConfChange` (`ccEntry`,
`ccPropMsg`) and the pure vocabulary (`ccEntryType`, `CCData`, `enterJointOf`). In raft v3.7
the messages are pointers: their predicates are `InvPb.lean`'s (stage R1: `ownCCV1`, `ownCCV2`,
`ownCCI` over `*pb.ConfChange`/`*pb.ConfChangeV2`); the pure vocabulary is `CCModel.lean`'s
(R1); `ccEntry`/`ccPropMsg` go with `ProposeConfChange`'s port (stage R5). What is left is over
the model's entries (`EntryM`), whose `Data'` is the entry's bytes (D6).
-/
module

public import Proof.go_etcd_io.raft.v3.InvPb

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section own
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- What `stepLeader`'s proposal loop needs of an entry `e` of a proposal, with `o` its
decoded conf change (2026-10-13): none for an entry that is not a conf change; for one,
its bytes decode to `o` as its type says (pure since D6, stage R4: the record holds the bytes;
until then its data slice held them read-only). (`Unmarshal` panics if decoding fails, so the
proposer has to provide the bytes; `confChangeToMsg`'s `CCData`.) -/
def ccEntOk (e : EntryM) : Option CCMsg → IProp GF
  | none => iprop(⌜¬ IsConfEnt e⌝)
  | some (.v1 m) => iprop(⌜e.Type' = W32 1 ∧ ccDecodeV1 e.Data' = some m⌝)
  | some (.v2 m) => iprop(⌜e.Type' = W32 2 ∧ ccDecodeV2 e.Data' = some m⌝)

/-- `ccEntOk` of every entry of a batch, with the decoded conf changes `cs`. -/
def ccEntsOk (ents : List EntryM) (cs : List (Option CCMsg)) : IProp GF :=
  [∗list] e;o ∈ ents;cs, ccEntOk e o

instance ccEntOk_persistent (e : EntryM) (o : Option CCMsg) :
    Persistent (ccEntOk (GF := GF) e o) := by
  rcases o with _ | (m | m) <;> unfold ccEntOk <;> infer_instance

instance ccEntsOk_persistent (ents : List EntryM) (cs : List (Option CCMsg)) :
    Persistent (ccEntsOk (GF := GF) ents cs) := by
  unfold ccEntsOk; infer_instance

theorem ccEntOk_type (e : EntryM) (o : Option CCMsg) :
    ccEntOk (GF := GF) e o ⊢ ⌜o.isSome = decide (IsConfEnt e)⌝ := by
  rcases o with _ | (m | m) <;> unfold ccEntOk
  · iintro %H; ipureintro; simp [H]
  · iintro ⟨%H, -⟩; ipureintro; simp [IsConfEnt, H]
  · iintro ⟨%H, -⟩; ipureintro; simp [IsConfEnt, H]

theorem ccEntsOk_types (ents : List EntryM) (cs : List (Option CCMsg)) :
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
theorem ccEntsOk_normal (ents : List EntryM) (H : ∀ e ∈ ents, e.Type' = W32 0) :
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
