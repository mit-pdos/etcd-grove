/- `RawNode.ProposeConfChange` (rawnode.go), Lean-first (2026-10-13, reconfiguration stage D).

`ProposeConfChange(cc)` is `m, err := confChangeToMsg(cc); if err != nil { return err };
return rn.raft.Step(m)`: a `MsgProp` (`Term` and `From` zero) whose one entry carries the
conf change, `EntryConfChange` or `EntryConfChangeV2` with its gogoproto encoding
(`confChangeToMsg`, `MarshalConfChange`, whose `Marshal` never fails). `Step` of it at a
leader runs `stepLeader`'s conf-change loop, which decodes the entry back (`Unmarshal`;
`Marshal`'s spec says the bytes decode) and appends it or, refused, the empty normal entry
in its place; at a follower it is forwarded, at a candidate dropped. The `RawNode`'s
client-facing state is unchanged, as for `Propose`.

The conf change is `some o`: a `nil` `ConfChangeI` (`confChangeToMsg(nil)`, which only
`appliedTo`'s auto-leave sends, dead here: `AutoLeave` is off) proposes an
`EntryConfChangeV2` with no data, which `Unmarshal` decodes to what `ccDecodeV2 []` says,
which nothing states.

The entry's data is recorded as a proposed slice (`isPropData`, with its decoding): the
proposal's protocol message carries it (`isMessage`, `entData`), so that a leader the
proposal is forwarded to can read the bytes back (`node.run`, from the proposed slices'
invariant, `propData_ccEnts`). The caller provides the recording (`"#Hreg"`: what
`propData_register` gives with the invariant, `InvNode.lean`). A conf-change entry is no
client operation: its data is outside the client log (`entDataIs`, `none`).
(2026-10-16, stage R5, D6: the entry's record holds its bytes, so the protocol message carries
them and a leader decodes them from the record (`entData_cc`, `ccEntsOk_cc`, pure); the
recording and `"#Hreg"` are gone.)

Not stated: whether the change is appended or refused (a pending conf change, an empty
`ConfChangeV2`), which `Step`'s postcondition does not expose and the error does not tell
(a refused conf change is appended as an empty normal entry, `nil` returned); and the order
in which the application must apply committed conf changes (`ApplyConfChange`) relative to
`Advance`, which is `RawNode.ApplyConfChange`'s concern (its spec's documentation).

raft v3.7 (2026-10-16, stage R5): `confChangeToMsg` returns a `*pb.Message`, owned
(`confChangeToMsg.spec`), which `raft.Step` takes for good; `cc` is given back.
-/
module

public import Proof.go_etcd_io.raft.v3.ApiVocab
public import Proof.go_etcd_io.raft.v3.InvRawnode
public import Proof.go_etcd_io.raft.v3.InvConfChangeMsg

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

-- (2026-10-16, stage R5, D6) `propRegister` (recording a slice as proposed, `isPropData`) is
-- gone with the proposed slices: a conf-change entry holds its bytes.

omit [GooseInterp] [GooseSemantics] go_gctx [StorageModel GF] sem package_sem in
theorem confChangeEntryType_some (o : ConfChangeIM) :
    confChangeEntryType (some o) = W32 1 ∨ confChangeEntryType (some o) = W32 2 := by
  rcases o with m | m
  · left; rfl
  · right; rfl

omit [GooseInterp] [GooseSemantics] go_gctx [StorageModel GF] sem package_sem in
theorem ccData_decodes (o : ConfChangeIM) (bs : List w8) (H : MarshalsConfChange (some o) bs) :
    CCDecodes (confChangeEntryType (some o)) bs := by
  rcases o with m | m
  · refine ⟨fun _ => ⟨m, H⟩, fun h => ?_⟩
    exfalso; revert h; simp only [confChangeEntryType]; word
  · refine ⟨fun h => ?_, fun _ => ⟨m, H⟩⟩
    exfalso; revert h; simp only [confChangeEntryType]; word

-- (2026-10-26, raft's signature, stage 1) `CCAllowed` moved to `Proof.go_etcd_io.raft.v3.ApiVocab`.

omit [GooseSemantics] go_gctx [StorageModel GF] sem package_sem in
/-- A conf change's entry is no client operation: its data are bytes that decode.
(2026-10-16, stage R5, D6: over the entry's record `ccEntryM`, which holds the bytes; until then
over a proposed slice, `isPropData`.) -/
theorem entData_cc (γ : RaftNames) (o : ConfChangeIM) (bs : List w8)
    (H : MarshalsConfChange (some o) bs) (Hok : γ.reCCOk (confChangeEntryType (some o)) bs) :
    ⊢ propData (GF := GF) γ (ccEntryM (some o) bs) := by
  unfold propData
  iexists none
  unfold propDataIs
  iright
  ipureintro
  refine ⟨?_, ccData_decodes o bs H, Hok⟩
  show confChangeEntryType (some o) ≠ W32 0
  rcases confChangeEntryType_some o with h | h <;> rw [h] <;> word

omit [GooseSemantics] go_gctx [StorageModel GF] sem package_sem in
/-- A conf change's entry carries no ticket (D21 M6). -/
theorem entTk_cc (γ : RaftNames) (o : ConfChangeIM) (bs : List w8) :
    ⊢ entTk (GF := GF) γ (ccEntryM (some o) bs) := by
  unfold entTk
  rw [if_neg]
  · iempintro
  · intro h
    have h1 : confChangeEntryType (some o) = W32 0 := h.1
    rcases confChangeEntryType_some o with h' | h' <;> rw [h'] at h1 <;> revert h1 <;> word

omit [GooseInterp] [GooseSemantics] go_gctx hG [StorageModel GF] sem package_sem in
/-- What `Step` needs of the conf change's entry: its bytes decode (pure since D6). -/
theorem ccEntsOk_cc (o : ConfChangeIM) (bs : List w8) (H : MarshalsConfChange (some o) bs) :
    ⊢ ccEntsOk (GF := GF) [ccEntryM (some o) bs] [some o] := by
  unfold ccEntsOk
  iapply (BigSepL2.bigSepL2_cons (Φ := fun _ e o => ccEntOk (GF := GF) e o)).2
  isplitl
  · rcases o with m | m
    · simp only [ccEntOk]
      ipureintro; exact ⟨rfl, H⟩
    · simp only [ccEntOk]
      ipureintro; exact ⟨rfl, H⟩
  iapply (BigSepL2.bigSepL2_nil (Φ := fun _ e o => ccEntOk (GF := GF) e o)).2
  iempintro

/-- See the file header. -/
abbrev RawNode.ProposeConfChange.spec : Prop :=
  ∀ (γ : RaftNames) (rn : Loc) (id : w64) (rs : RNState) (c : GoInterface) (o : ConfChangeIM)
    (dq : DFrac),
  -- (2026-10-15, stage N) a change the cluster admits
  CCAllowed γ o →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hrn" ∷ ownRawNode γ rn id rs ∗
      "Hc" ∷ ownConfChangeI c dq (some o) }}
    (App (Val (rn @!! go.GoType.PointerType RawNode.ty @!! go!"ProposeConfChange")) (Val #c))
  {{ (err : GoInterface), RET #err;
      "Hrn" ∷ ownRawNode γ rn id rs ∗
      "Hc" ∷ ownConfChangeI c dq (some o) ∗
      "Herr" ∷ (⌜err = interface.nil⌝ ∨ globalAddr ErrProposalDropped ↦□ err) }}

end spec

end EtcdGrove
end Perennial
