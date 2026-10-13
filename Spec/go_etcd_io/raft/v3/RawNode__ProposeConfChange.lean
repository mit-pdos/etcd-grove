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

Not stated: whether the change is appended or refused (a pending conf change, an empty
`ConfChangeV2`), which `Step`'s postcondition does not expose and the error does not tell
(a refused conf change is appended as an empty normal entry, `nil` returned); and the order
in which the application must apply committed conf changes (`ApplyConfChange`) relative to
`Advance`, which is `RawNode.ApplyConfChange`'s concern (its spec's documentation).
-/
module

public import Proof.go_etcd_io.raft.v3.InvRawnode
public import Proof.go_etcd_io.raft.v3.InvConfChangeMsg

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- The ability to record a slice as proposed (`isPropData`): what the proposed slices'
invariant gives (`propData_register`, `InvNode.lean`). -/
def propRegister (γ : RaftNames) : IProp GF :=
  iprop(□ ∀ (sl : GoSlice) (bs : List w8), sl ↦*□ bs ={⊤}=∗ isPropData γ sl bs)

instance propRegister_persistent (γ : RaftNames) : Persistent (propRegister (GF := GF) γ) := by
  unfold propRegister; infer_instance

omit ffi [FfiInterp ffi] [FfiSemantics ext ffi] go_gctx [StorageModel GF] sem package_sem in
theorem ccEntryType_some (o : CCMsg) :
    ccEntryType (some o) = W32 1 ∨ ccEntryType (some o) = W32 2 := by
  rcases o with m | m
  · left; rfl
  · right; rfl

omit ffi [FfiInterp ffi] [FfiSemantics ext ffi] go_gctx [StorageModel GF] sem package_sem in
theorem ccData_decodes (o : CCMsg) (bs : List w8) (H : CCData (some o) bs) :
    CCDecodes (ccEntryType (some o)) bs := by
  rcases o with m | m
  · refine ⟨fun _ => ⟨m, H⟩, fun h => ?_⟩
    exfalso; revert h; simp only [ccEntryType]; word
  · refine ⟨fun h => ?_, fun _ => ⟨m, H⟩⟩
    exfalso; revert h; simp only [ccEntryType]; word

/-- A conf change's entry is no client operation: its data are bytes that decode. -/
theorem entData_cc (γ : RaftNames) (o : CCMsg) (data : GoSlice) (bs : List w8)
    (H : CCData (some o) bs) :
    ⊢ isPropData (GF := GF) γ data bs -∗ entData γ (ccEntry (some o) data) := by
  iintro #Hpd
  unfold entData
  iexists none
  unfold entDataIs
  iright
  isplitr
  · ipureintro
    show ccEntryType (some o) ≠ W32 0
    rcases ccEntryType_some o with h | h <;> rw [h] <;> word
  iexists bs
  dsimp only [ccEntry]
  iframe Hpd
  ipureintro
  exact ccData_decodes o bs H

/-- What `Step` needs of the conf change's entry: its bytes, which decode. -/
theorem ccEntsOk_cc (o : CCMsg) (data : GoSlice) (bs : List w8) (H : CCData (some o) bs) :
    ⊢ data ↦*□ bs -∗ ccEntsOk (GF := GF) [ccEntry (some o) data] [some o] := by
  iintro #Hd
  unfold ccEntsOk
  iapply (BigSepL2.bigSepL2_cons (Φ := fun _ e o => ccEntOk (GF := GF) e o)).2
  isplitl
  · rcases o with m | m
    · simp only [ccEntOk]
      isplitr
      · ipureintro; rfl
      iexists bs
      dsimp only [ccEntry]
      iframe Hd
      ipureintro; exact H
    · simp only [ccEntOk]
      isplitr
      · ipureintro; rfl
      iexists bs
      dsimp only [ccEntry]
      iframe Hd
      ipureintro; exact H
  iapply (BigSepL2.bigSepL2_nil (Φ := fun _ e o => ccEntOk (GF := GF) e o)).2
  iempintro

/-- See the file header. -/
abbrev RawNode.ProposeConfChange.spec : Prop :=
  ∀ (γ : RaftNames) (rn : Loc) (id : w64) (rs : RNState) (c : GoInterface) (o : CCMsg)
    (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hrn" ∷ ownRawNode γ rn id rs ∗
      "Hc" ∷ ownCCI c dq (some o) ∗
      "#Hreg" ∷ propRegister γ }}
    (App (Val (rn @!! go.GoType.PointerType RawNode.ty @!! go!"ProposeConfChange")) (Val #c))
  {{ (err : GoInterface), RET #err;
      "Hrn" ∷ ownRawNode γ rn id rs ∗
      "Hc" ∷ ownCCI c dq (some o) ∗
      "Herr" ∷ (⌜err = interface.nil⌝ ∨ globalAddr ErrProposalDropped ↦□ err) }}

end spec

end EtcdGrove
end Perennial
