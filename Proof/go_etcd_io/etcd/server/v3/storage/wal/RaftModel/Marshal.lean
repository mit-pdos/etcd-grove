/-
**The raftpb instance's marshaller and unmarshaller** (W4c U4 of `notes/wal-fsext-w4c-plan.md`, "W4c U4
log"): `walRaftMr : WalMarshal` (the bytes the WAL's records hold: protobuf-go's encodings of the
canonical contents, `RaftModel/Codec.lean`, `RaftModel/EntCodec.lean`) and `walRaftU : WalUnmarshal`
(their decoders), with the pure laws the WAL's results take of them:

- `walRaftU_ok : walRaftU.Ok walRaftMr` (`ReadAll`'s fold: the round trips);
- `walRaftU_snapCoh : walRaftU.SnapCoh` (`ReadAll`'s `MustUnmarshalMessage.specWalSnap`: every snapshot
  it decodes is protobuf-go's encoding of a content with valid unknown fields);
- `walRaftMr_createOk : WalMarshalCreateOk walRaftMr` (`Create`'s initial snapshot record);
- `walRaftMr_encState_lt` (`walAreaOk`'s bound on the hard state's encoding, ledger 2026-11-14).

The hard state's bytes `hsEnc` are not yet tied to protobuf-go by a trusted fact (`Codec.lean`): these
laws are pure and hold of the definitions; the Iris laws that need the tie (`WalPbIn.MarshalHsLaw`, ...)
are the U4 log's blocked items. Lean-first.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.wal.RaftModel.Codec
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.RaftModel.EntCodec
public import Spec.go_etcd_io.etcd.server.v3.storage.wal.ReadAllCallees

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open go_etcd_io.raft.v3 WalEnc

section marshal
variable [GooseExts]

/-- **The raftpb instance's marshaller** (see the file header). -/
def walRaftMr : WalMarshal where
  encEntry := walEncEnt
  encState h := hsEnc (walHsCanon h)
  encSnap m := snapEnc (walSnapCanon m)
  snap0 := snapEnc snapC0

/-- **The raftpb instance's unmarshaller** (see the file header). -/
def walRaftU : WalUnmarshal where
  decEntry := walDecEnt
  decState := walDecHs
  decSnap := walDecSnap

/-- **The round trips** (`WalUnmarshal.Ok`). -/
theorem walRaftU_ok : walRaftU.Ok walRaftMr where
  entry e := walDecEnt_enc e
  state h := walDecHs_enc h
  snap m := walDecSnap_enc m
  snap0 := by
    have := walDecSnap_enc snapC0.model
    rw [walSnapCanon_snapC0] at this
    exact this

/-- **The snapshot decoder is coherent with protobuf-go** (`WalUnmarshal.SnapCoh`). -/
theorem walRaftU_snapCoh : walRaftU.SnapCoh := by
  intro bs s hs
  change walDecSnap bs = some s at hs
  unfold walDecSnap at hs
  split at hs
  · rename_i h
    refine ⟨walSnapCanon (Classical.choose h), walSnapCanon_levels _, Classical.choose_spec h, ?_⟩
    rw [walSnapCanon_model]
    exact Option.some.inj hs
  · cases hs

/-- **`Create`'s marshaller premise** (`WalMarshalCreateOk`). -/
theorem walRaftMr_createOk : WalMarshalCreateOk walRaftMr :=
  ⟨rfl, by simp only [walRaftMr, walSnapCanon_snapC0]⟩

/-- **The hard state's encoding is short** (`walAreaOk`'s last conjunct). -/
theorem walRaftMr_encState_lt (hs : HardStateM) : (walRaftMr.encState hs).length < 2 ^ 32 := by
  have := walHsCanon_enc_len hs
  simp only [walRaftMr]
  omega

end marshal

end EtcdGrove
end Perennial
