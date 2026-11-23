/-
The swiftpaxos client's codec lemmas beyond dsv-epaxos's (`NetRpc/Codec.lean`): the client asks
the master `GetReplicaList` and `GetLeader` (`client.Client.callMasterRL`/`callMasterL`), so it
encodes their (empty) arguments and decodes their replies into fresh zero values. Stated here,
proved in `NetRpc/CodecCliProof.lean` (`swiftCliCodecLaws`).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.NetRpc.Codec

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net
open github_com.imdea_software.swiftpaxos.netrpcw

namespace github_com.imdea_software.swiftpaxos

section codec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [net.rpc.Assumptions] [net.FieldAssumptions] [π : NetProtoGS]
variable [examples.swiftnet.Assumptions]

attribute [local instance] GooseGlobalGS.gooseInvGS

abbrev enc_GetLeaderArgs.spec : Prop :=
  ∀ (p : Loc) (dq : DFrac) (Ψ : List w8 → IProp GF),
    p ↦{dq} replica.defs.GetLeaderArgs.mk ∗
      (p ↦{dq} replica.defs.GetLeaderArgs.mk -∗ Ψ encGetLeaderArgs) ⊢
    swiftCodec.enc (ptrIface replica.defs.GetLeaderArgs.ty p) Ψ

abbrev enc_GetReplicaListArgs.spec : Prop :=
  ∀ (p : Loc) (dq : DFrac) (Ψ : List w8 → IProp GF),
    p ↦{dq} replica.defs.GetReplicaListArgs.mk ∗
      (p ↦{dq} replica.defs.GetReplicaListArgs.mk -∗ Ψ encGetReplicaListArgs) ⊢
    swiftCodec.enc (ptrIface replica.defs.GetReplicaListArgs.ty p) Ψ

/-- `GetLeader`'s reply decoded into the zero `GetLeaderReply` (the client's `new(...)`). -/
abbrev dec_GetLeaderReply.spec : Prop :=
  ∀ (p : Loc) (rep : List w8) (Ψ : Bool → IProp GF),
    ⌜tagOk tGetLeaderReply rep⌝ ∗
    p ↦ replica.defs.GetLeaderReply.mk (W64 0) ∗
      (∀ ok, (if ok then ∃ id : w64, p ↦ replica.defs.GetLeaderReply.mk id ∗
          ⌜∀ id', rep = encGetLeaderReply id' → id = id'⌝
        else ∃ v : replica.defs.GetLeaderReply, p ↦ v) -∗ Ψ ok) ⊢
    swiftCodec.dec rep (ptrIface replica.defs.GetLeaderReply.ty p) Ψ

/-- `GetReplicaList`'s reply decoded into the zero `GetReplicaListReply`. -/
abbrev dec_GetReplicaListReply.spec : Prop :=
  ∀ (p : Loc) (rep : List w8) (Ψ : Bool → IProp GF),
    ⌜tagOk tGetReplicaListReply rep⌝ ∗
    p ↦ replica.defs.GetReplicaListReply.mk slice.nil slice.nil false ∗
      (∀ ok, (if ok then ∃ (s1 s2 : GoSlice) (rl : List GoString) (al : List Bool) (r : Bool),
          p ↦ replica.defs.GetReplicaListReply.mk s1 s2 r ∗ s1 ↦* rl ∗ s2 ↦* al ∗
          ⌜∀ rl' al' r', rep = encGetReplicaListReply rl' al' r' →
            rl = rl' ∧ al = al' ∧ r = r'⌝
        else ∃ v : replica.defs.GetReplicaListReply, p ↦ v) -∗ Ψ ok) ⊢
    swiftCodec.dec rep (ptrIface replica.defs.GetReplicaListReply.ty p) Ψ

/-- The client's codec lemmas (beyond `CodecLaws`). -/
structure CliCodecLaws : Prop where
  enc_GetLeaderArgs : enc_GetLeaderArgs.spec (GF := GF)
  enc_GetReplicaListArgs : enc_GetReplicaListArgs.spec (GF := GF)
  dec_GetLeaderReply : dec_GetLeaderReply.spec (GF := GF)
  dec_GetReplicaListReply : dec_GetReplicaListReply.spec (GF := GF)

end codec

end github_com.imdea_software.swiftpaxos

end Perennial
