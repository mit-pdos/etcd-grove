/-
`(*Replica).handleTryPreAccept`, `(*Replica).handleTryPreAcceptReply`: never invoked (no
replica sends a TryPreAccept: `Inv.noTPA`), so their specs take the contradiction the invariant
gives (`hdead : False`).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.epaxos.HCtx

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net github_com.imdea_software.swiftpaxos_epaxos.kvs
open model epaxosProof

attribute [local instance] GooseGlobalGS.gooseInvGS

variable [GooseExts]

section heap
variable [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [go.Semantics]
variable [epaxos.Assumptions] [HasExt netExt] [π : NetProtoGS]
variable [state.Assumptions] [github_com.emirpasic.gods.maps.treemap.Assumptions] [TH : StateTreemap GF]

/-- **`handleTryPreAccept(tpa)`**: unreachable (`Inv.noTPA`). -/
theorem wp_handleTryPreAccept (γ : EpNames) (i : Nat) (r rr : Loc) (L : List GoString)
    (p : FwPtrs) (Rext : IProp GF) (ord : List w32) (σ : RState) (l : Loc)
    (m : TryPreAccept) (hdead : False) :
    {{ hdCtx (GF := GF) γ i r rr L p Rext ord ∗ ownRep γ i r σ ∗ ownTryPreAccept l m (DFrac.own 1) ∗
        repFrag γ i (hTryPreAccept σ m).1 ∗ outsOk γ i (hTryPreAccept σ m).2 }}
      (App (Val (r @!! go.GoType.PointerType epaxos.Replica.ty @!! go!"handleTryPreAccept"))
        (Val #l))
    {{ RET #(); repDone γ i r }} := hdead.elim

/-- **`handleTryPreAcceptReply(tpar)`**: unreachable (`Inv.noTPA`). -/
theorem wp_handleTryPreAcceptReply (γ : EpNames) (i : Nat) (r rr : Loc) (L : List GoString)
    (p : FwPtrs) (Rext : IProp GF) (ord : List w32) (σ : RState) (l : Loc)
    (m : TryPreAcceptReply) (hdead : False) :
    {{ hdCtx (GF := GF) γ i r rr L p Rext ord ∗ ownRep γ i r σ ∗ ownTryPreAcceptReply l m (DFrac.own 1) ∗
        repFrag γ i (hTryPreAcceptReply σ m).1 ∗ outsOk γ i (hTryPreAcceptReply σ m).2 }}
      (App (Val (r @!! go.GoType.PointerType epaxos.Replica.ty @!! go!"handleTryPreAcceptReply"))
        (Val #l))
    {{ RET #(); repDone γ i r }} := hdead.elim

end heap

end Perennial.github_com.imdea_software.swiftpaxos_epaxos
