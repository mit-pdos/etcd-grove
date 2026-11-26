/-
Package `proposer`: the recorders' gRPC client stubs (`consensus_grpc.pb.go`'s
`consensusClient.ESP`, `.FetchBatches`, `.InformDecision`), each one `cc.Invoke` with the
method's spec (`Proto.lean`) and the kit's codec (`Msg.lean`).
-/
module

public import Dsverify.Proof.raxos.Wire
public import Dsverify.Proof.raxos.Proposer.Strings

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.raxos


open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net
open Perennial.raxos.pure Perennial.raxos.msg
open models_lab.pbcodec (PbCodec)
open raxos.replica.src

namespace prop

section esp
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [π : NetProtoGS] [qv : hyp.QpVocab GF]
variable [raxos.replica.src.Assumptions] [raxos.proto.client.Assumptions]
  [raxos.examples.quepaxanet.Assumptions]

attribute [local instance] hyp.qpCodec

variable [gh : hyp.grpc.GrpcHyp qv.grpc]

/-- The recorder number of a recorder address. -/
theorem consensusMS_rec (γ : QNames) (r : Nat) (hr : 1 ≤ r ∧ r ≤ 5) :
    consensusMS (GF := GF) γ (recAddr r) go!"/Consensus/ESP" = some (espSpec γ r) ∧
    consensusMS (GF := GF) γ (recAddr r) go!"/Consensus/FetchBatches" = some (fetchSpec γ) ∧
    consensusMS (GF := GF) γ (recAddr r) go!"/Consensus/InformDecision" = some (informSpec γ) := by
  have e1 : (go!"/Consensus/FetchBatches" : GoString) ≠ go!"/Consensus/ESP" := by decide
  have e2 : (go!"/Consensus/InformDecision" : GoString) ≠ go!"/Consensus/ESP" := by decide
  have e3 : (go!"/Consensus/InformDecision" : GoString) ≠ go!"/Consensus/FetchBatches" := by decide
  refine ⟨?_, ?_, ?_⟩ <;> simp [consensusMS, recOfAddr_recAddr r hr, e1, e2, e3]

omit gh in
theorem pb_marshal_eq : (PbCodec.marshal (GF := GF)) = marshalPre := rfl
omit gh in
theorem pb_unmarshal_eq : (PbCodec.unmarshal (GF := GF)) = unmarshalPre := rfl

/-- What an ESP call to recorder `r` for the request `m` returns on success. -/
def espPost (γ : QNames) (r : Nat) (m : PM) (rr : RR) : IProp GF :=
  iprop(⌜rrOk rr⌝ ∗ (⌜rr = rrNotFound⌝ ∨
    ∃ p st, ⌜m.p = some p ∧ rr = rrOf st⌝ ∗ evIn γ (.record (r : Int) m.index m.s p.val st)))

set_option maxHeartbeats 800000 in
/-- `c.ESP(ctx, in)` on recorder `r`'s client: the reply (owned) of the recorder's `record`
event for the request, or the not-found reply; or an error. -/
theorem wp_ESP (γ : QNames) (r : Nat) (l cc : Loc) (ctx : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) (ml : Loc) (dq : DFrac) (m : PM) (opts : GoSlice)
    (Hopts : opts.len = W64 0 := by rfl) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.raxos.replica.src ∗ ⌜1 ≤ r ∧ r ≤ 5⌝ ∗
        l ↦□ (consensusClient.mk
          (interface.mkOk (go.GoType.PointerType google_golang_org.grpc.ClientConn.ty) #cc)) ∗
        qv.grpc.isClientConn cc (world γ) (recAddr r) ∗
        context.isContext ctx cd ∗ repPM ml dq m ∗ (⌜pmOk m⌝ -∗ pmFacts γ m) }}
      (App (App (App (Val (l @!! go.GoType.PointerType consensusClient.ty @!! go!"ESP"))
        (Val #(interface.ok ctx))) (Val #ml)) (Val #opts))
    {{ (out : Loc) (err : GoInterface), RET (PairV #out #err);
        (⌜err = interface.nil⌝ ∗ ∃ rr, repRR out (DFrac.own 1) rr ∗ espPost γ r m rr) ∨
        ⌜err ≠ interface.nil ∧ out = null⌝ }} := by
  wp_start as ⟨%Hr, #Hl, #Hcc, #Hctx, Hm, Hfacts⟩
  iStructNamed Hl
  wp_auto
  have hMS := (consensusMS_rec (GF := GF) γ r Hr).1
  wp_apply gh.Invoke cc (world γ) (recAddr r) ctx cd
    go!"/Consensus/ESP" (espSpec γ r) (interface.mkOk (go.GoType.PointerType ProposerMessage.ty) #ml)
    (interface.mkOk (go.GoType.PointerType RecorderResponse.ty) #«$r0_ptr») opts
    (fun rep => iprop(∃ rr, ⌜rep = encRR rr⌝ ∗ espPost γ r m rr)) iprop(True)
    («$r0_ptr» ↦ zero_val RecorderResponse)
    (fun rep ok => if ok then iprop(∃ v,
      (⌜∃ v0, rrOk v0 ∧ encRR v0 = rep⌝ -∗ repRR «$r0_ptr» (DFrac.own 1) v) ∗
      ⌜∀ v0, rrOk v0 → encRR v0 = rep → v = v0⌝) else iprop(True))
    $$ [Hm Hfacts «$r0»] as %err Hres
  · iframe #
    isplitr
    · ipureintro; exact hMS
    isplitr
    · ipureintro; exact Hopts
    isplitl [Hm Hfacts]
    · unfold hyp.grpc.encPre
      iright
      isplitr
      · ipureintro; intro h; cases h
      rw [pb_marshal_eq]
      unfold marshalPre
      ileft
      iexists ml, dq, m
      isplitr
      · ipureintro; rfl
      iPkgInit
      iframe Hm
      iintro Hm
      isplit
      · iintro %Hok
        isplitl
        · unfold espSpec
          iexists m
          isplitr
          · ipureintro; exact ⟨rfl, Hok⟩
          isplitl
          · iapply Hfacts; ipureintro; exact Hok
          iintro %rr ⟨%Hrr, H⟩
          iexists rr
          isplitr
          · ipureintro; rfl
          unfold espPost
          iframe H
          ipureintro; exact Hrr
        · itrivial
      · iintro -; itrivial
    iframe «$r0»
    imodintro
    iintro Hz %rep
    rw [pb_unmarshal_eq]
    unfold unmarshalPre
    iright; ileft
    iexists «$r0_ptr»
    isplitr
    · ipureintro; rfl
    iPkgInit
    iframe Hz
    unfold decInto
    isplit
    · iintro %v Hv %Hv
      simp only [↓reduceIte]
      iexists v
      iframe Hv
      ipureintro; exact Hv
    · simp only [Bool.false_eq_true, ↓reduceIte]; itrivial
  icases Hres with (⟨%He, -, %rep, ⟨%rr, %Hrep, Hpost⟩, %v, Hv, %Hv⟩ | ⟨%Hne, -⟩)
  · subst He
    wp_auto
    unfold espPost
    icases Hpost with ⟨%Hok, Hpost⟩
    ihave Hv := Hv $$ %(⟨rr, Hok, Hrep.symm⟩ : ∃ v0, rrOk v0 ∧ encRR v0 = rep)
    have := Hv rr Hok Hrep.symm
    subst this
    iapply HΦ
    ileft
    isplitr
    · ipureintro; rfl
    iexists v
    iframe Hv
    iframe Hpost
    ipureintro; exact Hok
  · rcases err with e | _
    · wp_auto
      iapply HΦ
      iright
      ipureintro; exact ⟨Hne, rfl⟩
    · exact absurd rfl Hne

set_option maxHeartbeats 800000 in
/-- `c.FetchBatches(ctx, in)` on recorder `r`'s client: registered batches (owned), or an error. -/
theorem wp_FetchBatches (γ : QNames) (r : Nat) (l cc : Loc) (ctx : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) (ml : Loc) (dq : DFrac) (ids : List GoString)
    (opts : GoSlice)
    (Hopts : opts.len = W64 0 := by rfl) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.raxos.replica.src ∗ ⌜1 ≤ r ∧ r ≤ 5⌝ ∗
        l ↦□ (consensusClient.mk
          (interface.mkOk (go.GoType.PointerType google_golang_org.grpc.ClientConn.ty) #cc)) ∗
        qv.grpc.isClientConn cc (world γ) (recAddr r) ∗
        context.isContext ctx cd ∗ repDReq ml dq ids }}
      (App (App (App (Val (l @!! go.GoType.PointerType consensusClient.ty @!! go!"FetchBatches"))
        (Val #(interface.ok ctx))) (Val #ml)) (Val #opts))
    {{ (out : Loc) (err : GoInterface), RET (PairV #out #err);
        (⌜err = interface.nil⌝ ∗ ∃ bs, repDResp out (DFrac.own 1) bs ∗ ⌜∀ b ∈ bs, batchFit b⌝ ∗
          [∗list] b ∈ bs, batchReg γ b.id b) ∨
        ⌜err ≠ interface.nil⌝ }} := by
  wp_start as ⟨%Hr, #Hl, #Hcc, #Hctx, Hm⟩
  wp_auto
  iStructNamed Hl
  wp_auto
  have hMS := (consensusMS_rec (GF := GF) γ r Hr).2.1
  wp_apply gh.Invoke cc (world γ) (recAddr r) ctx cd
    go!"/Consensus/FetchBatches" (fetchSpec γ) (interface.mkOk (go.GoType.PointerType DecideRequest.ty) #ml)
    (interface.mkOk (go.GoType.PointerType DecideResponse.ty) #«$r0_ptr») opts
    (fun rep => iprop(∃ bs, ⌜rep = encDResp bs ∧ ∀ b ∈ bs, batchFit b⌝ ∗
      [∗list] b ∈ bs, batchReg γ b.id b)) iprop(True)
    («$r0_ptr» ↦ zero_val DecideResponse)
    (fun rep ok => if ok then iprop(∃ v,
      (⌜∃ v0, (∀ b ∈ v0, batchOk b) ∧ encDResp v0 = rep⌝ -∗ repDResp «$r0_ptr» (DFrac.own 1) v) ∗
      ⌜∀ v0, (∀ b ∈ v0, batchOk b) → encDResp v0 = rep → v = v0⌝) else iprop(True))
    $$ [Hm «$r0»] as %err Hres
  · iframe #
    isplitr
    · ipureintro; exact hMS
    isplitr
    · ipureintro; exact Hopts
    isplitl [Hm]
    · unfold hyp.grpc.encPre
      iright
      isplitr
      · ipureintro; intro h; cases h
      rw [pb_marshal_eq]
      unfold marshalPre
      iright; iright; ileft
      iexists ml, dq, ids
      isplitr
      · ipureintro; rfl
      iPkgInit
      iframe Hm
      iintro Hm
      isplit
      · iintro %Hok
        isplitl
        · unfold fetchSpec
          iexists ids
          isplitr
          · ipureintro; exact ⟨rfl, Hok⟩
          iintro %bs ⟨%Hbs, H⟩
          iexists bs
          iframe H
          ipureintro; exact ⟨rfl, Hbs⟩
        · itrivial
      · iintro -; itrivial
    iframe «$r0»
    imodintro
    iintro Hz %rep
    rw [pb_unmarshal_eq]
    unfold unmarshalPre
    iright; iright; iright; ileft
    iexists «$r0_ptr»
    isplitr
    · ipureintro; rfl
    iPkgInit
    iframe Hz
    unfold decInto
    isplit
    · iintro %v Hv %Hv
      simp only [↓reduceIte]
      iexists v
      iframe Hv
      ipureintro; exact Hv
    · simp only [Bool.false_eq_true, ↓reduceIte]; itrivial
  icases Hres with (⟨%He, -, %rep, ⟨%bs, ⟨%Hrep, %Hok⟩, Hregs⟩, %v, Hv, %Hv⟩ | ⟨%Hne, -⟩)
  · subst He
    wp_auto
    ihave Hv := Hv $$ %(⟨bs, fun b hb => (Hok b hb).1, Hrep.symm⟩ :
      ∃ v0, (∀ b ∈ v0, batchOk b) ∧ encDResp v0 = rep)
    have := Hv bs (fun b hb => (Hok b hb).1) Hrep.symm
    subst this
    iapply HΦ
    ileft
    isplitr
    · ipureintro; rfl
    iexists v
    iframe Hv Hregs
    ipureintro; exact Hok
  · rcases err with e | _
    · wp_auto
      iapply HΦ
      iright
      ipureintro; exact Hne
    · exact absurd rfl Hne

set_option maxHeartbeats 800000 in
/-- `c.InformDecision(ctx, in)` on recorder `r`'s client, for decided slots. -/
theorem wp_InformDecision (γ : QNames) (r : Nat) (l cc : Loc) (ctx : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) (ml : Loc) (dq : DFrac) (ds : List DSlot)
    (opts : GoSlice)
    (Hopts : opts.len = W64 0 := by rfl) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.raxos.replica.src ∗ ⌜1 ≤ r ∧ r ≤ 5⌝ ∗
        l ↦□ (consensusClient.mk
          (interface.mkOk (go.GoType.PointerType google_golang_org.grpc.ClientConn.ty) #cc)) ∗
        qv.grpc.isClientConn cc (world γ) (recAddr r) ∗
        context.isContext ctx cd ∗ repDecs ml dq ds ∗
        ([∗list] d ∈ ds, decided γ d.index d.ids) }}
      (App (App (App (Val (l @!! go.GoType.PointerType consensusClient.ty @!! go!"InformDecision"))
        (Val #(interface.ok ctx))) (Val #ml)) (Val #opts))
    {{ (out : Loc) (err : GoInterface), RET (PairV #out #err); True }} := by
  wp_start as ⟨%Hr, #Hl, #Hcc, #Hctx, Hm, Hds⟩
  wp_auto
  iStructNamed Hl
  wp_auto
  have hMS := (consensusMS_rec (GF := GF) γ r Hr).2.2
  wp_apply gh.Invoke cc (world γ) (recAddr r) ctx cd
    go!"/Consensus/InformDecision" (informSpec γ) (interface.mkOk (go.GoType.PointerType Decisions.ty) #ml)
    (interface.mkOk (go.GoType.PointerType raxos.replica.src.Empty.ty) #«$r0_ptr») opts
    (fun _ => iprop(True)) iprop(True)
    («$r0_ptr» ↦ zero_val raxos.replica.src.Empty)
    (fun _ _ => iprop(True))
    $$ [Hm Hds «$r0»] as %err Hres
  · iframe #
    isplitr
    · ipureintro; exact hMS
    isplitr
    · ipureintro; exact Hopts
    isplitl [Hm Hds]
    · unfold hyp.grpc.encPre
      iright
      isplitr
      · ipureintro; intro h; cases h
      rw [pb_marshal_eq]
      unfold marshalPre
      iright; iright; iright; iright; ileft
      iexists ml, dq, ds
      isplitr
      · ipureintro; rfl
      iPkgInit
      iframe Hm
      iintro Hm
      isplit
      · iintro %Hok
        isplitl
        · unfold informSpec
          iexists ds
          isplitr
          · ipureintro; exact ⟨rfl, Hok⟩
          iframe Hds
        · itrivial
      · iintro -; itrivial
    iframe «$r0»
    imodintro
    iintro Hz %rep
    rw [pb_unmarshal_eq]
    unfold unmarshalPre
    iright; iright; iright; iright; iright; ileft
    iexists «$r0_ptr»
    isplitr
    · ipureintro; rfl
    iPkgInit
    iframe Hz
    unfold decInto
    isplit
    · iintro %v - -; itrivial
    · itrivial
  icases Hres with (⟨%He, -⟩ | ⟨%Hne, -⟩)
  · subst He
    wp_auto
    iapply HΦ; itrivial
  · rcases err with e | _
    · wp_auto
      iapply HΦ; itrivial
    · exact absurd rfl Hne

end esp

end prop

end Perennial.raxos
