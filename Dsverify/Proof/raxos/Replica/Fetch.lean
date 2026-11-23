/-
Package `replica`: `Recorder.HandleFetch` and `Recorder.HandleDecisions` (the recorder's answers
to `FetchBatches` and `InformDecision`).
-/
module

public import Dsverify.Proof.raxos.Replica.Handlers

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.deprecated false

namespace Perennial.raxos


open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net
open Perennial.raxos.pure Perennial.raxos.msg
open raxos.replica.src
open hyp.grpc (handlerOk replyOk decOk)
open models_lab.pbcodec (PbCodec)

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [π : NetProtoGS] [qv : hyp.QpVocab GF]
variable [raxos.replica.src.Assumptions] [raxos.proto.client.Assumptions]
  [raxos.examples.quepaxanet.Assumptions]

attribute [local instance] hyp.qpCodec
 

set_option goose.wp.extras true

theorem wp_convertToDecideResponseClientBatchMessages (re : Loc) (msl : GoSlice) (ps : List Loc)
    (cmds : List GoString) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.raxos.replica.src ∗ msl ↦*□ ps ∗
        repList repCSingle ps .discard cmds }}
      (App (Val (re @!! go.GoType.PointerType Recorder.ty @!!
        go!"convertToDecideResponseClientBatchMessages")) (Val #msl))
    {{ (rt : GoSlice), RET #rt; ∃ qs, rt ↦* qs ∗ repList repDRSingle qs .discard cmds }} := by
  wp_start as ⟨#Hms, #Hrep⟩
  ihave %Hlen := ownSlice_len $$ Hms
  ihave %Hlc : ⌜ps.length = cmds.length⌝ $$ []
  · iunfold repList at Hrep; icases Hrep with ⟨%H, -⟩; ipureintro; exact H
  wp_auto
  wp_apply (wp_slice_make2 (V := Loc) _) as %sl ⟨Hsl, Hcap⟩
  · ipureintro; word
  ihave HI : (∃ (i : w64) (sl : GoSlice) (zs : List Loc), "i" ∷ i_ptr ↦ i ∗
      "rt" ∷ rt_ptr ↦ sl ∗ "Hsl" ∷ sl ↦* zs ∗ "Hcap" ∷ ownSliceCap Loc sl (DFrac.own 1) ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z msl.len ∧ zs.length = sint.nat i⌝ ∗
      "#Hpre" ∷ repList repDRSingle zs .discard (cmds.take (sint.nat i)) :
      IProp GF) $$ [i rt Hsl Hcap]
  · iexists _, _, _
    iframe
    isplitr
    · ipureintro; simp only [List.length_replicate]; refine ⟨by word, by word, by word⟩
    · simp only [show sint.nat (W64 0) = 0 from rfl, List.take_zero, List.replicate_zero]
      iapply repList_nil
  wp_for HI
  wp_if_destruct
  · have Hb : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z msl.len := ⟨Hi.1, by simpa [goose_wp_simp_extra] using Hif⟩
    list_elem ps (sint.nat i) as q
    list_elem cmds (sint.nat i) as c
    ihave #Hq : repCSingle q .discard c $$ []
    · iunfold repList at Hrep
      icases Hrep with ⟨-, Hs⟩
      ihave Hx := BigSepL.bigSepL_lookup (Φ := fun i p => iprop(∃ y, ⌜cmds[i]? = some y⌝ ∗
        repCSingle p DFrac.discard y)) Hq_lookup $$ Hs
      icases Hx with ⟨%y, %Hy, Hx⟩
      rw [Hc_lookup] at Hy; cases Hy; iexact Hx
    iunfold repCSingle at Hq
    icases Hq with ⟨%xq, #Hxq, %Hxm⟩
    simp only [Hb, _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index msl (sint.Z i) ps _ q Hi.1 $$ [] as -
    · iframe #; ipureintro; exact Hq_lookup
    irename «$sl0» => Hnq
    generalize «$sl0_ptr» = nq at *
    imod ptDRSingle_share ⊤ _ _ $$ Hnq with #Hnq
    wp_bind (App (Val (GoInstruction (CompositeLiteral (go.GoType.SliceType
      (go.GoType.PointerType DecideResponse_ClientBatch_SingleMessage.ty))))) (Val (LiteralValueV _)))
    iapply wp_slice_literal (V := Loc)
      (t := go.GoType.PointerType DecideResponse_ClientBatch_SingleMessage.ty) [nq]
    wp_auto
    isplitl []
    · ipureintro; rfl
    iintro %l1 ⟨Hl1, -⟩
    wp_apply wp_slice_append (V := Loc) _ _ _ _ _ $$ [$Hsl $Hcap $Hl1] as %sl' ⟨Hsl, Hcap, -⟩
    wp_for_post
    iframe
    iexists _, sl', _
    iframe
    isplitr
    · ipureintro; simp only [List.length_append, List.length_singleton]
      refine ⟨by word, by word, by word⟩
    · rw [show sint.nat (i + W64 1) = sint.nat i + 1 by word, List.take_add_one, Hc_lookup]
      simp only [Option.toList_some]
      iapply repList_snoc $$ [$Hpre]
      unfold repDRSingle
      iexists _; iframe #; ipureintro; exact ⟨rfl, Hxm.2⟩
  · iapply HΦ
    iexists zs; iframe
    have e2 : cmds.take (sint.nat i) = cmds := List.take_of_length_le (by word)
    have e3 : repList (GF := GF) repDRSingle zs .discard cmds =
        repList repDRSingle zs .discard (cmds.take (sint.nat i)) := by rw [e2]
    rw [e3]
    iexact Hpre

theorem wp_HandleFetch (γ : QNames) (k : Nat) (re req : Loc) (ids : List GoString) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.raxos.replica.src ∗ isRecorder γ k re ∗
        repDReq req .discard ids }}
      (App (Val (re @!! go.GoType.PointerType Recorder.ty @!! go!"HandleFetch")) (Val #req))
    {{ (resp : Loc), RET #resp; ∃ (x : DecideResponse) (qs : List Loc) (bs : List Batch),
        resp ↦ x ∗ x.ClientBatches' ↦* qs ∗ repList repDRBatch qs .discard bs ∗
        ⌜(∀ b ∈ bs, batchFit b) ∧ x.unknownFields'.len = W64 0⌝ ∗
        [∗list] b ∈ bs, batchReg γ b.id b }} := by
  wp_start as ⟨#Hre, #Hreq⟩
  ihave #Hre' := Hre
  iunfold isRecorder at Hre'
  icases Hre' with ⟨%cb, %γs, %ch, %γc, %mu, #Hcb, #Hst, -⟩
  iunfold repDReq at Hreq
  icases Hreq with ⟨%x, #Hx, %Hxu, #Hids⟩
  ihave %Hlen := ownSlice_len $$ Hids
  wp_auto
  wp_apply (wp_slice_make2 (V := Loc) _) as %sl ⟨Hsl, Hcap⟩
  · ipureintro; word
  ihave HI : (∃ (i : w64) (xr : DecideResponse) (qs : List Loc) (bs : List Batch),
      "i" ∷ i_ptr ↦ i ∗ "response" ∷ response_ptr ↦ xr ∗
      "Hsl" ∷ xr.ClientBatches' ↦* qs ∗ "Hcap" ∷ ownSliceCap Loc xr.ClientBatches' (DFrac.own 1) ∗
      "#Hbs" ∷ repList repDRBatch qs .discard bs ∗ "%Hbok" ∷ ⌜∀ b ∈ bs, batchFit b⌝ ∗
      "#Hreg" ∷ ([∗list] b ∈ bs, batchReg γ b.id b) ∗ "%Hi" ∷ ⌜0 ≤ sint.Z i⌝ ∗
      "%Hxru" ∷ ⌜xr.unknownFields'.len = W64 0⌝ : IProp GF)
      $$ [i response Hsl Hcap]
  · rw [show List.replicate 0 (zero_val Loc) = ([] : List Loc) from rfl]
    iexists _, _, [], []
    iframe
    isplitl []
    · iapply repList_nil
    isplitr
    · ipureintro; simp
    isplitl []
    · iapply BigSepL.bigSepL_nil.2; iempintro
    · ipureintro; exact ⟨by word, rfl⟩
  wp_for HI
  wp_if_destruct
  · have Hb : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z x.Ids'.len := ⟨Hi, by simpa [goose_wp_simp_extra] using Hif⟩
    list_elem ids (sint.nat i) as xid
    simp only [Hb, _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index _ (sint.Z i) ids _ xid Hi $$ [] as -
    · iframe #; ipureintro; exact Hxid_lookup
    wp_apply store_get_proof γ γs cb xid false $$ [$Hst] as %v %ok ⟨-, Hok⟩
    · simp only [Bool.false_eq_true, ↓reduceIte]; itrivial
    cases ok <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> wp_auto
    · wp_for_post
      iframe
      iexists _, _, _, bs
      iframe
      iframe #
      ipureintro; refine ⟨Hbok, by word⟩
    · icases Hok with ⟨%b, ⟨%Hbid, %Hbok'⟩, #Hcb, #Hbr, -⟩
      iunfold repCBVal at Hcb
      icases Hcb with ⟨%mps, %Hvf, #Hmps, #Hmreps⟩
      wp_apply wp_convertToDecideResponseClientBatchMessages re _ mps b.cmds $$ [$Hmps $Hmreps]
        as %rt ⟨%rqs, Hrt, #Hrqs⟩
      ipersist Hrt
      irename «$sl0» => Hnq
      generalize «$sl0_ptr» = nq at *
      imod ptDRBatch_share ⊤ _ _ $$ Hnq with #Hnq
      wp_bind (App (Val (GoInstruction (CompositeLiteral (go.GoType.SliceType
        (go.GoType.PointerType DecideResponse_ClientBatch.ty))))) (Val (LiteralValueV _)))
      iapply wp_slice_literal (V := Loc) (t := go.GoType.PointerType DecideResponse_ClientBatch.ty) [nq]
      wp_auto
      isplitl []
      · ipureintro; rfl
      iintro %l1 ⟨Hl1, -⟩
      wp_apply wp_slice_append (V := Loc) _ _ _ _ _ $$ [$Hsl $Hcap $Hl1] as %sl' ⟨Hsl, Hcap, -⟩
      wp_for_post
      iframe
      iexists _, _, qs ++ [nq], bs ++ [b]
      iframe
      isplitl []
      · iapply repList_snoc $$ [$Hbs]
        unfold repDRBatch
        iexists _, rqs
        iframe #
        ipureintro; exact ⟨rfl, Hvf.1, Hvf.2.1⟩
      isplitr
      · ipureintro; intro b' hb'
        rcases List.mem_append.1 hb' with h | h
        · exact Hbok b' h
        · simp at h; subst h; exact Hbok'
      isplitl []
      · iapply (BigSepL.bigSepL_snoc (Φ := fun _ b => batchReg γ b.id b)).2
        iframe #; rw [Hbid]; iexact Hbr
      · ipureintro; word
  · iapply HΦ
    iexists _, qs, bs
    iframe; iframe #; ipureintro; exact ⟨Hbok, Hxru⟩

theorem wp_GRPCConnection_FetchBatches (γ : QNames) (k : Nat) (gc re lin : Loc)
    (ids : List GoString) (ctx : GoInterface) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.raxos.replica.src ∗
        gc.[GRPCConnection, go!"Recorder"] ↦□ re ∗ isRecorder γ k re ∗ repDReq lin .discard ids }}
      (App (App (Val (gc @!! go.GoType.PointerType GRPCConnection.ty @!! go!"FetchBatches"))
        (Val #ctx)) (Val #lin))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); ⌜err = interface.nil⌝ ∗
        ∃ bs, repDResp resp .discard bs ∗ ⌜∀ b ∈ bs, batchFit b⌝ ∗
          [∗list] b ∈ bs, batchReg γ b.id b }} := by
  wp_start as ⟨#Hgc, #Hre, #Hreq⟩
  wp_auto
  wp_apply +noauto wp_HandleFetch γ k re lin ids $$ [$Hre $Hreq]
    as %resp ⟨%x, %qs, %bs, Hx, Hqs, #Hbs, %Hbok, #Hreg⟩
  imod ptDResp_share ⊤ _ _ $$ Hx with #Hx
  ipersist Hqs
  wp_auto
  iapply HΦ
  isplitr
  · ipureintro; rfl
  iexists bs
  iframe #
  isplitl []
  · unfold repDResp; iexists x, qs; iframe #; ipureintro; exact Hbok.2
  · ipureintro; exact Hbok.1

theorem fetch_handlerOk (γ : QNames) (k : Nat) (gc re : Loc) :
    isPkgInit (PROP := IProp GF) pkg_id.raxos.replica.src ∗
      gc.[GRPCConnection, go!"Recorder"] ↦□ re ∗ isRecorder γ k re ⊢
    handlerOk qv.grpc (connIface gc) (functions _Consensus_FetchBatches_Handler []) (fetchSpec γ) := by
  iintro ⟨#Hpkg, #Hgc, #Hre⟩
  unfold handlerOk
  imodintro
  iintro %ctx %cd %dec %Got %Θ #Hctx Hdec HΘ
  wp_func_call
  wp_call
  wp_auto
  irename «$r0» => Hin
  generalize «$r0_ptr» = lin at *
  iunfold decOk at Hdec
  wp_apply Hdec $$ %(interface.mkOk (go.GoType.PointerType DecideRequest.ty) #lin)
      %(fun bs b => if b then iprop(∃ v,
        (⌜∃ v0, (∀ s ∈ v0, strOk s) ∧ encDReq v0 = bs⌝ -∗ repDReq lin (DFrac.own 1) v) ∗
        ⌜∀ v0, (∀ s ∈ v0, strOk s) → encDReq v0 = bs → v = v0⌝) else iprop(True)) [Hin]
      as %err Herr
  · iintro %bs
    rw [show (PbCodec.unmarshal (GF := GF)) = unmarshalPre from rfl]
    unfold unmarshalPre
    iright; iright; ileft
    iexists lin
    isplitr
    · ipureintro; rfl
    iframe Hin
    unfold decInto
    isplit
    · iintro %v Hv %Hv0
      simp only [↓reduceIte]
      iexists v; iframe; ipureintro; exact Hv0
    · simp only [Bool.false_eq_true, ↓reduceIte]; itrivial
  icases Herr with (⟨%He, Hv⟩ | ⟨%He, #Herr, -⟩)
  rotate_left
  · rcases err with ei | _
    · wp_auto
      iapply HΘ; iright; iframe #; ipureintro; exact He
    · exact absurd rfl He
  subst He
  wp_auto
  icases Hv with ⟨%bs, %Φ, HS, HGot, %v, Hv, %Hv0⟩
  iunfold fetchSpec at HS
  icases HS with ⟨%ids, ⟨%Hbs, %Hids⟩, HΦ⟩
  ihave Hv := Hv $$ %(⟨ids, Hids, Hbs.symm⟩ : ∃ v0, (∀ s ∈ v0, strOk s) ∧ encDReq v0 = bs)
  have Hvm := Hv0 ids Hids Hbs.symm
  subst Hvm
  imod repDReq_persist ⊤ _ _ _ $$ Hv with #Hv
  have Hts : go.typeSetContains (go.GoType.PointerType GRPCConnection.ty) ConsensusServer.ty =
    true := by go_type_set
  simp only [Hts, ↓reduceIte]
  wp_auto
  wp_apply wp_GRPCConnection_FetchBatches γ k gc re lin v _ $$ [$Hgc $Hre $Hv]
    as %resp %err ⟨%Herr, %bs', #Hrr, %Hbok, #Hreg⟩
  subst Herr
  iapply HΘ
  ileft
  isplitr
  · ipureintro; rfl
  iexists Φ
  iframe HGot
  unfold replyOk
  iright
  isplitr
  · ipureintro; nofun
  rw [show (PbCodec.marshal (GF := GF)) = marshalPre from rfl]
  unfold marshalPre
  iright; iright; iright; ileft
  iexists resp, DFrac.discard, bs'
  isplitr
  · ipureintro; rfl
  iframe #
  iintro -
  isplit
  · iintro - %bs'' %Hbs''
    cases Hbs''
    iapply HΦ
    iframe #; ipureintro; exact Hbok
  · iintro %Hn; exact absurd (fun b h => (Hbok b h).1) Hn

theorem wp_HandleDecisions (γ : QNames) (k : Nat) (re req : Loc) (ds : List DSlot) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.raxos.replica.src ∗ isRecorder γ k re ∗
        repDecs req .discard ds ∗ ⌜∀ d ∈ ds, dslotOk d⌝ ∗
        [∗list] d ∈ ds, decided γ d.index d.ids }}
      (App (Val (re @!! go.GoType.PointerType Recorder.ty @!! go!"HandleDecisions")) (Val #req))
    {{ RET #(); True }} := by
  wp_start as ⟨#Hre, #Hreq, %Hok, #Hdec⟩
  ihave #Hre' := Hre
  iunfold isRecorder at Hre'
  icases Hre' with ⟨%cb, %γs, %ch, %γc, %mu, #Hcb, #Hst, #Hch, #Hchb, #Hname, #Hmu, #Hmux, #Hinv, %Hk⟩
  iunfold repDecs at Hreq
  icases Hreq with ⟨%x, %sps, #Hx, %Hxu, #Hsps, #Hslots⟩
  wp_auto
  wp_if_destruct
  · wp_apply (wp_slice_make2 (V := w64) _) as %isl ⟨Hisl, Hicap⟩
    · ipureintro; word
    wp_apply (wp_slice_make2 (V := GoSlice) _) as %dsl ⟨Hdsl, Hdcap⟩
    · ipureintro; word
    wp_apply (wp_slice_make2 (V := w32) _) as %psl ⟨Hpsl, Hpcap⟩
    · ipureintro; word
    ihave %Hspl := ownSlice_len $$ Hsps
    ihave %Hsl : ⌜sps.length = ds.length⌝ $$ []
    · iunfold repList at Hslots; icases Hslots with ⟨%H, -⟩; ipureintro; exact H
    ihave HI : (∃ (i : w64) (is : List w64) (dss : List GoSlice) (ps : List w32)
        (isl dsl psl : GoSlice),
        "i" ∷ i_ptr ↦ i ∗
        "d" ∷ d_ptr ↦ ({ indexes' := isl, decisions' := dsl, proposers' := psl } : Decision) ∗
        "Hisl" ∷ isl ↦* is ∗ "Hicap" ∷ ownSliceCap w64 isl (DFrac.own 1) ∗
        "Hdsl" ∷ dsl ↦* dss ∗ "Hdcap" ∷ ownSliceCap GoSlice dsl (DFrac.own 1) ∗
        "Hpsl" ∷ psl ↦* ps ∗ "Hpcap" ∷ ownSliceCap w32 psl (DFrac.own 1) ∗
        "#Hacc" ∷ decAcc γ is ps dss ∗
        "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z x.DecidedSlots'.len ∧ is.length = sint.nat i⌝ :
          IProp GF)
        $$ [i d Hisl Hicap Hdsl Hdcap Hpsl Hpcap]
    · iexists _, _, _, _, isl, dsl, psl
      simp only [show sint.nat (W64 0) = 0 from rfl, List.replicate_zero]
      iframe
      isplitl []
      · iapply decAcc_nil
      · ipureintro; refine ⟨by word, by word, by simp; rfl⟩
    wp_for HI
    wp_if_destruct
    · have Hb : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z x.DecidedSlots'.len := ⟨Hi.1, by simpa [goose_wp_simp_extra] using Hif⟩
      list_elem sps (sint.nat i) as q
      list_elem ds (sint.nat i) as dd
      ihave #Hq : repDecSlot q .discard dd $$ []
      · iunfold repList at Hslots
        icases Hslots with ⟨-, Hs⟩
        ihave Hx := BigSepL.bigSepL_lookup (Φ := fun i p => iprop(∃ y, ⌜ds[i]? = some y⌝ ∗
          repDecSlot p DFrac.discard y)) Hq_lookup $$ Hs
        icases Hx with ⟨%y, %Hy, Hx⟩
        rw [Hdd_lookup] at Hy; cases Hy; iexact Hx
      ihave #Hddd : decided γ dd.index dd.ids $$ []
      · iapply BigSepL.bigSepL_lookup (Φ := fun _ d => decided γ d.index d.ids) Hdd_lookup $$ Hdec
      have Hddok : dslotOk dd := Hok dd (List.mem_of_getElem? Hdd_lookup)
      iunfold repDecSlot at Hq
      icases Hq with ⟨%xq, #Hxq, %Hxqu, %Hxqf, #Hids⟩
      simp only [Hb, _root_.and_self, ↓reduceIte]
      wp_apply wp_load_slice_index _ (sint.Z i) sps _ q Hi.1 $$ [] as -
      · iframe #; ipureintro; exact Hq_lookup
      wp_bind (App (Val (GoInstruction (CompositeLiteral (go.GoType.SliceType go.int))))
        (Val (LiteralValueV _)))
      iapply wp_slice_literal (V := w64) (t := go.int) [xq.Index']
      wp_auto
      isplitl []
      · ipureintro; rfl
      iintro %l1 ⟨Hl1, -⟩
      wp_apply wp_slice_append (V := w64) _ _ _ _ _ $$ [$Hisl $Hicap $Hl1] as %isl' ⟨Hisl, Hicap, -⟩
      simp only [Hb, _root_.and_self, ↓reduceIte]
      wp_apply wp_load_slice_index _ (sint.Z i) sps _ q Hi.1 $$ [] as -
      · iframe #; ipureintro; exact Hq_lookup
      wp_bind (App (Val (GoInstruction (CompositeLiteral (go.GoType.SliceType
        (go.GoType.SliceType go.string))))) (Val (LiteralValueV _)))
      iapply wp_slice_literal (V := GoSlice) (t := go.GoType.SliceType go.string) [xq.Ids']
      wp_auto
      isplitl []
      · ipureintro; rfl
      iintro %l2 ⟨Hl2, -⟩
      wp_apply wp_slice_append (V := GoSlice) _ _ _ _ _ $$ [$Hdsl $Hdcap $Hl2] as %dsl' ⟨Hdsl, Hdcap, -⟩
      simp only [Hb, _root_.and_self, ↓reduceIte]
      wp_apply wp_load_slice_index _ (sint.Z i) sps _ q Hi.1 $$ [] as -
      · iframe #; ipureintro; exact Hq_lookup
      wp_bind (App (Val (GoInstruction (CompositeLiteral (go.GoType.SliceType go.int32))))
        (Val (LiteralValueV _)))
      iapply wp_slice_literal (V := w32) (t := go.int32) [_]
      wp_auto
      isplitl []
      · ipureintro; rfl
      iintro %l3 ⟨Hl3, -⟩
      wp_apply wp_slice_append (V := w32) _ _ _ _ _ $$ [$Hpsl $Hpcap $Hl3] as %psl' ⟨Hpsl, Hpcap, -⟩
      wp_for_post
      iframe
      iexists _, _, _, _, isl', dsl', psl'
      iframe
      isplitl []
      · iapply decAcc_snoc γ is ps dss xq.Index' _ xq.Ids' dd.ids Hddok.2.2 $$ [$Hacc $Hids]
        rw [Hxqf.1]; iexact Hddd
      · ipureintro; simp only [List.length_append, List.length_singleton]
        refine ⟨by word, by word, by word⟩
    · ihave %Hisl_len := ownSlice_len $$ Hisl
      ipersist Hisl
      ipersist Hdsl
      ipersist Hpsl
      wp_apply wp_bag_send γc ch _ (decisionP γ) $$ [$Hchb]
      · unfold decisionP
        isplitl []
        · iapply decidedSlotsP_of $$ [$Hisl $Hpsl $Hdsl $Hacc]
        · ipureintro; dsimp only; simp at Hif; word
      iapply HΦ; itrivial
  · iapply HΦ; itrivial

theorem wp_GRPCConnection_InformDecision (γ : QNames) (k : Nat) (gc re lin : Loc)
    (ds : List DSlot) (ctx : GoInterface) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.raxos.replica.src ∗
        gc.[GRPCConnection, go!"Recorder"] ↦□ re ∗ isRecorder γ k re ∗ repDecs lin .discard ds ∗
        ⌜∀ d ∈ ds, dslotOk d⌝ ∗ [∗list] d ∈ ds, decided γ d.index d.ids }}
      (App (App (Val (gc @!! go.GoType.PointerType GRPCConnection.ty @!! go!"InformDecision"))
        (Val #ctx)) (Val #lin))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); ⌜err = interface.nil⌝ ∗
        repEmpty resp .discard }} := by
  wp_start as ⟨#Hgc, #Hre, #Hreq, %Hok, #Hdec⟩
  wp_auto
  irename «$r0» => He
  generalize «$r0_ptr» = le at *
  imod ptEmpty_share ⊤ _ _ $$ He with #He
  wp_apply wp_HandleDecisions γ k re lin ds $$ [$Hre $Hreq $Hdec]
  · ipureintro; exact Hok
  iapply HΦ
  isplitr
  · ipureintro; rfl
  unfold repEmpty; iexists _; iframe #; ipureintro; rfl

theorem inform_handlerOk (γ : QNames) (k : Nat) (gc re : Loc) :
    isPkgInit (PROP := IProp GF) pkg_id.raxos.replica.src ∗
      gc.[GRPCConnection, go!"Recorder"] ↦□ re ∗ isRecorder γ k re ⊢
    handlerOk qv.grpc (connIface gc) (functions _Consensus_InformDecision_Handler []) (informSpec γ) := by
  iintro ⟨#Hpkg, #Hgc, #Hre⟩
  unfold handlerOk
  imodintro
  iintro %ctx %cd %dec %Got %Θ #Hctx Hdec HΘ
  wp_func_call
  wp_call
  wp_auto
  irename «$r0» => Hin
  generalize «$r0_ptr» = lin at *
  iunfold decOk at Hdec
  wp_apply Hdec $$ %(interface.mkOk (go.GoType.PointerType Decisions.ty) #lin)
      %(fun bs b => if b then iprop(∃ v,
        (⌜∃ v0, (∀ d ∈ v0, dslotOk d) ∧ encDecs v0 = bs⌝ -∗ repDecs lin (DFrac.own 1) v) ∗
        ⌜∀ v0, (∀ d ∈ v0, dslotOk d) → encDecs v0 = bs → v = v0⌝) else iprop(True)) [Hin]
      as %err Herr
  · iintro %bs
    rw [show (PbCodec.unmarshal (GF := GF)) = unmarshalPre from rfl]
    unfold unmarshalPre
    iright; iright; iright; iright; ileft
    iexists lin
    isplitr
    · ipureintro; rfl
    iframe Hin
    unfold decInto
    isplit
    · iintro %v Hv %Hv0
      simp only [↓reduceIte]
      iexists v; iframe; ipureintro; exact Hv0
    · simp only [Bool.false_eq_true, ↓reduceIte]; itrivial
  icases Herr with (⟨%He, Hv⟩ | ⟨%He, #Herr, -⟩)
  rotate_left
  · rcases err with ei | _
    · wp_auto
      iapply HΘ; iright; iframe #; ipureintro; exact He
    · exact absurd rfl He
  subst He
  wp_auto
  icases Hv with ⟨%bs, %Φ, HS, HGot, %v, Hv, %Hv0⟩
  iunfold informSpec at HS
  icases HS with ⟨%ds, ⟨%Hbs, %Hds⟩, #Hdecs, HΦ⟩
  ihave Hv := Hv $$ %(⟨ds, Hds, Hbs.symm⟩ : ∃ v0, (∀ d ∈ v0, dslotOk d) ∧ encDecs v0 = bs)
  have Hvm := Hv0 ds Hds Hbs.symm
  subst Hvm
  imod repDecs_persist ⊤ _ _ _ $$ Hv with #Hv
  have Hts : go.typeSetContains (go.GoType.PointerType GRPCConnection.ty) ConsensusServer.ty =
    true := by go_type_set
  simp only [Hts, ↓reduceIte]
  wp_auto
  wp_apply wp_GRPCConnection_InformDecision γ k gc re lin v _ $$ [$Hgc $Hre $Hv $Hdecs]
    as %resp %err ⟨%Herr, #Hrr⟩
  · ipureintro; exact Hds
  subst Herr
  iapply HΘ
  ileft
  isplitr
  · ipureintro; rfl
  iexists Φ
  iframe HGot
  unfold replyOk
  iright
  isplitr
  · ipureintro; nofun
  rw [show (PbCodec.marshal (GF := GF)) = marshalPre from rfl]
  unfold marshalPre
  iright; iright; iright; iright; iright; ileft
  iexists resp, DFrac.discard
  isplitr
  · ipureintro; rfl
  iframe #
  iintro - %bs'' %Hbs''
  cases Hbs''
  iexact HΦ

end proof

end Perennial.raxos
