/-
The definitions, specs and lemmas of `TableAcks.lean` that its proofs do not need (split out for the import tiers, CLAUDE.md "Import tiers": its importers that are not linking modules import this module, and see no proof).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.TableAcksPure
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

namespace swift.tbl

/-- A slow ack as the Go struct. -/
def slowV (s : sp.SlowAck) : swift.MLightSlowAck := ⟨s.rep, s.bal, ofCmdId s.id⟩

section specs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF]

/-- `(*MAcks).Unmarshal(br)`: without an error, the bytes read are the body of a well-formed
`.acks fs ss`, which `t` represents (`swift.msgRepM`'s shape). -/
abbrev MAcks.Unmarshal.specS : Prop :=
  ∀ (t : Loc) (v : swift.MAcks) (br : Loc) (rd : GoInterface) (I : List w8 → IProp netDistGF)
    (R : List w8),
  {{ ctxV ∗ bufio.readerOk rd I ∗ sp.streamLaw br rd I R (sp.nextOk (W8 13)) ∗
      bufio.ownReader br rd I R ∗ t ↦ v }}
    (App (Val (t @!! go.GoType.PointerType swift.MAcks.ty @!! go!"Unmarshal"))
      (Val #(interface.mkOk (go.GoType.PointerType bufio.Reader.ty) #br)))
  {{ (err : GoInterface), RET #err; ∃ data : List w8, bufio.ownReader br rd I (R ++ data) ∗
      ((⌜err = interface.nil⌝ ∗ ∃ (fs : List sp.FastAck) (ss : List sp.SlowAck) (fsl ssl : GoSlice)
          (fps : List (swift.MFastAck × sp.FastAck)),
          ⌜data = (sp.Msg.acks fs ss).body ∧ (sp.Msg.acks fs ss).wf ∧ fps.map Prod.snd = fs⌝ ∗
          t ↦ swift.MAcks.mk fsl ssl ∗ fsl ↦* fps.map Prod.fst ∗ ssl ↦* ss.map slowV ∗
          [∗list] p ∈ fps, swift.fastAckRepr p.1 p.2) ∨
        (⌜err ≠ interface.nil⌝ ∗ ∃ v' : swift.MAcks, t ↦ v')) }}

end specs

section proofs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF] [SwiftKitDeps]
variable [swift.Assumptions] [io.Assumptions] [errors.Assumptions]
  [bufio.Assumptions]

set_option goose.wp.extras true

omit [swift.Assumptions] [io.Assumptions] [errors.Assumptions]
  [bufio.Assumptions] in
/-- The first 4 bytes of a 10-byte buffer, as the slice `b[:4]`. -/
theorem slice_take4 (p : Loc) (xs : List w8) (hl : xs.length = 10) :
    (slice.mk p (W64 10) (W64 10) ↦* xs : IProp netDistGF) ⊢
      slice.mk p (W64 4) (W64 10) ↦* xs.take 4 := by
  rw [ownSlice_unseal]; unfold ownSliceDef
  iintro (%H | ⟨H, -⟩)
  · exfalso; obtain ⟨h1, -⟩ := H; simp [slice.nil] at h1
  iright
  simp only
  icases (array_split (V := w8) (W64 4) p (DFrac.own 1) _ _ (by word)).1 $$ H
    with ⟨H, -⟩
  isplitl [H]
  · iExactEq H; rfl
  · ipureintro; simp [hl]; decide

omit go_gctx hG sem [swift.Assumptions] [io.Assumptions] [errors.Assumptions]
  [bufio.Assumptions] in
theorem acks_body (fs : List sp.FastAck) (ss : List sp.SlowAck) :
    (sp.Msg.acks fs ss).body = sp.varintLen fs.length ++ (fs.map sp.FastAck.enc).flatten ++
      sp.varintLen ss.length ++ (ss.map sp.SlowAck.enc).flatten := rfl

theorem four_of {data : List w8} {u : List w8} (hl : data.length ≤ u.length) (hu : u.length = 4)
    (he : sint.Z (W64 4) ≤ (data.length : Int)) : ∃ a b c d, data = [a, b, c, d] := by
  have : sint.Z (W64 4) = 4 := rfl
  match data with
  | [a, b, c, d] => exact ⟨a, b, c, d, rfl⟩
  | [] | [_] | [_, _] | [_, _, _] => rw [this] at he; simp at he
  | _ :: _ :: _ :: _ :: _ :: _ => simp at hl; omega

set_option hygiene false in
/-- `ReadAtLeast(wire, bs, 4)` into `b[:4]` (an error returns), then the 4 bytes' loads. -/
macro "rd4" a:ident b:ident c:ident d:ident : tactic => `(tactic| (
  try wp_auto
  try rw [show sint.Z (W64 0) = 0 from rfl, go.arrayIndexRef_0, show W64 4 - W64 0 = W64 4 from rfl,
    show W64 10 - W64 0 = W64 10 from rfl]
  try wp_auto
  wp_apply bufio.wp_ReadAtLeast _ _ _ _ [_, _, _, _] (W64 4) (by simp; decide) $$
    [Hown Hb4] as %n0 %err ⟨%data0, %Hd0, Hb4, Hown, #He0⟩
  · iframe Hown Hb4 Hbr
  obtain ⟨-, hdl0, herr0⟩ := Hd0
  rcases err with e0 | _
  · subst hB
    wp_auto
    wp_for_post
    iapply HΦ
    iexists _
    isplitl [Hown]
    · iExactEq Hown; simp only [List.append_assoc]; rfl
    iright
    isplitr
    · ipureintro; intro h; cases h
    iexists _
    iexact Ht
  obtain ⟨$a, $b, $c, $d, rfl⟩ := four_of hdl0 rfl (herr0.1 rfl)
  try isimp only [List.length_cons, List.length_nil, List.drop_succ_cons, List.drop_zero,
    List.drop_nil, List.append_nil, Nat.reduceAdd] at Hb4
  try rw [List.append_assoc B _ [$a, $b, $c, $d]]
  try wp_auto
  wp_apply wp_load_slice_index _ (sint.Z (W64 0)) _ _ _ (by decide) $$ [Hb4] as Hb4
  · iframe Hb4; ipureintro; rfl
  try wp_auto
  wp_apply wp_load_slice_index _ (sint.Z (W64 1)) _ _ _ (by decide) $$ [Hb4] as Hb4
  · iframe Hb4; ipureintro; rfl
  try wp_auto
  wp_apply wp_load_slice_index _ (sint.Z (W64 2)) _ _ _ (by decide) $$ [Hb4] as Hb4
  · iframe Hb4; ipureintro; rfl
  try wp_auto
  wp_apply wp_load_slice_index _ (sint.Z (W64 3)) _ _ _ (by decide) $$ [Hb4] as Hb4
  · iframe Hb4; ipureintro; rfl
  try wp_auto))

end proofs

end swift.tbl

end Perennial.github_com.imdea_software.swiftpaxos

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

namespace swift.tbl

section pureGob
variable [sp.GobFmt]

theorem fastAck_of_next {d : List w8} (h : sp.nextOk (W8 9) d) : fastAckNext d := by
  obtain ⟨m, w, hw, -, hc, hp⟩ := h
  cases m <;> simp [sp.Msg.code, sp.rpcTable] at hc
  exact ⟨_, w, hw, hp⟩

end pureGob

section entries
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF] [SwiftKitDeps]
variable [swift.Assumptions] [io.Assumptions] [errors.Assumptions]
  [bufio.Assumptions]

set_option goose.wp.extras true

theorem unmarshalOk_fastAck (wp_FA : MFastAck.Unmarshal.specS (hG := hG)) (l : Loc)
    (v : swift.MFastAck) :
    ctxV ∗ l ↦ v ⊢ sp.unmarshalOk (W8 9) (swift.msgRep (W8 9))
      (interface.mkOk (go.GoType.PointerType swift.MFastAck.ty) #l) := by
  iintro ⟨#Hctx, Hl⟩
  unfold sp.unmarshalOk
  iexists _
  isplitr
  · ipureintro; rfl
  iintro %br %rd %I %R %Φ #Hrd #Hlaw Hown HΦ
  ihave #Hlaw' := streamLaw_mono br rd I R _ fastAckNext (fun d hd => fastAck_of_next hd) $$ Hlaw
  iapply Iris.wp_fupd
  wp_apply wp_FA l v br rd I R $$ [$Hctx $Hrd $Hlaw' $Hown $Hl] as %err ⟨%data, Hown, Hres⟩
  icases Hres with (⟨%He, %f, %dsl, %csl, ⟨%Hd, %Hwf⟩, Ht, Hdsl, Hcsl⟩ | ⟨%He, -⟩)
  · imod ownSlice_persist $$ Hdsl with #Hdsl
    imod ownSlice_persist $$ Hcsl with #Hcsl
    imodintro
    iapply HΦ $$ Hown
    ileft
    isplitr
    · ipureintro; exact He
    iexists .fastAck f
    isplitr
    · ipureintro; subst Hd; exact sp.decodes_of_body rfl Hwf
    unfold swift.msgRep swift.msgRepM
    iexists l, _
    iframe Ht
    isplitr
    · ipureintro; rfl
    unfold swift.fastAckRepr
    iframe Hdsl Hcsl
    ipureintro; exact ⟨rfl, rfl, rfl, rfl⟩
  · imodintro
    iapply HΦ $$ Hown
    iright
    ipureintro; exact He

theorem wp_New_MAcks (o : Loc) :
    {{ (True : IProp netDistGF) }}
      (App (Val (o @!! go.GoType.PointerType swift.MAcks.ty @!! go!"New")) (Val #()))
    {{ (l : Loc), RET #(interface.mkOk (go.GoType.PointerType swift.MAcks.ty) #l);
        l ↦ (zero_val swift.MAcks) }} := by
  wp_start
  wp_auto
  wp_alloc_auto
  wp_auto
  iapply HΦ; iframe

/-- The persistent facts `MFastAck`'s entry uses: `ctxV`, the package, the pool's switch. -/
def ctxFA (v : Bool) : IProp netDistGF :=
  iprop(ctxV ∗ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.swift ∗
    typedPointsto (globalAddr swift.useFastAckPool) v DFrac.discard)

instance ctxFA_persistent (v : Bool) : Persistent (ctxFA (hG := hG) v) := by
  unfold ctxFA; infer_instance

theorem wp_New_MFastAck (wp_newFA : newFastAck.specP' (hG := hG)) (v : Bool) (o : Loc) :
    {{ ctxFA v }}
      (App (Val (o @!! go.GoType.PointerType swift.MFastAck.ty @!! go!"New")) (Val #()))
    {{ (l : Loc), RET #(interface.mkOk (go.GoType.PointerType swift.MFastAck.ty) #l);
        ∃ fa : swift.MFastAck, l ↦ fa }} := by
  wp_start as #Hctx
  iunfold ctxFA at Hctx
  icases Hctx with ⟨-, #Hpkg, #Hv⟩
  wp_auto
  wp_apply wp_newFA v $$ [$Hpkg $Hv] as %l Hl
  try wp_auto
  iapply HΦ $$ Hl

theorem newOk_fastAck (wp_FA : MFastAck.Unmarshal.specS (hG := hG))
    (wp_newFA : newFastAck.specP' (hG := hG)) (v : Bool) (o : Loc) :
    ctxFA v ⊢ sp.newOk (W8 9) (swift.msgRep (W8 9))
      (interface.mkOk (go.GoType.PointerType swift.MFastAck.ty) #o) := by
  apply newOk_of _ _ _ o (ctxFA v) (fun l => iprop(∃ fa : swift.MFastAck, l ↦ fa))
    (wp_New_MFastAck wp_newFA v o)
  intro l
  iintro ⟨#Hctx, %fa, Hl⟩
  iunfold ctxFA at Hctx
  icases Hctx with ⟨#HV, -, -⟩
  iapply unmarshalOk_fastAck wp_FA l fa $$ [$HV $Hl]

end entries

end swift.tbl

end Perennial.github_com.imdea_software.swiftpaxos
