/-
The definitions, specs and lemmas of `TableOptAcks.lean` that its proofs do not need (split out for the import tiers, CLAUDE.md "Import tiers": its importers that are not linking modules import this module, and see no proof).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.TableAcksDefs
@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

namespace swift.tbl

section specs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF]

/-- `(*MOptAcks).Unmarshal(br)`: without an error, the bytes read are the body of a
well-formed `.optAcks r b al`, which `t` represents (`swift.msgRepM`'s shape). -/
abbrev MOptAcks.Unmarshal.specS : Prop :=
  ∀ (t : Loc) (v : swift.MOptAcks) (br : Loc) (rd : GoInterface) (I : List w8 → IProp netDistGF)
    (R : List w8),
  {{ ctxV ∗ bufio.readerOk rd I ∗ sp.streamLaw br rd I R (sp.nextOk (W8 14)) ∗
      bufio.ownReader br rd I R ∗ t ↦ v }}
    (App (Val (t @!! go.GoType.PointerType swift.MOptAcks.ty @!! go!"Unmarshal"))
      (Val #(interface.mkOk (go.GoType.PointerType bufio.Reader.ty) #br)))
  {{ (err : GoInterface), RET #err; ∃ data : List w8, bufio.ownReader br rd I (R ++ data) ∗
      ((⌜err = interface.nil⌝ ∗ ∃ (r b : w32) (asl : GoSlice) (ps : List (swift.Ack × sp.Ack)),
          ⌜data = (sp.Msg.optAcks r b (ps.map Prod.snd)).body ∧
            (sp.Msg.optAcks r b (ps.map Prod.snd)).wf⌝ ∗
          t ↦ swift.MOptAcks.mk r b asl ∗ asl ↦* ps.map Prod.fst ∗
          [∗list] p ∈ ps, swift.ackRepr p.1 p.2) ∨
        (⌜err ≠ interface.nil⌝ ∗ ∃ v' : swift.MOptAcks, t ↦ v')) }}

end specs

section proofs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF] [SwiftKitDeps]
variable [swift.Assumptions] [io.Assumptions] [errors.Assumptions]
  [bufio.Assumptions]

set_option goose.wp.extras true

omit [swift.Assumptions] [io.Assumptions] [errors.Assumptions]
  [bufio.Assumptions] in
/-- The first 8 bytes of a 10-byte buffer, as the slice `b[:8]`. -/
theorem slice_take8 (p : Loc) (xs : List w8) (hl : xs.length = 10) :
    (slice.mk p (W64 10) (W64 10) ↦* xs : IProp netDistGF) ⊢
      slice.mk p (W64 8) (W64 10) ↦* xs.take 8 := by
  rw [ownSlice_unseal]; unfold ownSliceDef
  iintro (%H | ⟨H, -⟩)
  · exfalso; obtain ⟨h1, -⟩ := H; simp [slice.nil] at h1
  iright
  simp only
  icases (array_split (V := w8) (W64 8) p (DFrac.own 1) _ _ (by word)).1 $$ H
    with ⟨H, -⟩
  isplitl [H]
  · iExactEq H; rfl
  · ipureintro; simp [hl]; decide

omit [swift.Assumptions] [io.Assumptions] [errors.Assumptions]
  [bufio.Assumptions] go_gctx hG sem in
theorem optAcks_body (r b : w32) (al : List sp.Ack) :
    (sp.Msg.optAcks r b al).body = (sp.le32 r ++ sp.le32 b) ++ sp.varintLen al.length ++
      (al.map sp.Ack.enc).flatten := by
  simp [sp.Msg.body, List.append_assoc]

end proofs

end swift.tbl

end Perennial.github_com.imdea_software.swiftpaxos

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

namespace swift.tbl

section entries
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF] [SwiftKitDeps]
variable [swift.Assumptions] [io.Assumptions] [errors.Assumptions]
  [bufio.Assumptions]

set_option goose.wp.extras true

omit [io.Assumptions] [errors.Assumptions] [bufio.Assumptions] in
theorem wp_New_MOptAcks (o : Loc) :
    {{ (True : IProp netDistGF) }}
      (App (Val (o @!! go.GoType.PointerType swift.MOptAcks.ty @!! go!"New")) (Val #()))
    {{ (l : Loc), RET #(interface.mkOk (go.GoType.PointerType swift.MOptAcks.ty) #l);
        l ↦ (zero_val swift.MOptAcks) }} := by
  wp_start
  wp_auto
  wp_alloc_auto
  wp_auto
  iapply HΦ; iframe

end entries

end swift.tbl

end Perennial.github_com.imdea_software.swiftpaxos
