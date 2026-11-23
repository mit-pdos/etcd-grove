/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/TableFixed.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
The swift table's fixed-size entries and the entries no peer sends:

* `MNewLeader.Unmarshal` (8 bytes, over any reader with `readsOk`);
* `unmarshalOk`/`newOk` of `MLightSlowAck` (12, the client's `MLightSlowAck.Unmarshal` proof),
  `MNewLeader` (16), and of `MSlowAck` (11), `MPing` (19), `MPingRep` (20), `MCollect` (21),
  `MAccept` (22) (vacuous: no well-formed message has their type).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.TableBase
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.TableFixedDefs

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

end specs

section proofs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF] [SwiftKitDeps]
variable [swift.Assumptions] [io.Assumptions] [errors.Assumptions]
  [bufio.Assumptions]

set_option goose.wp.extras true

theorem MNewLeader.Unmarshal.wp_proof : MNewLeader.Unmarshal.specI (hG := hG) := by
  intro t v rd I R
  wp_start as ⟨#Hrd, HI, Ht⟩
  try wp_auto
  ihave Hsl := slice_array b_ptr 8 (Perennial.zero_val (GoArray w8 8)) (by decide) $$ b
  rw [show sint.Z (W64 0) = 0 from rfl, go.arrayIndexRef_0, show W64 8 - W64 0 = W64 8 from rfl]
  rw [show (Perennial.zero_val (GoArray w8 8)).arr = List.replicate 8 (W8 0) from rfl]
  wp_apply bufio.wp_ReadAtLeast rd I R _ (List.replicate 8 (W8 0)) (W64 8) ?_ $$
    [$Hpkg $Hrd $HI $Hsl] as %n %err ⟨%data, %Hd, Hsl, HI, #He⟩
  obtain ⟨hn, hdl, herr⟩ := Hd
  rcases err with e | _
  · wp_auto
    iapply HΦ
    iexists data
    iframe HI
    iright
    isplitr
    · ipureintro; intro h; cases h
    iexists v
    iexact Ht
  · have h8 : data.length = 8 := by
      have := herr.1 rfl; simp at hdl; have : sint.Z (W64 8) = 8 := rfl; omega
    obtain ⟨d0, d1, d2, d3, d4, d5, d6, d7, rfl⟩ :
        ∃ d0 d1 d2 d3 d4 d5 d6 d7 : w8, data = [d0, d1, d2, d3, d4, d5, d6, d7] := by
      match data, h8 with
      | [d0, d1, d2, d3, d4, d5, d6, d7], _ => exact ⟨d0, d1, d2, d3, d4, d5, d6, d7, rfl⟩
    isimp only [List.length_cons, List.length_nil, List.drop_replicate, List.append_nil,
      Nat.reduceAdd, Nat.sub_self, List.replicate_zero] at Hsl
    wp_auto
    rd_ld8
    iapply HΦ
    iexists _
    iframe HI
    ileft
    isplitr
    · ipureintro; rfl
    iexists leToU32 [d0, d1, d2, d3], leToU32 [d4, d5, d6, d7]
    isplitr
    · ipureintro
      simp only [sp.le32]
      rw [leToU32_le _ rfl, leToU32_le _ rfl]
      rfl
    iExactEq Ht
    simp only [encoding.binary.leToU32_4]

/-! ## The entries -/

theorem unmarshalOk_lightSlowAck (wp_LSA : swift.rd.MLightSlowAck.Unmarshal.specI (hG := hG))
    (l : Loc) (v : swift.MLightSlowAck) :
    ctxIO ∗ l ↦ v ⊢ sp.unmarshalOk (W8 12) (swift.msgRep (W8 12))
      (interface.mkOk (go.GoType.PointerType swift.MLightSlowAck.ty) #l) := by
  unfold ctxIO
  iintro ⟨⟨#Hio, #Hbuf⟩, Hl⟩
  unfold sp.unmarshalOk
  iexists _
  isplitr
  · ipureintro; rfl
  iintro %br %rd %I %R %Φ #Hrd - Hown HΦ
  ihave #Hrs := bufio.bufioReadsOk br rd I $$ [$Hbuf $Hrd]
  wp_apply wp_LSA l v _ (bufio.ownReader br rd I) R $$
    [$Hio $Hrs $Hown $Hl] as %err ⟨%data, Hown, Hres⟩
  icases Hres with (⟨%He, %s, %Hd, Hl⟩ | ⟨%He, -⟩)
  · iapply HΦ $$ Hown
    ileft
    isplitr
    · ipureintro; exact He
    iexists .lightSlowAck s
    isplitr
    · ipureintro; subst Hd; exact sp.decodes_of_body rfl trivial
    unfold swift.msgRep swift.msgRepM
    iexists l, _
    iframe Hl
    ipureintro
    exact ⟨rfl, rfl, rfl, rfl⟩
  · iapply HΦ $$ Hown
    iright
    ipureintro; exact He

theorem unmarshalOk_newLeader (l : Loc) (v : swift.MNewLeader) :
    ctxIO ∗ l ↦ v ⊢ sp.unmarshalOk (W8 16) (swift.msgRep (W8 16))
      (interface.mkOk (go.GoType.PointerType swift.MNewLeader.ty) #l) := by
  unfold ctxIO
  iintro ⟨⟨#Hio, #Hbuf⟩, Hl⟩
  unfold sp.unmarshalOk
  iexists _
  isplitr
  · ipureintro; rfl
  iintro %br %rd %I %R %Φ #Hrd - Hown HΦ
  ihave #Hrs := bufio.bufioReadsOk br rd I $$ [$Hbuf $Hrd]
  wp_apply MNewLeader.Unmarshal.wp_proof l v _ (bufio.ownReader br rd I) R $$
    [$Hio $Hrs $Hown $Hl] as %err ⟨%data, Hown, Hres⟩
  icases Hres with (⟨%He, %r, %b, %Hd, Hl⟩ | ⟨%He, -⟩)
  · iapply HΦ $$ Hown
    ileft
    isplitr
    · ipureintro; exact He
    iexists .newLeader r b
    isplitr
    · ipureintro; subst Hd; exact sp.decodes_of_body rfl trivial
    unfold swift.msgRep swift.msgRepM
    iexists l
    iframe Hl
    ipureintro; rfl
  · iapply HΦ $$ Hown
    iright
    ipureintro; exact He

theorem newOk_lightSlowAck (wp_LSA : swift.rd.MLightSlowAck.Unmarshal.specI (hG := hG))
    (o : Loc) :
    ctxIO ⊢ sp.newOk (W8 12) (swift.msgRep (W8 12))
      (interface.mkOk (go.GoType.PointerType swift.MLightSlowAck.ty) #o) := by
  apply newOk_of _ _ _ o ctxIO (fun l => iprop(l ↦ (zero_val swift.MLightSlowAck)))
  · iintro %Φ - HΦ
    iapply wp_New_MLightSlowAck o $$ [] HΦ
    itrivial
  · intro l; exact unmarshalOk_lightSlowAck wp_LSA l _

theorem newOk_newLeader (o : Loc) :
    ctxIO ⊢ sp.newOk (W8 16) (swift.msgRep (W8 16))
      (interface.mkOk (go.GoType.PointerType swift.MNewLeader.ty) #o) := by
  apply newOk_of _ _ _ o ctxIO (fun l => iprop(l ↦ (zero_val swift.MNewLeader)))
  · iintro %Φ - HΦ
    iapply wp_New_MNewLeader o $$ [] HΦ
    itrivial
  · intro l; exact unmarshalOk_newLeader l _

end proofs

end swift.tbl

end Perennial.github_com.imdea_software.swiftpaxos
