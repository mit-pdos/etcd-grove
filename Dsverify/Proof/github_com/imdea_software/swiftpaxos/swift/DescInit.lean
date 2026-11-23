/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/DescInit.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
**A raw descriptor becomes an owner state** (round 29, sv-swb; notes/prove-swift.md §35): the
first message of a descriptor (a goroutine's, `handleDesc.specD`, or a sequential one's,
`handleMsg.seqSpecD`) finds it as `newDesc` left it (`swift.descRaw`, NewDesc.lean: phase
`START`, no proposal, empty sets, `afterPropagate` with no stored closure, `waitingAck` nil); with
its channel's half of `msgs`, a quarter of `seq`, an epoch share (`epochRd`, `shOwn`) and the
reply channel's object, it is the owner state `descOwnF … (descRest … ∗ Do)` the handlers take
(`handleMsg.ackSpecI`, `handleMsg.propSpecI`). The row token is absent (`rowTokO`'s second
disjunct: the row is empty, no proposal, phase not `COMMIT`; G7). Round 35 (table rev 7b
§3.12, G-hrec): `newDesc` made the raw descriptor at a record `c0` of the owner record's base.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.HandlePropose
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.NewDesc

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section lemmas
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF]
variable [swift.Assumptions] [hook.Assumptions]

/-- **The raw descriptor's owner state** (see the file header). -/
theorem swift.descRaw_own (c : swift.DC) (RC : Loc → w32 → IProp netDistGF)
    (MP : GoInterface → IProp netDistGF) (x : swift.CommandId) (b : Nat) (sqv fqv : GoInterface)
    (szS szF : Nat) (memS memF : w32 → Prop) (γm : ChanNames) (d m : Loc) (s : Bool) (q : Qp)
    (bw : w32) (stp rcp : Loc) (Do : IProp netDistGF) (hsq : s = c.sq) (c0 : swift.DC)
    (hb : c.base = c0.base) :
    swift.descRaw c0 RC MP x b sqv fqv szS szF memS memF γm d ∗
      swift.slotCap c MP γm d x b iprop(swift.descCore c d x b ∗ (swift.descRest c b x d ∗ Do)) ∗
      typedPointsto (swift.dfld d go!"msgs") m (DFrac.own (1 : Qp).half) ∗ isChanBag γm m MP ∗
      typedPointsto (swift.dfld d go!"seq") s (DFrac.own (1 : Qp).half.half) ∗
      swift.epochRd c.γe c.γxe c.rp c.rr q b bw stp rcp ∗ swift.shOwn c d b q ∗ RC rcp bw ∗ Do ∗
      c.slot none ∗ swift.depSpecR c ∗ □ swift.slotB MP c.γxm b x ⊢
    swift.descOwnF c RC MP γm d x b iprop(swift.descRest c b x d ∗ Do) := by
  iintro ⟨Hraw, #Hcap, Hm, #Hmb, Hs, Hrd, Hsh, HRC, HDo, Hslt, #HdR, #HsB⟩
  iunfold swift.descRaw at Hraw
  -- round 35 (G-hrec): the raw descriptor was made at a record `c0` of the owner's base
  rw [swift.leadAckP_base c c0 hb.symm]
  icases Hraw with ⟨%cf, %sl, %fa, %cond, %df, %hd, %cc, %vs, %sn, #Hmx, Hcmd, #Hvs, %Hop, Hdep,
    Hhs, Hsn, Hph, Hslw, Hdf, -, Hsb, Hp, Hpd, Hwa, Hap, Hocf, #Hcond, Hsl, Hfa, Hsls, Hfas, #HhdB⟩
  iunfold swift.acksHdOkB at HhdB
  ihave #Hhd := HhdB $$ %c %hb HdR
  icases (typedPointsto_half_split _ _ _).1 $$ Hhs with ⟨Hhs1, Hhs2⟩
  icases (typedPointsto_half_split _ _ _).1 $$ Hp with ⟨Hp1, Hp2⟩
  ihave #Hnil := ownSlice_nil (GF := netDistGF) (V := swift.CommandId) DFrac.discard
  ihave #HnilH := ownSlice_nil (GF := netDistGF) (V := swift.SHash) DFrac.discard
  ihave Hbs := ownSlice_nil (GF := netDistGF) (V := w32) (DFrac.own 1)
  ihave Hbc := ownSliceCap_nil (GF := netDistGF) (V := w32)
  iunfold swift.descOwnF
  isplitr [Hap Hocf Hp2 Hsb Hbs Hbc]
  · iunfold swift.descOwn
    iexists sl, fa, sqv, fqv, szS, szF, memS, memF, hd
    iframe Hhd Hcap Hsls
    iunfold swift.setR
    iunfold swift.descSt
    iexists q, bw, stp, rcp,
      (⟨W64 0, cc, vs, slice.nil, [], slice.nil, [], null, s, m⟩ : swift.DescV), swift.rowEmpty
    iframe Hrd Hsh HRC
    isplitl [Hph Hcmd Hdep Hhs1 Hp1 Hs Hm]
    · iunfold swift.descF
      iframe Hph Hcmd Hvs Hdep Hnil Hhs1 HnilH Hp1 Hs Hm Hmb Hmx
      ipureintro; exact Hop
    isplitl [Hslt]
    · iunfold swift.rowTokO
      iright
      iframe Hslt
      isplitr
      · ipureintro; exact ⟨rfl, rfl⟩
      ileft; ipureintro; show (W64 0 : w64) ≠ W64 3; decide
    isplitr
    · ileft; ipureintro; rfl
    isplitr
    · isplitr
      · iunfold swift.rowAcc
        isplitr
        · ileft; ipureintro; rfl
        isplitr
        · ipureintro; intro h; simp [swift.rowEmpty] at h
        ileft; ipureintro; rfl
      iapply swift.repPre_null; rfl
    isplitr
    · ipureintro; intro h; exact absurd h (show ¬ ((W64 0 : w64) = W64 3) by decide)
    isplitr
    · iunfold swift.phaseWhy; ileft; ipureintro; show (W64 0 : w64) ≠ W64 1; decide
    isplitr
    · iunfold swift.depWhy; ileft; ileft; ipureintro; right; left; rfl
    isplitr
    · ipureintro
      refine ⟨⟨fun _ => ⟨Or.inl rfl, rfl⟩, fun h => absurd rfl h⟩, hsq⟩
    iframe HsB
    iframe Hsl Hfa
    simp only [↓reduceIte]
    iframe Hfas
    isplitl [Hwa Hslw]
    · iunfold swift.descCore
      iexists null, false
      iframe Hwa Hslw
      ileft; ipureintro; rfl
    iframe HDo
    iunfold swift.descRest
    iexists slice.nil, slice.nil, sn, df
    iframe Hpd Hsn Hhs2 Hdf
    iunfold swift.pdOk
    ileft; ipureintro; exact ⟨rfl, rfl⟩
  · iunfold swift.descOcf
    iexists cf, cond, [], false
    iframe Hcond
    isplitl [Hap Hocf Hp2 Hsb Hbs Hbc]
    · iunfold swift.ocfRes
      iframe Hap Hocf
      isplitl [Hp2]
      · iunfold swift.proposeHalf
        iexists null
        iframe Hp2
        ipureintro; simp
      iexists slice.nil, []
      iframe Hsb Hbs Hbc
      ipureintro; exact ⟨List.nodup_nil, Nat.le_refl 0⟩
    isplitr
    · iapply swift.ocfV_false
    iapply BigSepL.bigSepL_nil.2; itrivial

end lemmas

end Perennial.github_com.imdea_software.swiftpaxos
