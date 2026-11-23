/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/SeqOpen.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
**The ghost steps around the run loop's inline call** (round Q1, sv-swa; D59 (2), 45-a; table
§3R11 T7s.l/T7s.o/T7s.u, T7e, T7r; notes/prove-swift.md "seq_open (round Q1)"). Used by
`swift.seq_open` (SeqSpecProof.lean).

* `swift.slotCap_ofS`: the inline record's slot capability, read off `slotSpecS` at its frame
  (45-a; plan R8.2 (4)).
* `swift.elem_eighths`: a quarter of a registry element in two eighths (R's `cntFrozen` ½ =
  ¼ (`loanRec`) + ⅛ (`slot none`) + ⅛ (kept)).
* `swift.seq_lend` (T7s.l): the inline loan out of the sub-pool, opened into `epochRd q` and
  `shOwnR cI d b q` (the run loop's reader becomes the owner's).
* `swift.seq_return` (T7e/T7r): the loan back (`descInv_returnLoanO`), the reader back.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.HandleDescProofDefs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section lemmas
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF] [SwiftKitDeps]
variable [swift.Assumptions] [replica.Assumptions] [replica.defs.Assumptions] [rpc.Assumptions]
variable [sync.Assumptions] [hook.Assumptions]

/-- **The inline record's slot capability** (45-a, D59 (2); plan R8.2 (4)): `slotCap`'s right
disjunct at `cI = x.dcK … g (.seq γi)` and the owner frame `descCore ∗ (descRest ∗ cI.kf)` is
`slotSpecS` read at that frame (its pre is `slotCap`'s with the record's context). -/
theorem swift.slotCap_ofS (γ0 : sp.Names) (γc γm : GName) (x : swift.RunX)
    (wp_slotS : swift.Replica.handleMsg.slotSpecS γ0 γc γm x) (rp : Loc) (g : swift.DescG)
    (γi γsg : GName) (γd : ChanNames) (d : Loc) (y : swift.CommandId) :
    isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.swift ∗
      (x.dcK γ0 γc γm rp g (.seq γi)).ctx ⊢
    swift.slotCap (x.dcK γ0 γc γm rp g (.seq γi)) (swift.MPi g y γi γsg) γd d y g.ev.b
      iprop(swift.descCore (x.dcK γ0 γc γm rp g (.seq γi)) d y g.ev.b ∗
        (swift.descRest (x.dcK γ0 γc γm rp g (.seq γi)) g.ev.b y d ∗
          (x.dcK γ0 γc γm rp g (.seq γi)).kf d y)) := by
  iintro ⟨#Hpkg, #Hc⟩
  iunfold swift.slotCap
  iright
  imodintro
  iintro %s %dv %rv %q %sl %fa %cf %cond %fs %v
  imodintro
  iintro %Φ ⟨HmS, Hd, %Hdv, #Hex, Hsh, Htok, HsF, HfF, Hms,
    Hmf, Hocf, ⟨Hcore, Hrest, Hkf⟩, Henv⟩ HΦ
  rw [show (x.dcK γ0 γc γm rp g (.seq γi)).rp = rp from rfl]
  ihave Hsh : ghostMapElem x.γsh d (DFrac.own (1 : Qp).half) q $$ [Hsh]
  · iExactEq Hsh; rfl
  iapply (wp_slotS rp g γi γsg γd d y dv rv s q sl fa cf cond fs v)
    $$ [HmS Hd Htok Hsh HsF HfF Hms Hmf Hocf Hcore Hrest Hkf Henv]
  · iframe Hpkg Hc HmS Hd Htok Hsh HsF HfF Hms Hmf Hocf Hcore Hrest Hkf Henv
    isplitr
    · iExactEq Hex; rfl
    ipureintro; exact Hdv.1
  inext
  iintro H
  iapply HΦ; iexact H

/-- A quarter of a registry element in two eighths. -/
theorem swift.elem_eighths (γ : GName) (k : Nat) (v : Bool) :
    ghostMapElem (GF := netDistGF) γ k (DFrac.own (1 : Qp).half.half) v ⊣⊢
      ghostMapElem γ k (DFrac.own (1 : Qp).half.half.half) v ∗
        ghostMapElem γ k (DFrac.own (1 : Qp).half.half.half) v := by
  conv => lhs; rw [← Qp.half_add_half (1 : Qp).half.half]
  exact (ghostMapElem_fractional k γ v).fractional _ _

/-- **T7s.l: the inline loan** (table §3R11 T7s.l; `descInv_loanOut` with R's `γst` half as the
not-stopped witness, key `0` at ¼ of R's `cntFrozen`): opened at the inline record `cI` as
`epochRd q` and `shOwnR cI d b q` (the loan's pin, `status`, `FQ`, the reader R lends,
`cI.env d q`: the loan's token and receipt, `descX q`, the epoch's invariants). -/
theorem swift.seq_lend (γ0 : sp.Names) (γc γm : GName) (x : swift.RunX) (rp : Loc) (g : swift.DescG)
    (γi : GName) (d : Loc) :
    inv swift.descN (swift.descInv γ0 x.γd x.γn x.γout g (x.epN rp) (x.DR γ0 g.ev.b)
        (swift.descGo x.γn g x.str) x.str) ∗
      inv swift.seqN (swift.seqInbox g) ∗ swift.ownCtx γ0 γc γm x rp g ∗ £ 1 ∗
      ghostVar g.γst (1 : Qp).half false ∗
      ghostMapElem x.γn 0 (DFrac.own (1 : Qp).half.half) false ∗ swift.runReader rp x.γdl ⊢
    |={⊤}=> ghostVar g.γst (1 : Qp).half false ∗ ∃ q : Qp,
      swift.epochRd (x.dcK γ0 γc γm rp g (.seq γi)).γe (x.dcK γ0 γc γm rp g (.seq γi)).γxe
        (x.dcK γ0 γc γm rp g (.seq γi)).rp (x.dcK γ0 γc γm rp g (.seq γi)).rr q g.ev.b g.ev.bw
        g.ev.stp g.ev.rcp ∗
      swift.shOwnR (x.dcK γ0 γc γm rp g (.seq γi)) d g.ev.b q := by
  iintro ⟨#HI, #HSI, #HoC, Hlc, Hst, Hn, Hrdr⟩
  imod swift.descInv_loanOut γ0 x.γd x.γn x.γout g (x.epN rp) (x.DR γ0 g.ev.b) (swift.descGo x.γn g x.str)
      x.str 0 (1 : Qp).half.half (ghostVar g.γst (1 : Qp).half false) (swift.liveOk_run g)
    $$ [Hlc Hst Hn] with ⟨Hst, %iL, %q, Hsh, HX, Hloan, Hr⟩
  · iframe HI Hlc Hst Hn
  iunfold swift.epochShare at Hsh
  icases Hsh with ⟨Hrd, Hpin, Hstat, Hfq⟩
  iunfold swift.fqShare at Hfq
  icases Hfq with ⟨Hfq, #Hqi, %Hfqf⟩
  iunfold swift.runReader at Hrdr
  icases Hrdr with ⟨%dm, #Hdm, Hrdr⟩
  imodintro
  iframe Hst
  iexists q
  isplitl [Hrd]
  · iExactEq Hrd; rfl
  iunfold swift.shOwnR
  isplitl [Hstat]
  · iexists g.ev.st; iExactEq Hstat; rfl
  isplitl [Hfq]
  · iexists g.ev.fq, g.ev.szF, g.ev.memF
    isplitl [Hfq]
    · iExactEq Hfq; rfl
    iframe Hqi
    ipureintro; exact Hfqf
  isplitl [Hrdr]
  · ihave Hrdr := swift.ownRdr_of rp x.γdl dm $$ [Hrdr]
    · iframe Hdm Hrdr
    iExactEq Hrdr; rfl
  isplitl [Hloan Hr HX]
  · ihave Henv : swift.envK γ0 γc γm x rp g (.seq γi) d q $$ [Hloan Hr HX]
    · simp only [swift.envK]
      isplitl [Hloan Hr]
      · iexists iL; iframe Hloan Hr
      isplitl [HX]
      · icases HX with ⟨%dm, HX⟩
        iexists dm; iExactEq HX; rfl
      iunfold swift.epInvs
      iframe HI HSI HoC
    iExactEq Henv; rfl
  iExactEq Hpin; rfl

/-- **T7e/T7r: the inline loan back** (table §3R11 T7e/T7r; `descInv_returnLoanO`): from the
owner's `epochRd q ∗ shOwnR cI d b q` (as `descOwnF`'s park or `descGone` leave them), R's ¼ of
`cntFrozen` and its reader. -/
theorem swift.seq_return (γ0 : sp.Names) (γc γm : GName) (x : swift.RunX) (rp : Loc) (g : swift.DescG)
    (γi : GName) (d : Loc) (q : Qp) (bw : w32) (stp rcp : Loc) :
    £ 1 ∗ £ 1 ∗
      swift.epochRd (x.dcK γ0 γc γm rp g (.seq γi)).γe (x.dcK γ0 γc γm rp g (.seq γi)).γxe
        (x.dcK γ0 γc γm rp g (.seq γi)).rp (x.dcK γ0 γc γm rp g (.seq γi)).rr q g.ev.b bw stp rcp ∗
      swift.shOwnR (x.dcK γ0 γc γm rp g (.seq γi)) d g.ev.b q ⊢
    |={⊤}=> ghostMapElem x.γn 0 (DFrac.own (1 : Qp).half.half) false ∗ swift.runReader rp x.γdl := by
  iintro ⟨Hlc1, Hlc2, Hrd, HshR⟩
  iunfold swift.shOwnR at HshR
  icases HshR with ⟨⟨%st, Hstat⟩, ⟨%fq, %szF, %memF, Hfq, -, -⟩, Hrdr, Henv, Hpin⟩
  ihave Henv : swift.envK γ0 γc γm x rp g (.seq γi) d q $$ [Henv]
  · iExactEq Henv; rfl
  simp only [swift.envK]
  icases Henv with ⟨⟨%iL, Hloan, Hr⟩, ⟨%dm, HX⟩, #HE⟩
  iunfold swift.epInvs at HE
  icases HE with ⟨#HI, -, -⟩
  imod swift.descInv_returnLoanO γ0 x.γd x.γn x.γout g (x.epN rp) (x.DR γ0 g.ev.b)
      (swift.descGo x.γn g x.str) x.str iL q 0 (1 : Qp).half.half dm g.ev.b bw stp rcp st fq
    $$ [Hlc1 Hlc2 Hrd Hpin Hstat Hfq HX Hloan Hr] with Hn
  · iframe HI Hlc1 Hlc2 Hloan Hr
    isplitl [Hrd]
    · iExactEq Hrd; rfl
    isplitl [Hpin]
    · iExactEq Hpin; rfl
    isplitl [Hstat]
    · iExactEq Hstat; rfl
    isplitl [Hfq]
    · iExactEq Hfq; rfl
    iExactEq HX; rfl
  imodintro
  iframe Hn
  iunfold swift.ownRdr at Hrdr
  icases Hrdr with ⟨%dm', #Hdm, Hrdr⟩
  iunfold swift.runReader
  iexists dm'
  isplitr
  · iExactEq Hdm; rfl
  iExactEq Hrdr; rfl

/-- `cntFrozen`'s half as R's three parts (¼ the loan record, ⅛ `cI.slot none`, ⅛ kept). -/
theorem swift.frozen_parts (γ : GName) (k : Nat) (v : Bool) :
    ghostMapElem (GF := netDistGF) γ k (DFrac.own (1 : Qp).half) v ⊣⊢
      ghostMapElem γ k (DFrac.own (1 : Qp).half.half) v ∗
        ghostMapElem γ k (DFrac.own (1 : Qp).half.half.half) v ∗
          ghostMapElem γ k (DFrac.own (1 : Qp).half.half.half) v := by
  refine (swift.elem_quarters γ k v).trans ?_
  exact sep_congr .rfl (swift.elem_eighths γ k v)

/-- **`descDSB`'s parts the inline call uses** (T7s.l/T7e): the descriptors' and the inbox's
invariants, R's `γst` half and `cntFrozen` half, the epoch's construction, and the rest back. -/
theorem swift.descDSB_take (γ0 : sp.Names) (γc γm : GName) (x : swift.RunX) (rp : Loc)
    (g : swift.DescG) (ev : swift.EpV) (γp : GName) (i : Nat) :
    swift.descDSB γ0 γc γm x rp g ev γp i ⊢
      inv swift.descN (swift.descInv γ0 x.γd x.γn x.γout g (x.epN rp) (x.DR γ0 g.ev.b)
        (swift.descGo x.γn g x.str) x.str) ∗ inv swift.seqN (swift.seqInbox g) ∗
      ghostVar g.γst (1 : Qp).half false ∗ ghostMapElem x.γn 0 (DFrac.own (1 : Qp).half) false ∗
      ⌜∃ g00 : swift.DescG, g = swift.gO γ0 γc γm x rp g00⌝ ∗
      (ghostVar g.γst (1 : Qp).half false -∗ ghostMapElem x.γn 0 (DFrac.own (1 : Qp).half) false -∗
        swift.descDSB γ0 γc γm x rp g ev γp i) := by
  iintro H
  iunfold swift.descDSB at H
  icases H with ⟨Hr, Hs, Hl, %Hg, #Hc, %Hsq, %Hmp, %Hso, %Hgo, #Hcg⟩
  iunfold swift.descStateB at Hs
  icases Hs with ⟨%dm1, Hcd, HcV, HrV, #HI, Hst, Hfz, HγS, Hγb, #HSI⟩
  iunfold swift.cntFrozen at Hfz
  isplitr
  · iexact HI
  isplitr
  · iexact HSI
  iframe Hst Hfz
  isplitr
  · ipureintro; exact Hgo
  iintro Hst Hfz
  iunfold swift.descDSB
  iframe Hr Hl Hc
  isplitl [Hcd HcV HrV Hst Hfz HγS Hγb]
  · iunfold swift.descStateB
    iexists dm1
    iframe Hcd HcV HrV HI Hst HγS Hγb HSI
    iunfold swift.cntFrozen
    iexact Hfz
  isplitr
  · ipureintro; exact Hg
  isplitr
  · ipureintro; exact Hsq
  isplitr
  · ipureintro; exact Hmp
  isplitr
  · ipureintro; exact Hso
  isplitr
  · ipureintro; exact Hgo
  iexact Hcg

/-- **The parked state's `γsh` half and its frame** (T7s.u: the frame's `kfK` holds the other
`γsh` half; both are updated to the loan's share), and both back at any value. -/
theorem swift.descOwnFP_shDo (c : swift.DC) (RC : Loc → w32 → IProp netDistGF)
    (MP : GoInterface → IProp netDistGF) (γd : ChanNames) (d : Loc) (x : swift.CommandId) (b : Nat)
    (Do : IProp netDistGF) (q : Qp) :
    swift.descOwnFP c RC MP γd d x b q Do ⊢
      ghostMapElem c.γsh d (DFrac.own (1 : Qp).half) q ∗ Do ∗
      (∀ q' : Qp, ghostMapElem c.γsh d (DFrac.own (1 : Qp).half) q' -∗ Do -∗
        swift.descOwnFP c RC MP γd d x b q' Do) := by
  iintro Hp
  iunfold swift.descOwnFP at Hp
  icases Hp with ⟨Ho, Hocf⟩
  iunfold swift.descOwnP at Ho
  icases Ho with ⟨%s, %f, %qS, %qF, %szS, %szF, %memS, %memF, %hd, #Hhd, #Hcap, HoS, HsR⟩
  iunfold swift.setRP at HsR
  iunfold swift.descStP at HsR
  icases HsR with ⟨%dv, %rv, Hγ, Hd, Htok, Hcom, #Hra, Hph, #Hpw, #Hdw, Hrp, #HsB,
    ⟨Hsl, Hfa, HoF, Hcore, HDo⟩⟩
  iframe Hγ HDo
  iintro %q' Hγ' HDo
  iunfold swift.descOwnFP
  iframe Hocf
  iunfold swift.descOwnP
  iexists s, f, qS, qF, szS, szF, memS, memF, hd
  iframe Hhd Hcap HoS
  iunfold swift.setRP
  iunfold swift.descStP
  iexists dv, rv
  iframe Hγ' Hd Htok Hcom Hra Hph Hpw Hdw Hrp HsB Hsl Hfa HoF Hcore HDo

/-- The inline record's frame `kfK` (its sequential branch). -/
theorem swift.kf_seq (γ0 : sp.Names) (γc γm : GName) (x : swift.RunX) (rp : Loc) (g : swift.DescG)
    (γi : GName) (d : Loc) (y : swift.CommandId) :
    (x.dcK γ0 γc γm rp g (.seq γi)).kf d y =
      iprop(typedPointsto (swift.dfld d go!"active") true (DFrac.own (1 : Qp).half) ∗
        (∃ q : Qp, ghostMapElem x.γsh d (DFrac.own (1 : Qp).half) q) ∗
        (ghostVar γi (1 : Qp).half (x.str y, d) ∗ ∃ sc : Loc, swift.dfld d go!"stopChan" ↦ sc)) := rfl

/-- The inline record's loan environment (its sequential branch). -/
theorem swift.env_seq (γ0 : sp.Names) (γc γm : GName) (x : swift.RunX) (rp : Loc) (g : swift.DescG)
    (γi : GName) (d : Loc) (q : Qp) :
    (x.dcK γ0 γc γm rp g (.seq γi)).env d q =
      iprop((∃ iL : Nat, swift.epochLoan g.γq iL q ∗
        ghostMapElem g.γlj iL (DFrac.own (1 : Qp).half) ((0 : Nat), (1 : Qp).half.half)) ∗
        (∃ dm : GoSlice, swift.descX rp x.γd g dm q) ∗ swift.epInvs γ0 γc γm x rp g) := rfl

/-- The inline record's free ledger slot: ⅛ of R's key `0`. -/
theorem swift.slot_seq (γ0 : sp.Names) (γc γm : GName) (x : swift.RunX) (rp : Loc) (g : swift.DescG)
    (γi : GName) :
    (x.dcK γ0 γc γm rp g (.seq γi)).slot none =
      ghostMapElem x.γn 0 (DFrac.own (1 : Qp).half.half.half) false := rfl

/-- The inline record's retirement residue: the store's element and the free slot. -/
theorem swift.ret_seq (γ0 : sp.Names) (γc γm : GName) (x : swift.RunX) (rp : Loc) (g : swift.DescG)
    (γi : GName) (d : Loc) (y : swift.CommandId) :
    (x.dcK γ0 γc γm rp g (.seq γi)).ret d y =
      iprop(ghostMapElem g.γS d (DFrac.own 1) y ∗
        ghostMapElem x.γn 0 (DFrac.own (1 : Qp).half.half.half) false) := rfl

/-- **The records at `gO`'s two stages agree** (G-circ): `x.dcK` reads neither `sr` nor `so`'s
second stage. -/
theorem swift.dcK_gO (γ0 : sp.Names) (γc γm : GName) (x : swift.RunX) (rp : Loc) (g00 : swift.DescG)
    (k : swift.OwnK) :
    x.dcK γ0 γc γm rp (swift.gO γ0 γc γm x rp g00) k =
      x.dcK γ0 γc γm rp { g00 with sr := swift.soRaw γ0 γc γm x rp (swift.RCh γ0 γc γm rp) g00 } k :=
  rfl

/-- **T7s.u, free**: the tokenless parked state unparked at the loan's share `q` (both `γsh` halves,
the parked state's and its frame's `kfK`, agreed and updated to `q`; `descOwnF_unpark`). -/
theorem swift.seq_unparkF (γ0 : sp.Names) (γc γm : GName) (x : swift.RunX) (rp : Loc)
    (g : swift.DescG) (γi : GName) (RC : Loc → w32 → IProp netDistGF)
    (MP : GoInterface → IProp netDistGF) (γmc : ChanNames) (d : Loc) (y : swift.CommandId)
    (q0 q : Qp) (bw : w32) (stp rcp : Loc) :
    inv swift.shN (swift.shInv x.γsh) ∗
      swift.epochRd (x.dcK γ0 γc γm rp g (.seq γi)).γe (x.dcK γ0 γc γm rp g (.seq γi)).γxe
        (x.dcK γ0 γc γm rp g (.seq γi)).rp (x.dcK γ0 γc γm rp g (.seq γi)).rr q g.ev.b bw stp rcp ∗
      swift.shOwnR (x.dcK γ0 γc γm rp g (.seq γi)) d g.ev.b q ∗ RC rcp bw ∗
      swift.descOwnFP (x.dcK γ0 γc γm rp g (.seq γi)) RC MP γmc d y g.ev.b q0
        iprop(swift.descRest (x.dcK γ0 γc γm rp g (.seq γi)) g.ev.b y d ∗
          (x.dcK γ0 γc γm rp g (.seq γi)).kf d y) ∗
      (x.dcK γ0 γc γm rp g (.seq γi)).slot none ⊢
    |={⊤}=> swift.descOwnF (x.dcK γ0 γc γm rp g (.seq γi)) RC MP γmc d y g.ev.b
        iprop(swift.descRest (x.dcK γ0 γc γm rp g (.seq γi)) g.ev.b y d ∗
          (x.dcK γ0 γc γm rp g (.seq γi)).kf d y) := by
  iintro ⟨#HshI, Hrd, HshR, HRC, Hp, Hslt⟩
  ihave ⟨Hγ, ⟨Hrest, Hkf⟩, Hback⟩ := swift.descOwnFP_shDo _ _ _ _ _ _ _ _ _ $$ Hp
  ihave Hkf : iprop(typedPointsto (swift.dfld d go!"active") true (DFrac.own (1 : Qp).half) ∗
      (∃ q : Qp, ghostMapElem x.γsh d (DFrac.own (1 : Qp).half) q) ∗
      (ghostVar γi (1 : Qp).half (x.str y, d) ∗ ∃ sc : Loc, swift.dfld d go!"stopChan" ↦ sc)) $$ [Hkf]
  · iExactEq Hkf; rfl
  icases Hkf with ⟨Ha, ⟨%q1, Hk⟩, Hγi, Hsc⟩
  ihave ⟨%Hq, Hel⟩ := swift.sh_agree x.γsh d q0 q1 $$ [Hγ Hk]
  · isplitl [Hγ]
    · iExactEq Hγ; rfl
    iexact Hk
  imod swift.shInv_update x.γsh ⊤ (by simp) d q0 q $$ [Hel] with Hel
  · iframe HshI Hel
  icases (ghostMapElem_halves x.γsh d q).1 $$ Hel with ⟨Hsh1, Hsh2⟩
  ihave Hp := Hback $$ %q [Hsh1] [Hrest Ha Hsh2 Hγi Hsc]
  · iExactEq Hsh1; rfl
  · rw [swift.kf_seq]
    iframe Hrest Ha Hγi Hsc
    iexists q; iexact Hsh2
  imodintro
  iapply swift.descOwnF_unpark
  iframe Hrd HshR HRC Hp Hslt

/-- `MPi` depends on the epoch's names only through `mp` and `γk`. -/
theorem swift.MPi_congr (g g' : swift.DescG) (hmp : g.mp = g'.mp) (hk : g.γk = g'.γk)
    (y : swift.CommandId) (γi γsg : GName) :
    swift.MPi g y γi γsg = swift.MPi g' y γi γsg := by
  unfold swift.MPi swift.incW
  rw [hmp, hk]

/-- `incW` depends on the epoch's names only through `γk`. -/
theorem swift.incW_congr (g g' : swift.DescG) (hk : g.γk = g'.γk) (γi γsg : GName) :
    swift.incW g γi γsg = swift.incW g' γi γsg := by
  unfold swift.incW
  rw [hk]

/-- **T7s.o/T7s.u, raw**: the first inline call makes the raw form the owner form at the loan's
share `q` (as `hd_toOwn`: `descRaw_own` with `slotCap_ofS`, `depSpecR` from `depAll`, `slotB`
from `mpOk` and the commit witness, the reply channel's object from `ownCtx`; the `γsh` element
updated to `q`, half to `shOwn`, half to `kfK`), after T7s.l's loan at the raw form's incarnation.
The raw form is at `g00` (`gO`'s base), which agrees with `g` on
`ev`, `mp`, `γk` (stated so, not by unfolding `gO`, to keep the kernel off comparing the two). -/
theorem swift.seq_raw (γ0 : sp.Names) (γc γm : GName) (x : swift.RunX)
    (wp_slotS : swift.Replica.handleMsg.slotSpecS γ0 γc γm x) (rp : Loc) (g g00 : swift.DescG)
    (hev : g.ev = g00.ev) (hmp : g.mp = g00.mp) (hk : g.γk = g00.γk) (d : Loc)
    (y : swift.CommandId) :
    isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.swift ∗
      swift.ownCtx γ0 γc γm x rp g ∗ (x.dc γ0 γc γm rp).ctx ∗ swift.depAll γ0 γc γm x ∗
      inv swift.descN (swift.descInv γ0 x.γd x.γn x.γout g (x.epN rp) (x.DR γ0 g.ev.b)
        (swift.descGo x.γn g x.str) x.str) ∗ inv swift.seqN (swift.seqInbox g) ∗ £ 1 ∗
      ghostVar g.γst (1 : Qp).half false ∗
      ghostMapElem x.γn 0 (DFrac.own (1 : Qp).half.half) false ∗ swift.runReader rp x.γdl ∗
      ghostMapElem x.γn 0 (DFrac.own (1 : Qp).half.half.half) false ∗
      swift.soRaw γ0 γc γm x rp (swift.RCh γ0 γc γm rp) g00 d y ⊢
    |={⊤}=> ghostVar g.γst (1 : Qp).half false ∗ ∃ (γi γsg : GName) (γmc : ChanNames),
      □ swift.incW g γi γsg ∗
      swift.descOwnF (x.dcK γ0 γc γm rp g (.seq γi)) (swift.RCh γ0 γc γm rp) (swift.MPi g y γi γsg) γmc d y
        g.ev.b iprop(swift.descRest (x.dcK γ0 γc γm rp g (.seq γi)) g.ev.b y d ∗
          (x.dcK γ0 γc γm rp g (.seq γi)).kf d y) := by
  iintro ⟨#Hpkg, #HoC, #Hctx, #Hdep, #HI, #HSI, Hlc, Hst, Hn1, Hrdr, Hslt, Hraw⟩
  iunfold swift.soRaw at Hraw
  icases Hraw with ⟨%γi, %γsg, %γmc, %m, %sc, %q0, %sqv, %fqv, %szS, %szF, %memS, %memF, #Hw, Hγi,
    Hm, #Hmb, Ha, Hs, Hsc, Hsh, Hraw⟩
  imod swift.seq_lend γ0 γc γm x rp g γi d $$ [Hlc Hst Hn1 Hrdr] with ⟨Hst, %q, Hrd, HshR⟩
  · iframe HI HSI HoC Hlc Hst Hn1 Hrdr
  have hW := swift.incW_congr g g00 hk γi γsg
  have hM := swift.MPi_congr g g00 hmp hk y γi γsg
  ihave #HoC2 := HoC
  iunfold swift.ownCtx at HoC2
  icases HoC2 with ⟨#Hdsc, #HpB, -, #HRC, %Hpure, -⟩
  have Hmp := Hpure.1
  ihave #Hdsc2 := Hdsc
  iunfold swift.descDSCtx at Hdsc2
  icases Hdsc2 with ⟨-, -, #HshI, -, -, -⟩
  imod swift.shInv_update x.γsh ⊤ (by simp) d q0 q $$ [Hsh] with Hsh
  · iframe HshI Hsh
  icases (ghostMapElem_halves x.γsh d q).1 $$ Hsh with ⟨Hsh1, Hsh2⟩
  ihave #Hcap := swift.slotCap_ofS γ0 γc γm x wp_slotS rp g γi γsg γmc d y $$ [Hpkg Hctx]
  · iframe Hpkg
    iExactEq Hctx; rfl
  imodintro
  iframe Hst
  iexists γi, γsg, γmc
  isplitr
  · imodintro; rw [hW]; iexact Hw
  iapply swift.descRaw_own (x.dcK γ0 γc γm rp g (.seq γi)) (swift.RCh γ0 γc γm rp)
    (swift.MPi g y γi γsg) y g.ev.b sqv fqv szS szF memS memF γmc d m true q g.ev.bw g.ev.stp
    g.ev.rcp ((x.dcK γ0 γc γm rp g (.seq γi)).kf d y) rfl (x.dc γ0 γc γm rp) rfl
  isplitl [Hraw]
  · rw [hM, hev]; iexact Hraw
  isplitr
  · iexact Hcap
  isplitl [Hm]
  · iexact Hm
  isplitr
  · rw [hM]; iexact Hmb
  isplitl [Hs]
  · iexact Hs
  isplitl [Hrd]
  · iexact Hrd
  isplitl [Hsh1 HshR]
  · iunfold swift.shOwn
    isplitl [Hsh1]
    · iExactEq Hsh1; rfl
    iexact HshR
  isplitr
  · iexact HRC
  isplitl [Ha Hsh2 Hγi Hsc]
  · rw [swift.kf_seq]
    iframe Ha
    isplitl [Hsh2]
    · iexists q; iexact Hsh2
    isplitl [Hγi]
    · iexact Hγi
    iexists sc; iexact Hsc
  isplitl [Hslt]
  · iExactEq Hslt; rfl
  isplitr
  · iunfold swift.depAll at Hdep
    iapply Hdep
  imodintro
  iunfold swift.slotB
  iintro %s %Hs #Hex
  isplitr
  · iapply swift.mp_of_slot x γ0 γc γm rp g y _ Hmp
    iunfold swift.slotMP
    iexists s
    isplitr
    · ipureintro; exact ⟨rfl, Hs⟩
    iExactEq Hex; rfl
  imodintro; rw [hW]; iexact Hw

/-- **T7s.o/T7s.u, token out**: the parked state with its token in the store taken back at the
loan's share `q` (`takeLaw` with the claim `rest d γi` and the free slot: the token, its record and
`slotT`; the record's `x'` is `y`; its halves of `phase`/`dep` and quarter of `propose` joined with
`descFT`'s; `rowAcc` and the commit facts from `rowFacts`; `rowPhaseOk` from the record's, with
`descStT`'s `propose = null → D = []` (Q1-b) and, with a proposal, `dep`'s contents agreed with
`stopFacts`'; the record's `γi` half into `kfK`; both `γsh` halves updated to `q`). -/
theorem swift.seq_unparkT (γ0 : sp.Names) (γc γm : GName) (x : swift.RunX) (rp : Loc)
    (g : swift.DescG) (γi : GName) (RC : Loc → w32 → IProp netDistGF)
    (MP : GoInterface → IProp netDistGF) (γmc : ChanNames) (d : Loc) (y : swift.CommandId)
    (q0 q : Qp) (bw : w32) (stp rcp : Loc) :
    (x.dc γ0 γc γm rp).ctx ∗ inv swift.shN (swift.shInv x.γsh) ∗
      swift.epochRd (x.dcK γ0 γc γm rp g (.seq γi)).γe (x.dcK γ0 γc γm rp g (.seq γi)).γxe
        (x.dcK γ0 γc γm rp g (.seq γi)).rp (x.dcK γ0 γc γm rp g (.seq γi)).rr q g.ev.b bw stp rcp ∗
      swift.shOwnR (x.dcK γ0 γc γm rp g (.seq γi)) d g.ev.b q ∗ RC rcp bw ∗
      swift.claimTok x.γcl (g.ev.b, toCmdId y) (.rest d γi) ∗
      swift.descOwnFT (x.dcK γ0 γc γm rp g (.seq γi)) RC MP γmc d y g.ev.b q0
        iprop(swift.descRest (x.dcK γ0 γc γm rp g (.seq γi)) g.ev.b y d ∗
          (x.dcK γ0 γc γm rp g (.seq γi)).kf d y)
        iprop(swift.descRest (x.dcK γ0 γc γm rp g (.seq γi)) g.ev.b y d ∗ swift.kfK0 x d) ∗
      (x.dcK γ0 γc γm rp g (.seq γi)).slot none ⊢
    |={⊤}=> swift.descOwnF (x.dcK γ0 γc γm rp g (.seq γi)) RC MP γmc d y g.ev.b
        iprop(swift.descRest (x.dcK γ0 γc γm rp g (.seq γi)) g.ev.b y d ∗
          (x.dcK γ0 γc γm rp g (.seq γi)).kf d y) := by
  iintro ⟨#Hctx, #HshI, Hrd, HshR, HRC, Hcl, HT, Hslt⟩
  ihave #Htl := swift.takeLaw_dcK x γ0 γc γm rp g (.seq γi) $$ [Hctx]
  · iExactEq Hctx; rfl
  iunfold swift.shOwnR at HshR
  icases HshR with ⟨Hstat, Hfq, Hrdr, Henv, Hpin⟩
  iunfold swift.takeLaw at Htl
  imod Htl $$ %d %q %(g.ev.b, toCmdId y) %(swift.ClK.rest d γi) Henv Hslt [Hcl] with
    ⟨%rv, Htok, Hw, Henv, HsT⟩
  · iExactEq Hcl; rfl
  isimp only [swift.recOf, swift.retWhy] at Hw
  icases Hw with ⟨%x', %dv', %Hx, Hγi, Hph', Hdep', Hpr', #Hsf, #Hrf⟩
  obtain ⟨Hx', Hrpo'⟩ := Hx
  have hx : x' = y := by
    have := congrArg ofCmdId Hx'
    simpa using this
  subst hx
  iunfold swift.descOwnFT at HT
  icases HT with ⟨⟨%s, %f, %qS, %qF, %szS, %szF, %memS, %memF, %hd, #Hhd, #Hcap, HoS, HstT⟩, Hocf⟩
  iunfold swift.descStT at HstT
  icases HstT with ⟨%dv, Hγ, HdF, #Hpw, #Hdw, #Hrep, %Hsq, #HsB, ⟨Hsl, Hfa, HoF, Hcore, Hrest, Hk0⟩⟩
  iunfold swift.descFT at HdF
  icases HdF with ⟨Hph, Hcmd, #Hvs, Hdep, #HD, Hhs, #HHs, Hpr, Hseq, Hmsg, #Hbag, #Hmx, %Hop⟩
  iunfold swift.kfK0 at Hk0
  icases Hk0 with ⟨Ha, ⟨%q1, Hk⟩, Hsc⟩
  ihave ⟨%Hq, Hel⟩ := swift.sh_agree x.γsh d q0 q1 $$ [Hγ Hk]
  · isplitl [Hγ]
    · iExactEq Hγ; rfl
    iexact Hk
  imod swift.shInv_update x.γsh ⊤ (by simp) d q0 q $$ [Hel] with Hel
  · iframe HshI Hel
  icases (ghostMapElem_halves x.γsh d q).1 $$ Hel with ⟨Hsh1, Hsh2⟩
  ihave ⟨%Heph, Hph⟩ := typedPointsto_half_combine _ dv'.phase dv.phase (1 : Qp) $$ [Hph' Hph]
  · iframe
  ihave ⟨%Hedep, Hdep⟩ := typedPointsto_half_combine _ dv'.dep dv.dep (1 : Qp) $$ [Hdep' Hdep]
  · iframe
  ihave ⟨%Hepr, Hpr⟩ := typedPointsto_half_combine _ dv'.propose dv.propose (1 : Qp).half $$ [Hpr' Hpr]
  · iframe
  ihave %Hrpo : ⌜swift.rowPhaseOk x.N x.r g.ev.b dv rv⌝ $$ []
  · by_cases hn : dv.propose = null
    · ipureintro
      have h1 := Hrpo'.1 (by rw [Hepr]; exact hn)
      refine ⟨fun _ => ⟨?_, Hsq.2 hn⟩, fun h => absurd hn h⟩
      rw [← Heph]; exact h1.1
    · iunfold swift.stopFacts at Hsf
      icases Hsf with (%hn' | ⟨-, #HD2, -, -, -⟩)
      · exfalso; exact hn (by rw [← Hepr]; exact hn')
      ihave %hD := ownSlice_agree dv.dep DFrac.discard DFrac.discard dv.D dv'.D $$ HD [HD2]
      · rw [← Hedep]; iexact HD2
      ipureintro
      unfold swift.rowPhaseOk at Hrpo' ⊢
      rw [← Heph, ← Hepr, hD]
      exact Hrpo'
  icases Hrf with ⟨Hrf, -⟩
  iunfold swift.rowFacts at Hrf
  icases Hrf with ⟨#Hcm, #Hac, %Hiss, #Hpro, %Hph3⟩
  imodintro
  iunfold swift.descOwnF
  iframe Hocf
  iunfold swift.descOwn
  iexists s, f, qS, qF, szS, szF, memS, memF, hd
  iframe Hhd Hcap HoS
  iunfold swift.setR
  iunfold swift.descSt
  iexists q, bw, stp, rcp, dv, rv
  isplitl [Hrd]
  · iexact Hrd
  isplitl [Hsh1 Hstat Hfq Hrdr Henv Hpin]
  · iunfold swift.shOwn
    isplitl [Hsh1]
    · iExactEq Hsh1; rfl
    iunfold swift.shOwnR
    iframe Hstat Hfq Hrdr Henv Hpin
  isplitl [HRC]
  · iexact HRC
  isplitl [Hph Hcmd Hdep Hhs Hpr Hseq Hmsg]
  · iunfold swift.descF
    iframe Hph Hcmd Hvs Hdep HD Hhs HHs Hpr Hseq Hmsg Hbag Hmx
    ipureintro; exact Hop
  isplitl [Htok HsT]
  · iunfold swift.rowTokO
    ileft
    iframe Htok HsT
  isplitr
  · iexact Hcm
  isplitr
  · isplitr
    · iunfold swift.rowAcc
      isplitr
      · iexact Hac
      isplitr
      · ipureintro; rw [← Hepr]; exact Hiss
      rw [← Hepr]; iexact Hpro
    iexact Hrep
  isplitr
  · ipureintro; rw [← Hepr, ← Heph]; exact Hph3
  isplitr
  · iexact Hpw
  isplitr
  · iexact Hdw
  isplitr
  · ipureintro; exact ⟨Hrpo, Hsq.1⟩
  isplitr
  · iexact HsB
  iframe Hsl Hfa Hcore Hrest
  isplitl [HoF]
  · iExactEq HoF; rfl
  rw [swift.kf_seq]
  iframe Ha Hsc
  isplitl [Hsh2]
  · iexists q; iexact Hsh2
  iExactEq Hγi; rfl

/-- **T7e: park** at the end of the inline call (round 47's parked forms). Tokenless: the parked
free form (`descStP` over `rowTokP`) and the free slot out (as `descOwnF_park`). With the token:
its rest record (`x` itself; `rowPhaseOk`; the `γi` half from `kfK`; `phase`/`dep` halves and a
quarter of `propose` from `descF`; `stopFacts` from `rowAcc`, `dep`'s contents, `phaseWhy`/`depWhy`;
`rowFacts` from the commit fact, `rowAcc` and `descSt`'s phase fact) deposited by `store_putR`, which
gives the free slot and the claim `rest d γi` back; the rest parked token-out (`descOwnFT`, Q1-b/c).
Either way the epoch part (`epochRd q`, `shOwnR`) is out, for the loan's return. -/
theorem swift.seq_park (γ0 : sp.Names) (γc γm : GName) (x : swift.RunX) (rp : Loc)
    (g : swift.DescG) (γi : GName) (RC : Loc → w32 → IProp netDistGF)
    (MP : GoInterface → IProp netDistGF) (γmc : ChanNames) (d : Loc) (y : swift.CommandId)
    (γsg : GName) :
    (x.dc γ0 γc γm rp).ctx ∗ swift.incW g γi γsg ∗ swift.cgG x g ∗
      swift.descOwnF (x.dcK γ0 γc γm rp g (.seq γi)) RC MP γmc d y g.ev.b
        iprop(swift.descRest (x.dcK γ0 γc γm rp g (.seq γi)) g.ev.b y d ∗
          (x.dcK γ0 γc γm rp g (.seq γi)).kf d y) ⊢
    |={⊤}=> ∃ (q : Qp) (bw : w32) (stp rcp : Loc),
      swift.epochRd (x.dcK γ0 γc γm rp g (.seq γi)).γe (x.dcK γ0 γc γm rp g (.seq γi)).γxe
        (x.dcK γ0 γc γm rp g (.seq γi)).rp (x.dcK γ0 γc γm rp g (.seq γi)).rr q g.ev.b bw stp rcp ∗
      swift.shOwnR (x.dcK γ0 γc γm rp g (.seq γi)) d g.ev.b q ∗
      (x.dcK γ0 γc γm rp g (.seq γi)).slot none ∗
      (swift.descOwnFP (x.dcK γ0 γc γm rp g (.seq γi)) RC MP γmc d y g.ev.b q
          iprop(swift.descRest (x.dcK γ0 γc γm rp g (.seq γi)) g.ev.b y d ∗
            (x.dcK γ0 γc γm rp g (.seq γi)).kf d y) ∨
        (swift.claimTok x.γcl (g.ev.b, toCmdId y) (.rest d γi) ∗
          swift.descOwnFT (x.dcK γ0 γc γm rp g (.seq γi)) RC MP γmc d y g.ev.b q
            iprop(swift.descRest (x.dcK γ0 γc γm rp g (.seq γi)) g.ev.b y d ∗
              (x.dcK γ0 γc γm rp g (.seq γi)).kf d y)
            iprop(swift.descRest (x.dcK γ0 γc γm rp g (.seq γi)) g.ev.b y d ∗ swift.kfK0 x d))) := by
  iintro ⟨#Hctx, #Hw, #Hcg, H⟩
  ihave #Hctx2 := Hctx
  iunfold swift.DC.ctx at Hctx2
  iunfold swift.descCtxE at Hctx2
  icases Hctx2 with ⟨%me, %fr, %lg, %dm, %dc, %ex, %dr, %oe, %γa, %γrm, %rc, %γrc, -, -, %Hids, -, -,
    -, -, -, #Hninv, -⟩
  iunfold swift.descOwnF at H
  icases H with ⟨Ho, Hocf⟩
  iunfold swift.descOwn at Ho
  icases Ho with ⟨%s, %f, %qS, %qF, %szS, %szF, %memS, %memF, %hd, #Hhd, #Hcap, HoS, HsR⟩
  iunfold swift.setR at HsR
  iunfold swift.descSt at HsR
  icases HsR with ⟨%q, %bw, %stp, %rcp, %dv, %rv, Hrd, Hsh, -, Hd, Htok, Hcom, #Hra, Hph, #Hpw,
    #Hdw, Hrp, #HsB, HRs⟩
  iunfold swift.shOwn at Hsh
  icases Hsh with ⟨Hγ, HshR⟩
  iunfold swift.rowTokO at Htok
  icases Htok with (⟨Htk, HsT⟩ | ⟨%Hn, Hj, Hslt⟩)
  rotate_left
  · -- tokenless (as `descOwnF_park`)
    imodintro
    iexists q, bw, stp, rcp
    iframe Hrd HshR Hslt
    ileft
    iunfold swift.descOwnFP
    iframe Hocf
    iunfold swift.descOwnP
    iexists s, f, qS, qF, szS, szF, memS, memF, hd
    iframe Hhd Hcap HoS
    iunfold swift.setRP
    iunfold swift.descStP
    iexists dv, rv
    iframe Hγ Hd Hcom Hra Hph Hpw Hdw Hrp HsB HRs
    iunfold swift.rowTokP
    iframe Hj
    ipureintro; exact Hn
  -- with the token: the rest record into the store
  icases Hph with %Hph
  icases Hrp with %Hrp
  icases Hra with ⟨#Hacc, #Hrep⟩
  iunfold swift.rowAcc at Hacc
  icases Hacc with ⟨#Hac, %Hiss, #Hpro⟩
  icases HRs with ⟨Hsl, Hfa, HoF, Hcore, Hrest, Hkf⟩
  isimp only [swift.kf_seq] at Hkf
  icases Hkf with ⟨Ha, Hk, Hγi, Hsc⟩
  iunfold swift.slotT at HsT
  icases HsT with ⟨Hrc, Htx⟩
  iunfold swift.shOwnR at HshR
  icases HshR with ⟨Hstat, Hfq, Hrdr, Henv, Hpin⟩
  isimp only [swift.env_seq] at Henv
  icases Henv with ⟨⟨%iL, Hloan, Hlr⟩, HX, #HE⟩
  ihave #HE2 := HE
  iunfold swift.epInvs at HE2
  icases HE2 with ⟨#HI, -, -⟩
  iunfold swift.descF at Hd
  icases Hd with ⟨Hph0, Hcmd, #Hvs, Hdep, #HD, Hhs, #HHs, Hpr, Hseq, Hmsg, #Hbag, #Hmx, %Hop⟩
  icases (typedPointsto_half_split _ _ _).1 $$ Hph0 with ⟨Hph1, Hph2⟩
  icases (typedPointsto_half_split _ _ _).1 $$ Hdep with ⟨Hdep1, Hdep2⟩
  icases (typedPointsto_half_split _ _ _).1 $$ Hpr with ⟨Hpr1, Hpr2⟩
  imod swift.store_putR γ0 x.γv x.γe x.γo ⟨x.γxm, x.γout, x.γcl, x.str, x.N, x.r, x.γxu, x.γrp, x.γcg⟩ x.k x.γd x.γn g
      (x.epN rp) (x.DR γ0 g.ev.b) (swift.descGo x.γn g x.str) x.str iL q (g.ev.b, toCmdId y)
      (swift.ClK.rest d γi) rv (0, (1 : Qp).half.half.half)
    $$ [Hloan Htk Htx Hrc Hγi Hph2 Hdep2 Hpr2 Hcom] with ⟨Hloan, Hslt, Hcl⟩
  · isplitr
    · iexact Hninv
    isplitr
    · iexact HI
    isplitl [Hloan]
    · iexact Hloan
    isplitl [Htk]
    · iExactEq Htk; rfl
    isplitl [Hγi Hph2 Hdep2 Hpr2 Hcom]
    · simp only [swift.recOf, swift.retWhy]
      iexists y, dv
      isplitr
      · ipureintro; exact ⟨rfl, Hrp.1⟩
      isplitl [Hγi]
      · iExactEq Hγi; rfl
      isplitl [Hph2]
      · iexact Hph2
      isplitl [Hdep2]
      · iexact Hdep2
      isplitl [Hpr2]
      · iexact Hpr2
      isplitr
      · iunfold swift.stopFacts
        ihave #Hpro2 := Hpro
        icases Hpro2 with (%Hn | #Hgv)
        · ileft; ipureintro; exact Hn
        iright
        isplitr
        · iexact Hgv
        isplitr
        · iexact HD
        isplitr
        · iExactEq Hpw; rfl
        isplitr
        · iExactEq Hdw; rfl
        -- round 52 (51-5): the proposal's `propIs`, from the owner's `repPre` (T7e)
        ihave #HpP := swift.repPre_propIs _ _ _ _ _ _ $$ Hrep
        icases HpP with (%Hn' | #HpI)
        · icases Hgv with ⟨%gv, #Hg⟩
          ihave %hnn := typedPointsto_not_null _ _ _ $$ Hg
          exfalso; exact hnn Hn'
        iExactEq HpI; rfl
      isplitl [Hcom]
      · iunfold swift.rowFacts
        isplitl [Hcom]
        · iExactEq Hcom; rfl
        isplitr
        · iExactEq Hac; rfl
        isplitr
        · ipureintro; exact Hiss
        isplitr
        · iexact Hpro
        ipureintro; exact Hph
      -- round 56 (D79 (1), 52-3; 52-2): the incarnation's commit witness by ballot (the seq
      -- owner's `incW` is `soO`'s, held by `seq_close`)
      iapply swift.cgW_of x g γi γsg
      iframe Hcg Hw
    isplitl [Htx]
    · iExactEq Htx; rfl
    iExactEq Hrc; rfl
  imodintro
  iexists q, bw, stp, rcp
  isplitl [Hrd]
  · iexact Hrd
  isplitl [Hstat Hfq Hrdr Hloan Hlr HX Hpin]
  · iunfold swift.shOwnR
    iframe Hstat Hfq Hrdr Hpin
    rw [swift.env_seq]
    iframe HX HE
    iexists iL; iframe Hloan Hlr
  isplitl [Hslt]
  · iExactEq Hslt; rfl
  iright
  isplitl [Hcl]
  · iExactEq Hcl; rfl
  iunfold swift.descOwnFT
  isplitr [Hocf]
  · iexists s, f, qS, qF, szS, szF, memS, memF, hd
    iframe Hhd Hcap HoS
    iunfold swift.descStT
    iexists dv
    isplitl [Hγ]
    · iexact Hγ
    isplitl [Hph1 Hcmd Hdep1 Hhs Hpr1 Hseq Hmsg]
    · iunfold swift.descFT
      iframe Hph1 Hcmd Hvs Hdep1 HD Hhs HHs Hpr1 Hseq Hmsg Hbag Hmx
      ipureintro; exact Hop
    isplitr
    · iexact Hpw
    isplitr
    · iexact Hdw
    isplitr
    · iexact Hrep
    isplitr
    · ipureintro; exact ⟨Hrp.2, fun hn => (Hrp.1.1 hn).2⟩
    isplitr
    · iexact HsB
    iframe Hsl Hfa Hcore Hrest
    isplitl [HoF]
    · iExactEq HoF; rfl
    iunfold swift.kfK0
    iframe Ha Hk Hsc
  iexact Hocf

/-- **The facts of `gO`'s construction the inline call uses** (G-circ), as equations (the kernel
is kept off comparing `g`, its first stage `g0` and its base `g00`). -/
theorem swift.gO_facts (γ0 : sp.Names) (γc γm : GName) (x : swift.RunX) (rp : Loc)
    (g g00 : swift.DescG) (hg : g = swift.gO γ0 γc γm x rp g00) :
    ∃ g0 : swift.DescG, g.so = swift.soO γ0 γc γm x rp (swift.RCh γ0 γc γm rp) g0 ∧
      g0.sr = swift.soRaw γ0 γc γm x rp (swift.RCh γ0 γc γm rp) g00 ∧
      (∀ k, x.dcK γ0 γc γm rp g k = x.dcK γ0 γc γm rp g0 k) ∧
      g.ev = g0.ev ∧ g.mp = g0.mp ∧ g.γk = g0.γk ∧
      g.ev = g00.ev ∧ g.mp = g00.mp ∧ g.γk = g00.γk := by
  subst hg
  exact ⟨_, rfl, rfl, fun k => swift.dcK_gO γ0 γc γm x rp g00 k, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **T7s.l/T7s.u, parked**: the loan at the parked state's incarnation, then the free form
(`seq_unparkF`) or the token-out form (`seq_unparkT`), at `gO`'s first stage `g0` (where `soO`
keeps them), moved to `g` by `gO_facts`' equations. -/
theorem swift.seq_unparkO (γ0 : sp.Names) (γc γm : GName) (x : swift.RunX) (rp : Loc)
    (g g0 : swift.DescG) (hd : ∀ k, x.dcK γ0 γc γm rp g k = x.dcK γ0 γc γm rp g0 k)
    (hev : g.ev = g0.ev) (hmp : g.mp = g0.mp) (hk : g.γk = g0.γk) (d : Loc) (y : swift.CommandId) :
    swift.ownCtx γ0 γc γm x rp g ∗ (x.dc γ0 γc γm rp).ctx ∗
      inv swift.descN (swift.descInv γ0 x.γd x.γn x.γout g (x.epN rp) (x.DR γ0 g.ev.b)
        (swift.descGo x.γn g x.str) x.str) ∗ inv swift.seqN (swift.seqInbox g) ∗ £ 1 ∗
      ghostVar g.γst (1 : Qp).half false ∗
      ghostMapElem x.γn 0 (DFrac.own (1 : Qp).half.half) false ∗ swift.runReader rp x.γdl ∗
      ghostMapElem x.γn 0 (DFrac.own (1 : Qp).half.half.half) false ∗
      (∃ (γi γsg : GName) (γmc : ChanNames) (q : Qp),
        □ swift.incW g0 γi γsg ∗ swift.cgG x g0 ∗ (x.dc γ0 γc γm rp).ctx ∗
        (swift.descOwnFP (x.dcK γ0 γc γm rp g0 (.seq γi)) (swift.RCh γ0 γc γm rp)
            (swift.MPi g0 y γi γsg) γmc d y g0.ev.b q
            iprop(swift.descRest (x.dcK γ0 γc γm rp g0 (.seq γi)) g0.ev.b y d ∗
              (x.dcK γ0 γc γm rp g0 (.seq γi)).kf d y) ∨
         (swift.claimTok x.γcl (g0.ev.b, toCmdId y) (.rest d γi) ∗
          swift.descOwnFT (x.dcK γ0 γc γm rp g0 (.seq γi)) (swift.RCh γ0 γc γm rp)
            (swift.MPi g0 y γi γsg) γmc d y g0.ev.b q
            iprop(swift.descRest (x.dcK γ0 γc γm rp g0 (.seq γi)) g0.ev.b y d ∗
              (x.dcK γ0 γc γm rp g0 (.seq γi)).kf d y)
            iprop(swift.descRest (x.dcK γ0 γc γm rp g0 (.seq γi)) g0.ev.b y d ∗ swift.kfK0 x d)))) ⊢
    |={⊤}=> ghostVar g.γst (1 : Qp).half false ∗ ∃ (γi γsg : GName) (γmc : ChanNames),
      □ swift.incW g γi γsg ∗
      swift.descOwnF (x.dcK γ0 γc γm rp g (.seq γi)) (swift.RCh γ0 γc γm rp) (swift.MPi g y γi γsg) γmc d y
        g.ev.b iprop(swift.descRest (x.dcK γ0 γc γm rp g (.seq γi)) g.ev.b y d ∗
          (x.dcK γ0 γc γm rp g (.seq γi)).kf d y) := by
  iintro ⟨#HoC, #Hctx, #HI, #HSI, Hlc, Hst, Hn1, Hrdr, Hslt, ⟨%γi, %γsg, %γmc, %q0, #Hw, -, -, Hform⟩⟩
  imod swift.seq_lend γ0 γc γm x rp g γi d $$ [Hlc Hst Hn1 Hrdr] with ⟨Hst, %q, Hrd, HshR⟩
  · iframe HI HSI HoC Hlc Hst Hn1 Hrdr
  ihave #HoC2 := HoC
  iunfold swift.ownCtx at HoC2
  icases HoC2 with ⟨#Hdsc, -, -, #HRC, -, -⟩
  ihave #Hdsc2 := Hdsc
  iunfold swift.descDSCtx at Hdsc2
  icases Hdsc2 with ⟨-, -, #HshI, -, -, -⟩
  ihave Hown : |={⊤}=> swift.descOwnF (x.dcK γ0 γc γm rp g0 (.seq γi)) (swift.RCh γ0 γc γm rp)
      (swift.MPi g0 y γi γsg) γmc d y g0.ev.b
      iprop(swift.descRest (x.dcK γ0 γc γm rp g0 (.seq γi)) g0.ev.b y d ∗
        (x.dcK γ0 γc γm rp g0 (.seq γi)).kf d y) $$ [Hrd HshR Hslt Hform]
  · rw [hd (.seq γi), hev] at *
    icases Hform with (HFP | ⟨Hcl, HFT⟩)
    · iapply swift.seq_unparkF γ0 γc γm x rp g0 γi _ _ γmc d y q0 q g0.ev.bw g0.ev.stp g0.ev.rcp
      iframe HshI Hrd HshR HRC HFP
      rw [swift.slot_seq]; iexact Hslt
    · iapply swift.seq_unparkT γ0 γc γm x rp g0 γi _ _ γmc d y q0 q g0.ev.bw g0.ev.stp g0.ev.rcp
      iframe Hctx HshI Hrd HshR HRC Hcl HFT
      rw [swift.slot_seq]; iexact Hslt
  imod Hown
  imodintro
  iframe Hst
  iexists γi, γsg, γmc
  isplitr
  · imodintro; rw [swift.incW_congr g g0 hk]; iexact Hw
  rw [hd (.seq γi), hev, swift.MPi_congr g g0 hmp hk]
  iexact Hown

/-- **T7e/T7r: the close** after the inline call: parked (`seq_park`, then the loan back,
`seq_return`) into `g.so` (`soO` at `g0`), or retired (`descGone`: the store's element and the
free slot; the loan back). R's `cntFrozen` half is whole again (¼ from the loan's record, ⅛ the
slot, ⅛ kept). -/
theorem swift.seq_close (γ0 : sp.Names) (γc γm : GName) (x : swift.RunX) (rp : Loc)
    (g g0 : swift.DescG) (hso : g.so = swift.soO γ0 γc γm x rp (swift.RCh γ0 γc γm rp) g0)
    (hd : ∀ k, x.dcK γ0 γc γm rp g k = x.dcK γ0 γc γm rp g0 k)
    (hev : g.ev = g0.ev) (hmp : g.mp = g0.mp) (hk : g.γk = g0.γk) (γi γsg : GName) (γmc : ChanNames)
    (d : Loc) (y : swift.CommandId) :
    (x.dc γ0 γc γm rp).ctx ∗ □ swift.incW g γi γsg ∗ swift.cgG x g ∗ £ 1 ∗ £ 1 ∗
      ghostMapElem x.γn 0 (DFrac.own (1 : Qp).half.half.half) false ∗
      (swift.descOwnF (x.dcK γ0 γc γm rp g (.seq γi)) (swift.RCh γ0 γc γm rp) (swift.MPi g y γi γsg) γmc d y
          g.ev.b iprop(swift.descRest (x.dcK γ0 γc γm rp g (.seq γi)) g.ev.b y d ∗
            (x.dcK γ0 γc γm rp g (.seq γi)).kf d y) ∨
        swift.descDone (x.dcK γ0 γc γm rp g (.seq γi)) g.ev.b y d) ⊢
    |={⊤}=> ghostMapElem x.γn 0 (DFrac.own (1 : Qp).half) false ∗ swift.runReader rp x.γdl ∗
      (g.so d y ∨ ghostMapElem g.γS d (DFrac.own 1) y) := by
  iintro ⟨#Hctx, #Hw, #Hcg, Hlc1, Hlc2, Hn3, Hres⟩
  icases Hres with (Hown | Hdone)
  · imod swift.seq_park γ0 γc γm x rp g γi _ _ γmc d y γsg $$ [Hown] with
      ⟨%q, %bw, %stp, %rcp, Hrd, HshR, Hslt, Hform⟩
    · iframe Hctx Hw Hcg Hown
    imod swift.seq_return γ0 γc γm x rp g γi d q bw stp rcp $$ [Hlc1 Hlc2 Hrd HshR] with ⟨Hn1, Hrdr⟩
    · iframe Hlc1 Hlc2 Hrd HshR
    imodintro
    isimp only [swift.slot_seq] at Hslt
    isplitl [Hn1 Hslt Hn3]
    · iapply (swift.frozen_parts x.γn 0 false).2
      iframe Hn1 Hslt Hn3
    iframe Hrdr
    ileft
    rw [hso]
    iunfold swift.soO
    iright
    iexists γi, γsg, γmc, q
    isplitr
    · imodintro; rw [← swift.incW_congr g g0 hk]; iexact Hw
    isplitr
    · -- round 58 (D82 (1)): the epoch's registration (the tokenless home's `cgW`)
      iunfold swift.cgG at Hcg
      iunfold swift.cgG
      rw [← hev, ← hk]; iexact Hcg
    isplitr
    · iexact Hctx
    rw [← hd (.seq γi), ← hev, ← swift.MPi_congr g g0 hmp hk]
    iexact Hform
  · iunfold swift.descDone at Hdone
    iunfold swift.descGone at Hdone
    icases Hdone with ⟨-, -, Hret, %q, %bw, %stp, %rcp, Hrd, HshR⟩
    isimp only [swift.ret_seq] at Hret
    icases Hret with ⟨HS, Hslt⟩
    imod swift.seq_return γ0 γc γm x rp g γi d q bw stp rcp $$ [Hlc1 Hlc2 Hrd HshR] with ⟨Hn1, Hrdr⟩
    · iframe Hlc1 Hlc2 Hrd HshR
    imodintro
    isplitl [Hn1 Hslt Hn3]
    · iapply (swift.frozen_parts x.γn 0 false).2
      iframe Hn1 Hslt Hn3
    iframe Hrdr
    iright
    iexact HS

end lemmas

end Perennial.github_com.imdea_software.swiftpaxos
