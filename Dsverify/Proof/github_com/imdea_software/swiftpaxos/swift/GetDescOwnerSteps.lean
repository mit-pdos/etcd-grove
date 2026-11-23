/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/GetDescOwnerSteps.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
**The owner-side ghost steps of `getCmdDescWith`** (round O1, sv-swa; D59 (3); table §3R10.7 T14's
nested lookup "T26/T2'/T5l-T5r/T3'c/T4n/T4l/T4c with `descX`, `ρ = own iL j`"): what
`wp_coreO` (GetDescOwner.lean) needs beyond `wp_coreD`'s lemmas, for a creator that holds an
owner record's loan environment `envK` instead of the run loop's `γst` half.

* `swift.envK_open`: both owner kinds' `envK` as one shape (loan token `iL`, receipt half
  `(j0, ¼)`, `descX q`, the epoch's invariants), with the wand back.
* `swift.lrcpt_quarters`, `swift.lendRef_own`: the lock-lend's refuter `own iL j0` is a quarter of
  the receipt (T5l by G/I).
* `swift.descInv_allocIncL`: T2' by G/I (`descInv_allocInc` at the loan token).
* `swift.descInv_fqAgree`: the creator's `FQ` share (from `shOwnR`, at an existential value) agrees
  with the epoch's `g.ev.fq` (the sub-pool's own share, in `descInv`; the loan token refutes the
  stopped branch), with the epoch's quorum (`newDesc` at `g.ev`'s quorum, T2 by G/I).
* `swift.descRaw_mutex`: the new descriptor's `successorsL` mutex, kept for `depSpecR`'s post.

The existing-entry load (T5l/T5r) is `descInv_lockLend`/`descInv_lockReturn` at `Wt :=` the loan
token and `ρ := own iL j0`: the stopping epoch is refuted by the token (`liveOk_loan`), a read-lent
entry by `cmapLocked_pin_false` and a second lender by `cmapLocked_excl` (both inside
`descInv_lockLend`).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.GetDescWithVocab
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section steps
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF] [SwiftKitDeps]
variable [swift.Assumptions] [replica.Assumptions] [replica.defs.Assumptions] [rpc.Assumptions]
variable [sync.Assumptions] [hook.Assumptions]

/-- The owner records' base fields (round O1; `rfl`, for `simp only`). -/
theorem swift.dcK_rp (x : swift.RunX) (γ : sp.Names) (γc γm : GName) (rp : Loc) (g : swift.DescG)
    (k : swift.OwnK) : (x.dcK γ γc γm rp g k).rp = rp := rfl

theorem swift.dcK_γdl (x : swift.RunX) (γ : sp.Names) (γc γm : GName) (rp : Loc) (g : swift.DescG)
    (k : swift.OwnK) : (x.dcK γ γc γm rp g k).γdl = x.γdl := rfl

theorem swift.dcK_γe (x : swift.RunX) (γ : sp.Names) (γc γm : GName) (rp : Loc) (g : swift.DescG)
    (k : swift.OwnK) : (x.dcK γ γc γm rp g k).γe = x.γe := rfl

theorem swift.dcK_γxe (x : swift.RunX) (γ : sp.Names) (γc γm : GName) (rp : Loc) (g : swift.DescG)
    (k : swift.OwnK) : (x.dcK γ γc γm rp g k).γxe = x.γxe := rfl

theorem swift.dcK_rr (x : swift.RunX) (γ : sp.Names) (γc γm : GName) (rp : Loc) (g : swift.DescG)
    (k : swift.OwnK) : (x.dcK γ γc γm rp g k).rr = x.rr := rfl

theorem swift.dcK_γxp (x : swift.RunX) (γ : sp.Names) (γc γm : GName) (rp : Loc) (g : swift.DescG)
    (k : swift.OwnK) : (x.dcK γ γc γm rp g k).γxp = x.γxp := rfl

theorem swift.dcK_N (x : swift.RunX) (γ : sp.Names) (γc γm : GName) (rp : Loc) (g : swift.DescG)
    (k : swift.OwnK) : (x.dcK γ γc γm rp g k).N = x.N := rfl

/-- **Both owner kinds' loan environments as one shape** (round O1): the loan token, the
receipt half `(j0, ¼)` (`j0 = j` for a goroutine, `0` for the inline owner), `descX q` and the
epoch's invariants; the wand puts the environment back (a goroutine's `γn j ↦{¼}` is kept in it). -/
theorem swift.envK_open (γ : sp.Names) (γc γm : GName) (x : swift.RunX) (rp : Loc)
    (g : swift.DescG) (k : swift.OwnK) (d : Loc) (q : Qp) :
    swift.envK γ γc γm x rp g k d q ⊢
      ∃ (iL j0 : Nat), swift.epochLoan g.γq iL q ∗
        ghostMapElem g.γlj iL (DFrac.own (1 : Qp).half) (j0, (1 : Qp).half.half) ∗
        (∃ dm : GoSlice, swift.descX rp x.γd g dm q) ∗ swift.epInvs γ γc γm x rp g ∗
        (swift.epochLoan g.γq iL q -∗
          ghostMapElem g.γlj iL (DFrac.own (1 : Qp).half) (j0, (1 : Qp).half.half) -∗
          (∃ dm : GoSlice, swift.descX rp x.γd g dm q) -∗ swift.envK γ γc γm x rp g k d q) := by
  cases k with
  | go j iL γi =>
    simp only [swift.envK]
    iintro ⟨Hloan, Hr, Hj, HX, #HE⟩
    iexists iL, j
    iframe Hloan Hr HX
    isplitr
    · iexact HE
    iintro Hloan Hr HX
    iframe Hloan Hr Hj HX
    iexact HE
  | seq γi =>
    simp only [swift.envK]
    iintro ⟨⟨%iL, Hloan, Hr⟩, HX, #HE⟩
    iexists iL, (0 : Nat)
    iframe Hloan Hr HX
    isplitr
    · iexact HE
    iintro Hloan Hr HX
    iframe HX
    isplitl [Hloan Hr]
    · iexists iL
      iframe Hloan Hr
    iexact HE

/-- `envK_open` at an owner record's `env` (round O1). -/
theorem swift.envK_openK (γ : sp.Names) (γc γm : GName) (x : swift.RunX) (rp : Loc)
    (g : swift.DescG) (k : swift.OwnK) (d : Loc) (q : Qp) :
    (x.dcK γ γc γm rp g k).env d q ⊢
      ∃ (iL j0 : Nat), swift.epochLoan g.γq iL q ∗
        ghostMapElem g.γlj iL (DFrac.own (1 : Qp).half) (j0, (1 : Qp).half.half) ∗
        (∃ dm : GoSlice, swift.descX rp x.γd g dm q) ∗ swift.epInvs γ γc γm x rp g ∗
        (swift.epochLoan g.γq iL q -∗
          ghostMapElem g.γlj iL (DFrac.own (1 : Qp).half) (j0, (1 : Qp).half.half) -∗
          (∃ dm : GoSlice, swift.descX rp x.γd g dm q) -∗ (x.dcK γ γc γm rp g k).env d q) :=
  swift.envK_open γ γc γm x rp g k d q

/-- A receipt half of a loan as two quarters (round O1; `rcpt_quarters` at the loans' `Nat` keys). -/
theorem swift.lrcpt_quarters (γ : GName) (k : Nat) (v : Nat × Qp) :
    ghostMapElem (GF := netDistGF) γ k (DFrac.own (1 : Qp).half) v ⊣⊢
      ghostMapElem γ k (DFrac.own (1 : Qp).half.half) v ∗
        ghostMapElem γ k (DFrac.own (1 : Qp).half.half) v := by
  conv => lhs; rw [← Qp.half_add_half (1 : Qp).half]
  exact (ghostMapElem_fractional k γ v).fractional _ _

/-- The lock-lend refuter of a loan holder (round O1; T5l by G/I, `ρ = own iL j0`). -/
theorem swift.lendRef_own (g : swift.DescG) (k : GoString) (iL j : Nat) :
    swift.lendRef g k (.own iL j) =
      ghostMapElem g.γlj iL (DFrac.own (1 : Qp).half.half) (j, (1 : Qp).half.half) := rfl

/-- T4n's ghost step as `descInv_loanRecAcc`'s update (round O1): `cntLGhost_spawn_frac` with the
loan record's registry share. -/
theorem swift.cntLGhost_spawn_hup (γn : GName) (dm : GoSlice) (γdl : GName) (d c : w64)
    (T : List Nat) (j : Nat) (q : Qp) (hc : sint.Z c < sint.Z d) :
    swift.cntLGhost γn dm γdl d c T ∗ ghostMapElem γn j (DFrac.own q) false ⊢
      |={⊤ \ ↑swift.descN}=> (∃ i, swift.cntLGhost γn dm γdl d (c + W64 1) (i :: T) ∗
        swift.descSlot γn dm γdl i) ∗ ghostMapElem γn j (DFrac.own q) false := by
  iintro H
  imod (swift.cntLGhost_spawn_frac γn dm γdl d c T j q hc) $$ H with ⟨%i, HG, Hs, Hj⟩
  imodintro
  iframe Hj
  iexists i
  iframe

/-- **T2' by a goroutine or the inline owner** (round O1; round 45's `descInv_allocIncL`):
`descInv_allocInc` with the creator's loan token as the not-stopped witness. -/
theorem swift.descInv_allocIncL
    (γ : sp.Names) (γd γn γout : GName) (g : swift.DescG) (ep : swift.EpN)
    (DR : Loc → IProp netDistGF) (Run : Loc → swift.CommandId → IProp netDistGF)
    (str : swift.CommandId → GoString) (a : GoString × Loc) (iL : Nat) (q : Qp) :
    inv swift.descN (swift.descInv γ γd γn γout g ep DR Run str) ∗ swift.epochLoan g.γq iL q ∗ £ 1 ⊢
    |={⊤}=> swift.epochLoan g.γq iL q ∗
      ∃ γi : GName, ghostVar γi 1 a ∗ ghostMapElem g.γj γi (DFrac.own 1) ((0 : Nat), (1 : Qp)) :=
  swift.descInv_allocInc γ γd γn γout g ep DR Run str a _ (swift.liveOk_loan g iL q)

theorem swift.poolX_eq (n : swift.EpN) (v : swift.EpV) (X : Qp → IProp netDistGF) (Q : Qp)
    (γp : GName) (q0 : Qp) (L : GMap Nat Qp) :
    swift.epochPoolX n v X Q γp q0 L ⊣⊢ swift.poolS (swift.epochShareX n v X) Q γp q0 L := .rfl

/-- **The creator's `FQ` share is the epoch's** (round O1; T2 by G/I): `descInv` (not stopped: the
witness `Wt`) holds the sub-pool's own share `epochShareX q0`, whose `fqShare` is at `g.ev.fq`;
two points-tos of `FQ` agree. The epoch's quorum `quorumIs g.ev.fq g.ev.szF g.ev.memF` is
persistent and comes out. -/
theorem swift.descInv_fqAgree (γ : sp.Names) (γd γn γout : GName) (g : swift.DescG) (ep : swift.EpN)
    (DR : Loc → IProp netDistGF) (Run : Loc → swift.CommandId → IProp netDistGF)
    (str : swift.CommandId → GoString) (Wt : IProp netDistGF) (hWt : swift.liveOk g Wt)
    (rp : Loc) (hrp : ep.rp = rp) (fq : GoInterface) (q : Qp) :
    inv swift.descN (swift.descInv γ γd γn γout g ep DR Run str) ∗ £ 1 ∗ Wt ∗
      typedPointsto (swift.fld rp go!"FQ") fq (DFrac.own q) ⊢
    |={⊤}=> Wt ∗ typedPointsto (swift.fld rp go!"FQ") fq (DFrac.own q) ∗ ⌜fq = g.ev.fq⌝ ∗
      replica.mset.quorumIs g.ev.fq g.ev.szF g.ev.memF := by
  subst hrp
  iintro ⟨#HI, Hlc, HWt, HFQ⟩
  iinv HI with Hi Hclose
  imod lc_fupd_elim_later (E := ⊤ \ ↑swift.descN) $$ Hlc Hi with Hi
  iunfold swift.descInv at Hi
  icases Hi with ⟨%st, Hst2, Hrest⟩
  cases st
  rotate_left
  · simp only [↓reduceIte]
    iexfalso
    have hWt' := hWt
    unfold swift.liveOk at hWt'
    iapply hWt' $$ [HWt Hst2 Hrest]
    iframe
  simp only [Bool.false_eq_true, ↓reduceIte]
  icases Hrest with ⟨%Mc, Hrest⟩
  icases Hrest with ⟨%q0, Hrest⟩
  icases Hrest with ⟨%L, Hrest⟩
  icases Hrest with ⟨%dm1, Hrest⟩
  icases Hrest with ⟨%W, Hview, HW, HWd, Hents, HK, Hpool, Hrec, Hled, Hrca⟩
  ihave Hpool := (swift.poolX_eq ep g.ev (swift.descX ep.rp γd g dm1) g.Qd g.γq q0 L).1 $$ Hpool
  iunfold swift.poolS at Hpool
  icases Hpool with ⟨Ha, Hs, Hw⟩
  iunfold swift.epochShareX at Hs
  icases Hs with ⟨Hs, HX⟩
  iunfold swift.epochShare at Hs
  icases Hs with ⟨Hrd, Hpin, Hst, Hfq⟩
  iunfold swift.fqShare at Hfq
  icases Hfq with ⟨Hfq, #HqF, %Hm⟩
  icombine HFQ Hfq gives %Heq
  subst Heq
  imod Hclose $$ [Hst2 Hview HW HWd Hents HK Ha Hrd Hpin Hst Hfq HX Hw Hrec Hled Hrca] with -
  · inext
    iunfold swift.descInv
    iexists false
    simp only [Bool.false_eq_true, ↓reduceIte]
    iframe Hst2
    iexists Mc, q0, L, dm1, W
    iframe Hview HW HWd Hents HK Hrec Hled Hrca
    iapply (swift.poolX_eq ep g.ev (swift.descX ep.rp γd g dm1) g.Qd g.γq q0 L).2
    iunfold swift.poolS
    iframe Ha Hw
    iunfold swift.epochShareX
    iframe HX
    iunfold swift.epochShare
    iframe Hrd Hpin Hst
    iunfold swift.fqShare
    iframe Hfq HqF
    ipureintro; exact Hm
  imodintro
  iframe HWt HFQ HqF
  ipureintro; rfl

-- `swift.descRaw_mutex`: moved to NewDesc.lean (round 46, D60 O1-a: `wp_coreD` uses it).

end steps

end Perennial.github_com.imdea_software.swiftpaxos
