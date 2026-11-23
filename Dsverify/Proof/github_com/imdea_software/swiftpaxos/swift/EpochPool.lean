/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/EpochPool.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
The epoch pool (notes/prove-swift.md §11, §13): how the run loop lends the epoch's class-E
resources to the descriptor goroutines and gets all of them back once they are stopped.

* `swift.EpN` (names and locations) and `swift.EpV` (the epoch's values: ballot `b` (model) and
  `bw` (Go), `State`'s and `repchan`'s pointers, `status`).
* `swift.epochShare n v q`: a share `q` of the epoch: the descriptor side's `epochRd` (`ballot`,
  `State`, `repchan` at `q`, the epoch token at `(b, b)`, `γxe`), the epoch pin (`γxp` at `q`, value
  `b`) and `status` at `q`. Fractional (`swift.epochShare_split`).
* `swift.epochLoan γp i q`: the token of loan `i` (fraction `q`) a descriptor goroutine holds with
  its share.
* `swift.epochPool n v Q γp q0 L`: the run loop's side: the loans' authority `L` (loan ↦ its
  fraction), its own share `q0`, and the closing wand: its share with every lent share gives the
  pool's whole `Q` back. No arithmetic on fractions is needed: lending splits `q0` in halves,
  a return adds the returned share.

Laws: `epochPool_init` (a whole `Q` becomes an empty pool), `epochPool_lend` (a share and its loan
token for a new goroutine), `epochPool_return` (a goroutine's share comes back with its token),
`epochPool_stopped` (with every outstanding loan's share back, e.g. from `stopDescs`, the run
loop has the whole `Q`: **the stopped epoch**), `epochPool_borrow` (the run loop's own share, for a
sequential descriptor it runs inline, and back).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.Deliver

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

/-- The epoch's ghost names and locations. -/
structure swift.EpN where
  γe : GName
  γxe : GName
  γxp : GName
  rp : Loc
  rr : Loc
  /-- round 23 (D18 G2): the replica count (the fast quorum's members are in `AQ N b`) -/
  N : Nat

/-- The epoch's values (round 23, D18 G2: with the fast quorum `FQ`'s value `fq`, its size
`szF` and members `memF`). -/
structure swift.EpV where
  b : Nat
  bw : w32
  stp : Loc
  rcp : Loc
  st : w64
  fq : GoInterface
  szF : Nat
  memF : w32 → Prop

section defs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics]

/-- A share `q` of the fast quorum `FQ` (round 23, D18 G2: an epoch field, `handleSync` writes
it; a descriptor's `descCore` holds a share for its life): the value with its quorum and the
members in the ballot's fast quorum `AQ` (fixedMajority: `FQ = qs.AQ(ballot)`); round 35 (table
E7, D7): the ballot's leader is a member (what `shOwnR` needs; `New`/`handleSync` by `aq_fqOk`). -/
def swift.fqShare (n : swift.EpN) (v : swift.EpV) (q : Qp) : IProp netDistGF :=
  iprop(typedPointsto (swift.fld n.rp go!"FQ") v.fq (DFrac.own q) ∗
    replica.mset.quorumIs v.fq v.szF v.memF ∗ ⌜(∀ i : w32, v.memF i → sp.rid i ∈ sp.AQ n.N v.b) ∧
      (∀ i : w32, 0 ≤ sint.Z i → sp.rid i = sp.leaderOf n.N v.b → v.memF i)⌝)

/-- A share `q` of the epoch (see the file header). -/
def swift.epochShare (n : swift.EpN) (v : swift.EpV) (q : Qp) : IProp netDistGF :=
  iprop(swift.epochRd n.γe n.γxe n.rp n.rr q v.b v.bw v.stp v.rcp ∗ ghostVar n.γxp q v.b ∗
    typedPointsto (swift.fld n.rp go!"status") v.st (DFrac.own q) ∗
    swift.fqShare n v q)

/-- Loan `i`'s token (fraction `q`). -/
def swift.epochLoan (γp : GName) (i : Nat) (q : Qp) : IProp netDistGF :=
  ghostMapElem γp i (DFrac.own 1) q

/-- The run loop's side of the pool (see the file header). -/
def swift.epochPool (n : swift.EpN) (v : swift.EpV) (Q : Qp) (γp : GName) (q0 : Qp)
    (L : GMap Nat Qp) : IProp netDistGF :=
  iprop(ghostMapAuth γp 1 L ∗ swift.epochShare n v q0 ∗
    (swift.epochShare n v q0 -∗ ([∗map] _i ↦ q ∈ L, swift.epochShare n v q) -∗
      swift.epochShare n v Q))

/-- The run loop's epoch state between descriptor spawns: some pool of the whole `Q`
(the instance of `SyncSpecs`' `EpH`/`Ep true` for the descriptors' part). -/
def swift.epochRun (n : swift.EpN) (v : swift.EpV) (Q : Qp) (γp : GName) : IProp netDistGF :=
  iprop(∃ (q0 : Qp) (L : GMap Nat Qp), swift.epochPool n v Q γp q0 L)

/-- **The stopped epoch** (`Ep false` for the descriptors' part): the whole `Q` back. -/
def swift.epochStopped (n : swift.EpN) (v : swift.EpV) (Q : Qp) : IProp netDistGF :=
  swift.epochShare n v Q

end defs

section laws
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics]

/-- `epochShare` is fractional. -/
theorem swift.epochShare_split (n : swift.EpN) (v : swift.EpV) (q1 q2 : Qp) :
    swift.epochShare n v (q1 + q2) ⊣⊢ swift.epochShare n v q1 ∗ swift.epochShare n v q2 := by
  unfold swift.epochShare swift.epochRd swift.epochTok
  have hp : ∀ (l : Loc) {V : Type} [TypedPointsto (GF := netDistGF) V] (x : V),
      typedPointsto (GF := netDistGF) l x (DFrac.own (q1 + q2)) ⊣⊢
        typedPointsto l x (DFrac.own q1) ∗ typedPointsto l x (DFrac.own q2) := by
    intro l V _ x
    rw [← DFrac.op_own]
    exact (typedPointsto_dfractional (GF := netDistGF) l x).dfractional _ _
  have hg : ∀ {A : Type} [Pos.Countable A] (γ : GName) (a : A),
      (ghostVar (GF := netDistGF) γ (q1 + q2) a : IProp netDistGF) ⊣⊢
        ghostVar γ q1 a ∗ ghostVar γ q2 a := by
    intro A _ γ a
    exact (ghostVar_fractional γ a).fractional _ _
  unfold swift.fqShare
  constructor
  · iintro ⟨⟨Hb, Hs, Hr, He, Hx, %Hp⟩, Hpin, Hst, Hfq, #HqF, %Hm⟩
    icases (hp _ _).1 $$ Hfq with ⟨Hfq1, Hfq2⟩
    icases (hp _ _).1 $$ Hb with ⟨Hb1, Hb2⟩
    icases (hp _ _).1 $$ Hs with ⟨Hs1, Hs2⟩
    icases (hp _ _).1 $$ Hr with ⟨Hr1, Hr2⟩
    icases (hp _ _).1 $$ Hst with ⟨Hst1, Hst2⟩
    icases (hg _ _).1 $$ He with ⟨He1, He2⟩
    icases (hg _ _).1 $$ Hx with ⟨Hx1, Hx2⟩
    icases (hg _ _).1 $$ Hpin with ⟨Hpin1, Hpin2⟩
    isplitl [Hb1 Hs1 Hr1 He1 Hx1 Hpin1 Hst1 Hfq1]
    · iframe; iframe HqF; ipureintro; exact ⟨Hp, Hm⟩
    · iframe; iframe HqF; ipureintro; exact ⟨Hp, Hm⟩
  · iintro ⟨⟨⟨Hb1, Hs1, Hr1, He1, Hx1, %Hp⟩, Hpin1, Hst1, Hfq1, #HqF, %Hm⟩,
      ⟨⟨Hb2, Hs2, Hr2, He2, Hx2, -⟩, Hpin2, Hst2, Hfq2, -, -⟩⟩
    isplitl [Hb1 Hs1 Hr1 He1 Hx1 Hb2 Hs2 Hr2 He2 Hx2]
    · isplitl [Hb1 Hb2]
      · iapply (hp _ _).2; iframe
      isplitl [Hs1 Hs2]
      · iapply (hp _ _).2; iframe
      isplitl [Hr1 Hr2]
      · iapply (hp _ _).2; iframe
      isplitl [He1 He2]
      · iapply (hg _ _).2; iframe
      isplitl [Hx1 Hx2]
      · iapply (hg _ _).2; iframe
      ipureintro; exact Hp
    isplitl [Hpin1 Hpin2]
    · iapply (hg _ _).2; iframe
    isplitl [Hst1 Hst2]
    · iapply (hp _ _).2; iframe
    iframe HqF
    isplitl [Hfq1 Hfq2]
    · iapply (hp _ _).2; iframe
    ipureintro; exact Hm

/-- A whole `Q` of the epoch becomes an empty pool. -/
theorem swift.epochPool_init (n : swift.EpN) (v : swift.EpV) (Q : Qp) :
    swift.epochShare n v Q ⊢ |==> ∃ γp, swift.epochPool n v Q γp Q ∅ := by
  iintro HQ
  imod ghost_map_alloc_empty (GF := netDistGF) (K := Nat) (V := Qp) with ⟨%γp, Ha⟩
  imodintro
  iexists γp
  unfold swift.epochPool
  iframe
  iintro H -
  iexact H

/-- Lending: half of the run loop's share and a fresh loan token for a new goroutine. -/
theorem swift.epochPool_lend (n : swift.EpN) (v : swift.EpV) (Q : Qp) (γp : GName) (q0 : Qp)
    (L : GMap Nat Qp) (i : Nat) (hi : L.lookup i = none) :
    swift.epochPool n v Q γp q0 L ⊢
      |==> (swift.epochPool n v Q γp q0.half (L.insert i q0.half) ∗
        swift.epochShare n v q0.half ∗ swift.epochLoan γp i q0.half) := by
  unfold swift.epochPool swift.epochLoan
  iintro ⟨Ha, Hs, Hc⟩
  ihave Hnew := ghost_map_insert (GF := netDistGF) i q0.half hi $$ Ha
  imod Hnew with ⟨Ha, Hl⟩
  have hsplit := swift.epochShare_split n v q0.half q0.half
  rw [Qp.half_add_half] at hsplit
  icases hsplit.1 $$ Hs with ⟨Hs1, Hs2⟩
  imodintro
  iframe Ha Hs1 Hl Hs2
  iintro Hq Hm
  icases (BigSepM.bigSepM_insert hi).1 $$ Hm with ⟨Hi, Hm⟩
  iapply Hc $$ [Hq Hi] Hm
  iapply hsplit.2
  iframe

/-- A goroutine's share comes back with its loan token. -/
theorem swift.epochPool_return (n : swift.EpN) (v : swift.EpV) (Q : Qp) (γp : GName) (q0 : Qp)
    (L : GMap Nat Qp) (i : Nat) (q : Qp) :
    swift.epochPool n v Q γp q0 L ∗ swift.epochShare n v q ∗ swift.epochLoan γp i q ⊢
      |==> swift.epochPool n v Q γp (q0 + q) (GMap.delete i L) := by
  unfold swift.epochPool swift.epochLoan
  iintro ⟨⟨Ha, Hs, Hc⟩, Hq, Hl⟩
  ihave %Hlk := ghost_map_lookup $$ Ha Hl
  imod ghost_map_delete (GF := netDistGF) $$ Ha Hl with Ha
  imodintro
  iframe Ha
  isplitl [Hs Hq]
  · iapply (swift.epochShare_split n v q0 q).2
    iframe
  iintro Hs Hm
  icases (swift.epochShare_split n v q0 q).1 $$ Hs with ⟨Hs0, Hsq⟩
  iapply Hc $$ Hs0
  iapply (BigSepM.bigSepM_delete Hlk).2
  iframe

/-- **The stopped epoch**: with every outstanding loan's share back (`stopDescs` collects them
from the stopped goroutines), the run loop has the whole `Q`. -/
theorem swift.epochPool_stopped (n : swift.EpN) (v : swift.EpV) (Q : Qp) (γp : GName) (q0 : Qp)
    (L : GMap Nat Qp) :
    swift.epochPool n v Q γp q0 L ∗ ([∗map] _i ↦ q ∈ L, swift.epochShare n v q) ⊢
      swift.epochShare n v Q := by
  unfold swift.epochPool
  iintro ⟨⟨-, Hs, Hc⟩, Hm⟩
  iapply Hc $$ Hs Hm

/-- The run loop borrows its own share (to run a sequential descriptor inline) and gives it back. -/
theorem swift.epochPool_borrow (n : swift.EpN) (v : swift.EpV) (Q : Qp) (γp : GName) (q0 : Qp)
    (L : GMap Nat Qp) :
    swift.epochPool n v Q γp q0 L ⊢
      swift.epochShare n v q0 ∗ (swift.epochShare n v q0 -∗ swift.epochPool n v Q γp q0 L) := by
  unfold swift.epochPool
  iintro ⟨Ha, Hs, Hc⟩
  iframe Hs
  iintro Hs
  iframe

/-- `stopDescs`' ghost step: from the run loop's pool and the shares the stopped goroutines
handed in (one per outstanding loan), the stopped epoch. -/
theorem swift.epochRun_stopped (n : swift.EpN) (v : swift.EpV) (Q : Qp) (γp : GName) (q0 : Qp)
    (L : GMap Nat Qp) :
    swift.epochPool n v Q γp q0 L ∗ ([∗map] _i ↦ q ∈ L, swift.epochShare n v q) ⊢
      swift.epochStopped n v Q :=
  swift.epochPool_stopped n v Q γp q0 L

end laws

end Perennial.github_com.imdea_software.swiftpaxos
