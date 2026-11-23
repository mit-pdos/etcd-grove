/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/SyncEntryTok.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
**A sync entry's row token at a descriptor** (round 29, sv-swb; notes/prove-swift.md §35): the
ghost core of `handleSyncEntry` (recovery.go:700). The entry carries `takeSync_stepD`'s token for
`x`'s row of the new ballot `b`, at `swift.rvSync` (accepted, not pre-accepted, no path, not
committed), and the replica's `sp.accepted` fact (`getCmdDesc.syncSpecI`'s payload). At the
descriptor:

* a token already there is refuted (two tokens of one row);
* G10's disjunct of the stored closures (`∃ D, sp.preacc c.γ c.r b x D`: the leader's own ack of
  `b` stored at a tokenless incarnation) is refuted by `preacc_row` exactly as `install_tok`
  does with `handle_stepD`'s fresh token: `rvSync.1 = none` (the sync row is accepted but not
  pre-accepted), so `swift.stored_ok2T` applies (`hrv := rfl`). This is the "other refutation"
  §34 asked for: none is needed beyond `rvSync.1 = none`;
* `handleSyncEntry` writes `phase = COMMIT` with a non-nil `propose`; L2 (notes/prove-s2-g.md):
  the commit step (`commit_dstep'`, justified by the entry's `sp.accepted`) is no longer done
  here but at `ghostCommit`'s resolution after the write (HandleSyncEntry.lean): the row is
  returned at `swift.rvSync`.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.FastAckDefs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.DepEqualsPerm
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.SyncStepD

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

/-- **The sync entry's token installed and committed** (see the file header). -/
theorem swift.install_sync (c : swift.DC) (RC : Loc → w32 → IProp netDistGF)
    (MP : GoInterface → IProp netDistGF) (γd : ChanNames) (d : Loc) (x : swift.CommandId)
    (b : Nat) (Do : IProp netDistGF) (dv : swift.DescV) (rv0 : swift.RowV) (qe : Qp) (bw : w32)
    (stp rcp : Loc) (fs : List GoFunc) :
    c.ctx ∗ swift.takeLaw c ∗ c.env d qe ∗
      swift.epochRd c.γe c.γxe c.rp c.rr qe b bw stp rcp ∗ swift.rowTokO c b x dv rv0 ∗
      ([∗list] g ∈ fs, swift.storedOk c RC MP γd d x b Do g) ∗
      swift.claimTok c.γcl (b, toCmdId x) .sync ∗ sp.accepted c.γ c.r b (toCmdId x) ⊢
    |={⊤}=> swift.epochRd c.γe c.γxe c.rp c.rr qe b bw stp rcp ∗ c.env d qe ∗
      swift.rowTok c.γo b (toCmdId x) swift.rvSync ∗ swift.slotT c (b, toCmdId x) ∗
      swift.syncIn c.γ b (toCmdId x) ∗
      [∗list] g ∈ fs, swift.storedOk2 c RC MP γd d x b Do g := by
  iintro ⟨#Hctx, #Htl, Henv, Hrd, Htok, #Hfs, Hcl, #Hacc⟩
  ihave #Hctx2 := Hctx
  iunfold swift.DC.ctx at Hctx2
  iunfold swift.descCtxE at Hctx2
  icases Hctx2 with ⟨%me, %fr, %lg, %dm, %dc, %ex, %dr, %oe, %γa, %γrm, %rc, %γrc, -, -, %Hids, -, -, -,
    #Hinv, #Hcfg, #Hninv, -⟩
  obtain ⟨-, -, hrN, -, -, hk⟩ := Hids
  iunfold swift.epochRd at Hrd
  icases Hrd with ⟨Hbal, HStf, Hrcf, Het, Hxe, %Hbw⟩
  iunfold swift.rowTokO at Htok
  icases Htok with (⟨Htok, -⟩ | ⟨%Hn, -, Hslt⟩)
  · -- a token already there: the claim's token is in the store (refuted)
    imod (swift.claim_tok_false c (b, toCmdId x) .sync rv0) $$ [Hcl Htok] with Hf
    · iframe Hctx Hcl Htok
    iexfalso; iexact Hf
  -- T24 (table rev 6, G-slot): the token out of the store, the slot holding its receipt
  iunfold swift.takeLaw at Htl
  ihave Htk := Htl $$ %d %qe %(b, toCmdId x) %swift.ClK.sync Henv Hslt Hcl
  imod Htk with ⟨%rvt, Hnt, Hw, Henv, Hslt⟩
  ihave ⟨%Hrvt, #Hsy⟩ := swift.retWhy_sync c.γ c.γxm c.γcg c.str c.N c.r (b, toCmdId x) rvt $$ Hw
  subst Hrvt
  imod (swift.stored_ok2T c RC MP γd d x b Do fr lg qe swift.rvSync rfl hrN hk fs)
    $$ [Het Hnt] with ⟨Het, Hnt, #Hfs2⟩
  · iframe Hinv Hcfg Hninv Het Hnt Hfs
  -- L2: the commit is at `ghostCommit`'s resolution (the caller)
  imodintro
  iframe Hfs2 Henv Hslt Hsy Hnt
  iunfold swift.epochRd; iframe Hbal HStf Hrcf Het Hxe; ipureintro; exact Hbw

end lemmas

end Perennial.github_com.imdea_software.swiftpaxos
