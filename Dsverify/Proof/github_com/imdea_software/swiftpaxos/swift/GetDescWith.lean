/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/GetDescWith.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
**`r.getCmdDescWith(x, msg, seq)`** (swift.go:846; round 24, sv-swb; notes/prove-swift.md §30):
the run loop's lookup-or-create of `x`'s descriptor over the descriptors' state `descDS`
(DescDS.lean), with `ConcurrentMap.UpsertVL` (G1: the callback holds the shard's lock token, so
`key`'s entry is fixed while it reads `desc.seq`/`desc.msgs`).

* `swift.descInv_lendL` / `swift.descInv_returnL`: `descInv_lend`/`descInv_return` (StopRound.lean)
  under the Upsert lock token `cmapLocked` (instead of `IterCb`'s pin): the entry's state is lent
  to the callback (`stopDescs`' borrow token `γb`, whose authority the run loop holds at `0`).
* `swift.descDSN`: `propSpecIN`'s `DS` (HandleProposal.lean): `descDS` at the run loop's names
  with the proposal's `γ N r` the replica's, and the descriptors' context `descCtx`.
-/
/- Round 43 (D52 (4)): split by phase; this module holds `wp_coreD`, `wp_proofDS`, `wp_proofD`
and re-exports GetDescWithDefs/Loan/Ents. -/
module


public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.GetDescWithEnts
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.GetDescWithVocab

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section rch
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF] [SwiftKitDeps]
variable [swift.Assumptions] [replica.Assumptions] [replica.defs.Assumptions] [rpc.Assumptions]
variable [sync.Assumptions] [hook.Assumptions]

end rch

section proof
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF] [SwiftKitDeps]
variable [swift.Assumptions] [replica.Assumptions] [replica.defs.Assumptions] [rpc.Assumptions]
variable [sync.Assumptions] [github_com.orcaman.concurrent_map.Assumptions] [hook.Assumptions]

set_option goose.wp.extras true

/-- **`getCmdDescWith` with a proposal** (`propSpecIN`; round 27: from `wp_coreD`). -/
theorem swift.Replica.getCmdDescWith.wp_proofDS (γ0 : sp.Names) (c_γc c_γm : GName) (x : swift.RunX)
    (wp_Str : swift.CommandId.String.specS x.str) (hinj : Function.Injective x.str)
    (wp_HasV : ∀ dm γdl, swift.cmapHasV.spec dm γdl)
    (wp_Upsert : github_com.orcaman.concurrent_map.ConcurrentMap.UpsertVL.spec (GF := netDistGF))
    (wp_seq : swift.Replica.handleMsg.seqSpecD γ0 c_γc c_γm x)
    (wp_newDesc : ∀ (rp : Loc) (MP : GoInterface → IProp netDistGF), swift.mpTy MP →
      swift.Replica.newDesc.specNc (x.dc γ0 c_γc c_γm rp) (swift.RCh γ0 c_γc c_γm rp) MP)
    (wp_hd : swift.Replica.handleDesc.specD γ0 c_γc c_γm x (swift.RCh γ0 c_γc c_γm)) :
    swift.Replica.getCmdDescWith.propSpecIN (swift.descDSNo γ0 c_γc c_γm x) := by
  intro γ γcl γdl rp pm gp xid c dep hs sq sqb N r b ld s B D P H bw qb
  iintro %Φ ⟨#Hpkg, HDS, Hrdr, Hm, Hnt, Hbal, %Hbw⟩ HΦ
  iunfold swift.descDSNo at HDS
  icases HDS with ⟨HDS, %hγcl⟩
  subst hγcl
  iunfold swift.descDSN at HDS
  icases HDS with ⟨HDS, %Hnames, #Hctx, #HpB, #Hhist⟩
  obtain ⟨hγ, hdl, hN, hr⟩ := Hnames
  subst hγ hdl hN hr
  have hconv : ∀ g : swift.DescG, swift.mpOk x γ c_γc c_γm rp g → g.ev.b = b →
      swift.propMsgR γ pm gp xid c dep hs sq x.N x.r b ld s B D P H ∗
        swift.claimTok x.γcl (b, toCmdId xid) .fresh ⊢
        g.mp xid (interface.mkOk (go.GoType.PointerType swift.proposeMsg.ty) #pm) := by
    intro g hmpOk hb
    have hmp : _ = _ := hmpOk
    rw [hmp]
    iintro ⟨Hm, Hnt⟩
    iunfold swift.descMP
    iright; ileft
    iexists pm, gp, c, dep, hs, sq, ld, s, B, D, P, H
    isplitr
    · ipureintro; rfl
    rw [hb]
    iframe Hm
    iexact Hnt
  iapply (swift.Replica.getCmdDescWith.wp_coreD γ c_γc c_γm x wp_Str hinj wp_HasV wp_Upsert wp_seq
    wp_newDesc wp_hd γ x.γdl rp xid (interface.mkOk (go.GoType.PointerType swift.proposeMsg.ty) #pm) sqb
    x.N x.r b iprop(swift.propMsgR γ pm gp xid c dep hs sq x.N x.r b ld s B D P H ∗
      swift.claimTok x.γcl (b, toCmdId xid) .fresh) bw qb
    (by simp [interface.mkOk]) hconv) $$ [HDS Hrdr Hm Hnt Hbal]
  rotate_left
  · iintro %d
    inext
    iintro ⟨HDS, Hrdr, Hbal⟩
    iapply HΦ
    iframe Hrdr Hbal
    iunfold swift.descDSNo; iframe HDS; ipureintro; rfl
  iframe Hrdr Hm Hnt Hbal
  isplitr [HDS]
  · iexact Hpkg
  isplitl [HDS]
  · iunfold swift.descDSN; iframe HDS Hctx HpB Hhist; ipureintro; exact ⟨rfl, rfl, rfl, rfl⟩
  ipureintro; exact Hbw

/-- `wp_proofDS` at the old binders (round 26; ServersLink's call): the sequential inline call's
spec is still OPEN on the descriptor side (task 3: `handleMsg.seqSpecD` from `handleMsg`'s cases
over the sequential state `g.so`, notes/prove-swift.md §32). -/
theorem swift.Replica.getCmdDescWith.wp_proofD (γ0 : sp.Names) (γc γm : GName) (x : swift.RunX)
    (wp_Str : swift.CommandId.String.specS x.str) (hinj : Function.Injective x.str)
    (wp_HasV : ∀ dm γdl, swift.cmapHasV.spec dm γdl)
    (wp_Upsert : github_com.orcaman.concurrent_map.ConcurrentMap.UpsertVL.spec (GF := netDistGF))
    (wp_newDesc : ∀ (rp : Loc) (MP : GoInterface → IProp netDistGF), swift.mpTy MP →
      swift.Replica.newDesc.specNc (x.dc γ0 γc γm rp) (swift.RCh γ0 γc γm rp) MP)
    -- round 44 (D53 (1)): the linked specs (DescLinked.lean), passed in by ServersLink
    (wp_seq : swift.Replica.handleMsg.seqSpecD γ0 γc γm x)
    (wp_hd : swift.Replica.handleDesc.specD γ0 γc γm x (swift.RCh γ0 γc γm)) :
    swift.Replica.getCmdDescWith.propSpecIN (swift.descDSNo γ0 γc γm x) :=
  swift.Replica.getCmdDescWith.wp_proofDS γ0 γc γm x wp_Str hinj wp_HasV wp_Upsert
    wp_seq
    -- round 39 (D43 (5)): `newDesc` at the replica's records, a hypothesis linked in ServersLink
    -- (`swift.Replica.newDesc.wp_linked`, NewDescLinked.lean)
    wp_newDesc
    wp_hd

end proof


end Perennial.github_com.imdea_software.swiftpaxos
