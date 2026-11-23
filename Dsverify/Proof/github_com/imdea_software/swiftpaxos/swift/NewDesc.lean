/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/NewDesc.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
`r.newDesc()` (swift.go:895; round 22, sv-swb; notes/prove-swift.md §28): a descriptor from
`allocDesc` (at rest: `descPooled (descDFA γsh)`) with every field `newDesc` writes at its new
value (`swift.descNew`): `dep`/`hs`/`storedBallots`/`propose`/`proposeDep`/`waitingAck` nil
(P12), `phase = START`, `active`, `slowPath = false`, `seq` some `s`, a no-op `defered`, fresh
`msgs`/`stopChan` channels with the caller's bags (`MP`, `SP d sc`), `afterPropagate` an
`OptCondF` with an empty store and the condition `desc.propose != nil` (`condOk … proposeHalf`),
the two message sets (slow over `SQ`, fast over `FQ`) with one handler `hd` (`acksHdOk`: its
spec at any frame, so the spawn states the sets' lent states, which mention each other).
`successors` is reset under `successorsL` (its mutex is kept by the share map's invariant and
by the descriptor at rest). The share map's element whole, `cmd` as at rest.

The accept closure reads both acks' `Dep` slices: `ackP`/`leadAckP` carry them read-only
(SWB-16, D18; round 23): `acceptOk` over `Dep.Equals.specAnyV`.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.AllocDescDefs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.AcksSpecs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.RunCtx
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.DepEqualsVDefs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.NewDescDefs

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section defs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF] [SwiftKitDeps]
variable [swift.Assumptions] [hook.Assumptions]

end defs

section split
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF] [SwiftKitDeps]
variable [swift.Assumptions] [hook.Assumptions]

end split

section specs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF] [SwiftKitDeps]
variable [swift.Assumptions] [hook.Assumptions]

end specs

section proofs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF] [SwiftKitDeps]
variable [swift.Assumptions] [hook.Assumptions] [replica.Assumptions] [sync.Assumptions]

set_option goose.wp.extras true

/-- `newDesc` at one record `c` (round 39, D43 (5)), from the handler's spec at `c`. -/
theorem swift.Replica.newDesc.wp_proofc (c : swift.DC) (RC : Loc → w32 → IProp netDistGF)
    (MP : GoInterface → IProp netDistGF)
    (wp_alloc : swift.Replica.allocDesc.specA (hG := hG))
    (wp_hd : swift.getFastAndSlowAcksHandler.specIc c RC MP)
    (wp_RCF : hook.ocf.OptCondF.ReinitCondF.specI (hG := hG))
    (wp_RMS : replica.mset.MsgSet.ReinitMsgSet.specD (hG := hG))
    (wp_eqV : swift.Dep.Equals.specAnyV (hG := hG)) :
    swift.Replica.newDesc.specNc c RC MP := by
  intro SP γsh x b dm γdl γn D sq fq szS szF memS memF qf
  wp_start as ⟨#Hctx, #Hpool, #Hsh, #HcntL, #HD, #HSQ, #HqS, HFQ, #HqF⟩
  wp_auto
  wp_apply wp_alloc $$ [$Hpool $Hsh] as %d Hd
  iunfold swift.descPooled at Hd
  icases Hd with ⟨%m0, %s0, %sl0, %fa0, Hm0, Hs0, Hsl0, Hfa0, Hsl0a, Hfa0a, Hdf⟩
  simp only [swift.descDFA]
  iunfold swift.descDF at Hdf
  icases Hdf with ⟨%a0, %q0, Ha0, Hq0, -, Hr⟩
  iunfold swift.descRestA at Hr
  icases Hr with ⟨%qs, %ph, %sn, %cc, %vs, %dep, %hs, %pd, %sb, %p, %ap, %wa, %slw, %df, He, #Hmx, Hph,
    Hcmd, #Hvs, %Hop, Hdep, Hhs, Hsn, Hp, Hpd, Hap, Hapa, Hslw, Hdfr, Hwa, Hsb⟩
  wp_auto
  wp_apply chan.wp_make2 (V := GoInterface) (W64 8) as %mc %γm ⟨#Hmc, %Hmcap, Hmown⟩
  · ipureintro; decide
  try wp_auto
  wp_apply sync.Mutex.wp_Lock $$ [$Hmx] as ⟨Hlk, HS⟩
  iunfold swift.succInv at HS
  icases HS with ⟨%ssl, %sll, Hsucc, -, -⟩
  try wp_auto
  wp_apply sync.Mutex.wp_Unlock $$ [$Hmx $Hlk Hsucc]
  · iunfold swift.succInv
    iexists slice.nil, []
    iframe Hsucc
    isplitr
    · iapply (ownSlice_nil (V := swift.CommandId) (DFrac.own 1))
    · iapply ownSliceCap_nil
  try wp_auto
  wp_apply sync.Mutex.wp_Lock $$ [$HcntL] as ⟨Hclk, HC⟩
  iunfold swift.cntLInvR at HC
  icases HC with ⟨%n, %cnt, %T, Hn, Hcnt, HG⟩
  try wp_auto
  wp_apply sync.Mutex.wp_Unlock $$ [$HcntL $Hclk Hn Hcnt HG]
  · iunfold swift.cntLInvR
    iexists n, cnt, T
    iframe Hn Hcnt HG
  try wp_auto
  wp_apply chan.wp_make2 (V := Loc) (W64 8) as %sc %γs ⟨#Hsc, %Hsccap, Hsown⟩
  · ipureintro; decide
  iapply fupd_wp
  imod start_bag MP (ChanState.Buffered []) mc γm (by trivial) $$ [$Hmc] [Hmown] with #Hbm
  · iexact Hmown
  imod start_bag (SP d sc) (ChanState.Buffered []) sc γs (by trivial) $$ [$Hsc] [Hsown] with #Hbs
  · iexact Hsown
  imodintro
  try wp_auto
  ipersist desc
  ihave ⟨%cond0, %fs0, Hocf0⟩ := swift.ocfAny_ex $$ Hapa
  wp_apply wp_RCF $$ [Hocf0] as %cf Hocf
  · iframe Hocf0
  try wp_auto
  ipersist acceptFastAndSlowAck
  ipersist freeFastAck
  wp_apply (wp_hd γm d x b) $$ [$Hctx] as %hd #Hhd
  try wp_auto
  iunfold swift.msetAny at Hsl0a
  wp_apply (wp_RMS sl0 sq szS memS (swift.ackP x) swift.ackA (swift.leadAckP c b x) iprop(True))
    $$ [Hsl0a] as %sl Hsl
  · iframe Hsl0a HqS
    isplitr
    · acceptProof
    · iunfold replica.mset.freeOk; imodintro; iintro %m; imodintro
      iintro %Ψ ⟨HR, -⟩ HΨ; wp_auto; iapply HΨ; iexact HR
  try wp_auto
  iunfold swift.msetAny at Hfa0a
  wp_apply (wp_RMS fa0 fq szF memF (swift.ackP x) swift.ackA (swift.leadAckP c b x) iprop(True))
    $$ [Hfa0a] as %fa Hfa
  · iframe Hfa0a HqF
    isplitr
    · acceptProof
    · iunfold replica.mset.freeOk; imodintro; iintro %m; imodintro
      iintro %Ψ ⟨HR, -⟩ HΨ; wp_auto; iapply HΨ; iexact HR
  iapply HΦ
  iframe HFQ
  iunfold swift.descNew
  iexists _, γm, γs, mc, sc, cf, sl, fa, _, _, hd, qs, cc, vs, _
  iframe He Hmx Hcmd Hvs Hdep Hhs Hsn Hm0 Hbm Ha0 Hph Hslw Hq0 Hdfr Hsb Hp Hpd Hwa Hs0 Hbs Hap Hocf
  iframe Hsl0 Hfa0 Hsl Hfa Hhd
  isplitr
  · ipureintro; exact Hop
  isplitr
  · iunfold swift.nopOk; imodintro; iintro %P; imodintro
    iintro %Ψ HP HΨ; wp_auto; iapply HΨ; iexact HP
  iunfold hook.ocf.condOk; imodintro; iintro %v; imodintro
  iintro %Ψ Hph HΨ
  iunfold swift.proposeHalf at Hph
  icases Hph with ⟨%pp, Hpp, %Hv⟩
  wp_auto
  have hv : (!decide (pp = null)) = v := by rw [← Hv]; by_cases h : pp = null <;> simp [h]
  rw [hv]
  iapply HΨ
  iunfold swift.proposeHalf
  iexists pp; iframe Hpp; ipureintro; exact Hv

theorem swift.Replica.newDesc.wp_proof (RC : Loc → w32 → IProp netDistGF)
    (MP : GoInterface → IProp netDistGF)
    (wp_alloc : swift.Replica.allocDesc.specA (hG := hG))
    (wp_hd : swift.getFastAndSlowAcksHandler.specI RC MP)
    (wp_RCF : hook.ocf.OptCondF.ReinitCondF.specI (hG := hG))
    (wp_RMS : replica.mset.MsgSet.ReinitMsgSet.specD (hG := hG))
    (wp_eqV : swift.Dep.Equals.specAnyV (hG := hG)) :
    swift.Replica.newDesc.specN RC MP := fun c =>
  swift.Replica.newDesc.wp_proofc c RC MP wp_alloc (wp_hd c) wp_RCF wp_RMS wp_eqV
