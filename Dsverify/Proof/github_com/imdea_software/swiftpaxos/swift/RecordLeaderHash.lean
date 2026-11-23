/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/RecordLeaderHash.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
`r.recordLeaderHash(x, s, hs)` (swift.go; the `ackHash` arm's callee, `leaderAckHash`), total
(round 18, sv-swc; notes/prove-swift.md §22):

* `x` has a proposal in `proposes`: `r.updateLogs(p.Command, x, s, hs)` (one `HashLog.Update` per
  key of the command). Its premise `swift.leadUpdOk` (the command is a put or a get, and
  `Update`'s effect keeps `hlogOk` of its key) follows from the leader's numbering (change log
  C22, M3, round 19: `swift.leadUpdOk_of`, from `sp.num_paths`); it is stated per command through
  `cmdIs` (the proposal's `propIs` carries `cmdIs γ x c`).
* `x` has no proposal: `pendingHashUpds[x] = &UpdateEntry{hs, s}` (`swift.pendOwnH`, Local.lean:
  each entry read-only with its hash's path and the leader's number and path of the command, for
  the later `recordLeaderHash` of `handleProposal`).

`swift.Replica.updateLogs.specT` is a hypothesis (its proof: `keysOf` of a put/get is its key,
the `hlog` map's lookup/insert of a fresh `HL.init`, `HashLog.Update.spec`; not done).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.RunSpecs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.DepHashPure
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.RecordLeaderHashDefs

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section mono
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [π : NetProtoGS]
variable [swift.Assumptions]

end mono

section specs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF] [SwiftKitDeps]
variable [swift.Assumptions]

end specs

section ghost
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [π : NetProtoGS] [sp.GobFmt]
variable [swift.Assumptions]

end ghost

section proof
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF] [SwiftKitDeps]
variable [swift.Assumptions]

theorem swift.Replica.recordLeaderHash.wp_proofT
    (wp_upd : swift.Replica.updateLogs.specT (hG := hG)) :
    swift.Replica.recordLeaderHash.specT (hG := hG) := by
  intro γ γc γm γl N fr l rp hm pm pd hM pM pdM hd Λ b x sq hs H P
  haveI := swift.hlog.cmdId_intoValInj (sem := sem)
  wp_start as ⟨#Hinv, #Hcfg, Hhf, Hhlog, #HΛ, Hpf, Hprops, Hpdf, Hpend, #Hhs, #HP, #Hnum, #Hpath⟩
  iunfold swift.propsOwn at Hprops
  icases Hprops with ⟨Hpm, Hpents⟩
  wp_auto
  wp_apply wp_map_lookup2 $$ [$Hpm] as Hpm
  cases hx : pM !! x with
  | none =>
    try simp only [hx]
    wp_if_destruct
    · simp_all
    · -- no proposal: the update waits in `pendingHashUpds`
      iunfold swift.pendOwnH at Hpend
      icases Hpend with ⟨Hpdm, Hpdents⟩
      irename «$r0» => Hu
      ipersist Hu
      wp_apply wp_mapInsert $$ [$Hpdm] as Hpdm
      iapply HΦ

      iframe Hhf Hhlog HΛ Hpf Hpdf
      isplitl [Hpm Hpents]
      · iunfold swift.propsOwn; iframe
      isplitl
      · iunfold swift.pendOwnH
        iframe
        iapply (BigSepM.bigSepM_insert_elim (Φ := fun (x : swift.CommandId) (u : Loc) =>
          iprop(∃ (sl : GoSlice) (sq : w64) (H : swift.SHash) (P : List sp.CmdId),
            u ↦□ swift.UpdateEntry.mk sl sq ∗ sl ↦*□ [H] ∗ sp.startHash P H.H'.arr ∗
            sp.numIs γ (sp.leaderOf N b) b (toCmdId x) sq ∗
            sp.pathIs γ (sp.leaderOf N b) b (toCmdId x) P)))
        · iexists hs, sq, H, P; iframe #
        · iexact Hpdents
      ipureintro; simp
  | some gp =>
    try simp only [hx]
    wp_if_destruct
    rotate_left
    · simp_all
    ihave ⟨Hgp, Hclose⟩ := BigSepM.bigSepM_lookup_acc
      (show Iris.Std.PartialMap.get? pM x = some gp from hx) $$ Hpents
    icases Hgp with ⟨%c, #Hpi⟩
    ihave #Hpi2 := Hpi
    iunfold swift.propIs at Hpi2
    icases Hpi2 with ⟨%p, %w, %mu, %addr, %ts, %vs, #Hgp, #Hp, #Hvs, #Hc, %Hwf⟩
    iStructNamed Hgp
    iStructNamed Hp
    -- the leader's numbering (change log C22): `Λ` grows by the acknowledgement
    iapply fupd_wp
    ihave Hcok := sp.cmdIs_ok (γ := γ) (γc := γc) (γm := γm) (γl := γl) (toCmdId x) c $$ [Hinv Hc]
    · iframe Hinv Hc
    imod (fupd_mask_mono (E1 := ↑sp.spN) (E2 := ⊤) (by simp)) $$ Hcok with %Hcok
    have hK : swift.propsK pM (toCmdId x) := by
      unfold swift.propsK
      rw [show ofCmdId (toCmdId x) = x from rfl, hx]; rfl
    imod swift.leadUpd_ghost ⊤ (by simp) γ γc γm γl N fr l b Λ (toCmdId x) c sq H.H'.arr P hd
        (swift.propsK pM) hK Hcok.1 $$ [Hinv Hcfg HΛ Hnum Hpath Hc] with ⟨#HΛ', %Hlu⟩
    · iframe Hinv Hcfg HΛ Hnum Hpath Hc
    imodintro
    ihave Hhlog := swift.hlogOwn_mono hm hM false hd (K' := swift.propsK pM)
      (Λ' := swift.ΛAdd Λ c.key sq P) (fun _ h => h) (fun _ _ _ h => Or.inl h) $$ Hhlog
    simp only [Option.getD_some]
    wp_auto
    wp_apply wp_upd rp hm hM false hd (swift.propsK pM) (swift.ΛAdd Λ c.key sq P) c vs
        DFrac.discard x sq hs H P $$ [$Hhf $Hhlog]
      as %hM' ⟨Hhf, Hhlog, -⟩
    · iframe #; ipureintro; exact Hlu
    iapply HΦ
    iframe
    iframe HΛ'
    isplitl [Hpm Hclose]
    · iunfold swift.propsOwn
      iframe
      iapply Hclose
      iexists c; iexact Hpi
    ipureintro; intro; rfl

end proof

end Perennial.github_com.imdea_software.swiftpaxos
