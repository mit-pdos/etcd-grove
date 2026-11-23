/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swiftnet/ServersLink.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
`ServersOk`, linked: `servers_ok_of` (Proof/swiftnet/Servers.lean) applied to the callees'
results. The callees in other packages are not proved on this branch: each is a `sorry`
marked with its owner below (to be replaced by the owner's linked theorem when it lands).
The codec's law is `kitCodecOkC_holds` (Proof/swiftnet/KitLike.lean, decision D6: at the codec
`kitCodecC`; the frozen `kitCodecOk_holds` and its HUB-REQUEST 2 gap are not used).
`kitNameOk_holds` is not used: the registrations use `nameOkFor` at their receivers
(Proof/swiftnet/NameOkFor.lean, Proof/net/rpc/LocalRegister.lean).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.Servers
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.SrvInit
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.master.Link
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.dlog.Link
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.replica.defs.Link
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.registerRPC
public import Dsverify.Proof.encoding.gob.SetCodec
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.codec.CodecFns
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.Link
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.HookUser1
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.RunLoop
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.RunAlloc
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.RunArmsRL
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.UpdateLogs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.RunArmAck
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.RunArmRec
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.RunArmReinit
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.RunArmSync
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.NewLeaderProof
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.NewLeaderDesc
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.SyncLinkD
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.RunArmsDesc
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.DrainRechecks
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.HandleProposalProof
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.NewDescLink
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.DescLink
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.DepHash
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.CmdStr
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.TableAllocH
public import Dsverify.Proof.encoding.gob.Decoder__Decode
public import Dsverify.Proof.encoding.gob.NewDecoder
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.replica.ConnLink

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

-- The codec of the linked results (decision D6, HUB-REQUEST 2, Proof/swiftnet/KitLike.lean):
-- `kitCodecC`, whose `kitCodecOk` holds (`kitCodecOkC_holds`).
attribute [local instance 2000] examples.swiftnet.kitCodecC

section initSrv
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics]
variable [examples.swiftnet.Assumptions] [net.FieldAssumptions]

/-- The server-side initialization (change log C14, decision D9): the test package's first
initialization hands the boot thread the mutable globals on a replica node
(`adapter.swiftnetInitSrv_first`, Proof/swiftnet/SrvInit.lean). -/
theorem swiftnetInitSrv_proof :
    letI := @pkgStates _ netDistGF hG sem
    swiftnetInitSrv.spec :=
  adapter.swiftnetInitSrv_first

end initSrv

section link
variable [GoGlobalContext] [G : GooseGlobalGS .hasLC netDistGF] [π : NetProtoGS]

/-- The package states' facts `swift.New` uses, from `pkgStates`. -/
theorem srv_pkg_facts (hG : HeapGS .hasLC netDistGF) (s : go.Semantics) :
    letI := @pkgStates _ netDistGF hG s
    swift.SrvPkgFacts (hG := hG) := by
  letI := @pkgStates _ netDistGF hG s
  refine ⟨?_, ?_⟩
  · have h : isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.replica ⊢ replica.pkgSt := by
      with_unfolding_all exact isPkgInit_access (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.replica
    refine h.trans ?_
    unfold replica.pkgSt
    exact .rfl
  · have h : isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.replica.defs ⊢ defs.pkgSt := by
      with_unfolding_all exact isPkgInit_access (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.replica.defs
    refine h.trans ?_
    unfold defs.pkgSt
    exact .rfl

/-- `errVarintOverflow` (`swift.pkgSt`) on a server node. -/
theorem srv_errvarint_fact (hG : HeapGS .hasLC netDistGF) (s : go.Semantics) :
    letI := @pkgStates _ netDistGF hG s
    swift.ErrVarintFact (hG := hG) := by
  letI := @pkgStates _ netDistGF hG s
  have h : isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.swift ⊢ swift.pkgSt := by
    with_unfolding_all exact isPkgInit_access (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.swift
  refine h.trans ?_
  unfold swift.pkgSt
  iintro ⟨-, -, -, #He, -⟩
  iexact He

/-- The fast-ack pool (`swift.pkgSt`) on a server node. -/
theorem srv_pool_fact (hG : HeapGS .hasLC netDistGF) (s : go.Semantics) :
    letI := @pkgStates _ netDistGF hG s
    swift.FastAckPoolFact (hG := hG) := by
  letI := @pkgStates _ netDistGF hG s
  have h : isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.swift ⊢ swift.pkgSt := by
    with_unfolding_all exact isPkgInit_access (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.swift
  refine h.trans ?_
  unfold swift.pkgSt
  iintro ⟨-, -, -, -, #Hp, -⟩
  iexact Hp

/-- The hooks are nil (`swift.pkgSt`) on a server node: `runInv_alloc`'s `swift.HooksFact`. -/
theorem srv_hooks_fact (hG : HeapGS .hasLC netDistGF) (s : go.Semantics) :
    letI := @pkgStates _ netDistGF hG s
    swift.HooksFact (hG := hG) := by
  letI := @pkgStates _ netDistGF hG s
  have h : isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.swift ⊢ swift.pkgSt := by
    with_unfolding_all exact isPkgInit_access (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.swift
  unfold swift.HooksFact
  refine h.trans ?_
  unfold swift.pkgSt
  iintro ⟨#H1, #H2, -⟩
  iframe H1 H2

/-- L2's claim of a predicted node's ghost (`client.claimGhost.spec`, Spec/client/NodeGhost.lean,
group E's), at every node's heap, Go assumptions (the `sync` package's, which the claim's
`init_Mutex` needs) and the run's package states: a hypothesis here (proved: `claim_hyp`,
ClaimLink.lean). -/
def ClaimHyp [GoGlobalContext] : Prop :=
  ∀ (hG : HeapGS .hasLC netDistGF) (s : go.Semantics) [examples.swiftnet.Assumptions],
    letI := @pkgStates _ netDistGF hG s
    client.claimGhost.spec (hG := hG) (sem := s)

/-- The server nodes' callee specs. -/
theorem servers_hyps (hclaim : ClaimHyp) : ServersHyps := by
  intro hG s _ _ _ _
  letI := @pkgStates _ netDistGF hG s
  refine ⟨?init, hclaim hG s, ?reg, ?mnew, ?mrun, ?max, ?snew, kitCodecOkC_holds⟩
  case init => exact swiftnetInitSrv_proof
  case reg =>
    exact registerRPC.wp_proof net.rpc.SetCodec.wp_proof (encoding.gob.SetCodec.wp_proof rfl)
  case mnew => exact master.wp_New
  case mrun =>
    exact master.Master.wp_Run' dlog.Logger.wp_Printf dlog.Logger.wp_Fatal
      replica.defs.wp_NewBeTheLeaderReply
      examples.swiftnet.rpcDecodeAs_defs_RegisterArgs.wp_proof
      examples.swiftnet.rpcDecodeAs_defs_GetReplicaListArgs.wp_proof
      examples.swiftnet.rpcDecodeAs_defs_GetLeaderArgs.wp_proof
      examples.swiftnet.rpcPutU64.specNil.wp_proof
      examples.swiftnet.rpcEnc_defs_RegisterReply.wp_proof
      examples.swiftnet.rpcEnc_defs_GetReplicaListReply.wp_proof
      examples.swiftnet.rpcEnc_defs_GetLeaderReply.wp_proof
  case max =>
    -- the swift group's (Proof/swift/Link.lean), proved (D9/C14: the globals come from the first
    -- package initialization; HUB-REQUEST SW1 closed, D45 (4))
    exact setMaxDesc.wp_proof
  case snew =>
    -- round 46 (D-SWC2-6): the reply channel's `reply.specI` sorry (request SWC-2) is gone:
    -- `deliver.specE` (DeliverE.lean) is linked over the proved `reply.wp_proofE` (ReplyChan.lean)
    -- round 44 (sv-swb, D53 (1)): the descriptor links' callees (DescLink.lean)
    have hDL : swift.DescLinkH := ⟨swift.newFastAck.wp_proofP (srv_pool_fact hG s),
      swift.copyFastAck.wp_proofP (swift.newFastAck.wp_proofP (srv_pool_fact hG s))⟩
    -- the swift group's (Proof/swift/Link.lean): `swift.New`'s body is proved; its callees
    -- still open are marked (notes/prove-swift.md §10)
    exact swift.wp_New (srv_pkg_facts hG s)
      (swift.wp_NewBatcher
        swift.wp_clientChecksum
        (swift.releaseFastAck.wp_proof (srv_pool_fact hG s))
        (swift.wp_MOptAcks_marshal)
        (swift.wp_MAcks_marshal)
        (swift.wp_MFastAckClient_marshal)
        swift.wp_MLightSlowAck_marshal)
      (swift.wp_NewReplyChan
        swift.wp_clientChecksum
        (swift.wp_MReply_marshal))
      hook.HookUser1.wp_proof
      (swift.Replica.run.wp_proof'
        -- `swift.RunLoopOk` from the allocation (`swift.runInv_alloc`, proved) and the arms
        (swift.runLoopOk_of
          -- (`runInv_alloc` allocates at `str := swift.cmdStr`, `CommandId.String`'s function,
          -- CmdStr.lean; `runInv` records it)
          (srv_hooks_fact hG s)
          -- the arms over `swift.runInv` (round 18: `leader` proved; `propose` linked over
          -- `handleProposal.wp_proof` with two open callee specs; notes/prove-swift.md §27)
          (fun rp γ γc γm x =>
            { recBal := fun nb =>
                -- round 25: `recoveryBallot` over its callees' specs (QuorumOk.lean, AliveQuorum.lean)
                swift.runArm_recBal replica.wp_MaxBallot
                  (replica.QuorumSystem.SameHigherOk.wp_proof replica.wp_Leader replica.wp_MaxBallot)
                  (replica.NextBallotOfOk.wp_proof replica.wp_MaxBallot replica.wp_NextBallotOf)
                  (swift.Replica.aliveQuorumBallot.wp_proof replica.QuorumSystem.wp_NumAQ
                    replica.QuorumSystem.wp_AQ
                    (replica.NextBallotOfOk.wp_proof replica.wp_MaxBallot replica.wp_NextBallotOf))
                  rp γ γc γm x nb
              -- round 31: `reinitNewLeaderAckNs` (RunArmReinit.lean; the set `swift.nlSet` in
              -- `runFields`, its handler's spec stated by `handleNewLeaderAckN`'s caller)
              reinit := fun b => swift.runArm_reinit replica.wp_NewMajorityOf
                replica.mset.MsgSet.ReinitMsgSet.wp_proofD rp γ γc γm x b
              -- round N1 (Phase 4, sv-swc): `handleNewLeader` (NewLeaderProof.lean) over its callees;
              -- round N2: `fillNewLeaderAckN` over the descriptor side's N1-R1/N1-R2 (named
              -- sorries here); the committed descriptors' `getCmdDesc` is the sync arm's (round 47);
              -- round N3: the ack set's handler (`handleNewLeaderAckNs` at the descriptors' state)
              newLeader := fun l r b => swift.runArm_newLeader rp γ γc γm x
                (swift.Replica.handleNewLeader.wp_proofN rp γ γc γm x time.wp_Now
                  (swift.Replica.fillNewLeaderAckN.wp_proofN rp γ γc γm x
                    -- round 49 (sv-swb): the descriptor side's N1-R1/N1-R2 (NewLeaderDesc.lean)
                    (swift.n1r1 rp γ γc γm x) (swift.n1r2 rp γ γc γm x)
                    -- round N4: the walk's callees
                    github_com.orcaman.concurrent_map.ConcurrentMap.IterCbVN.wp_proof
                    github_com.orcaman.concurrent_map.ConcurrentMap.wp_GetV swift.wp_cmapHasV
                    swift.CommandId.String.wp_proof slices.SortFunc.wp_proofOn)
                  (swift.Replica.handleNewLeaderAckN.wp_proofN rp γ γc γm x
                    replica.mset.MsgSet.Add.wp_proofQ
                    -- round N3: the set's handler, `handleNewLeaderAckNs` at the descriptors' state
                    (swift.Replica.wp_handleNewLeaderAckNsD γ γc γm rp x
                      (swift.wp_NewReplyChan swift.wp_clientChecksum swift.wp_MReply_marshal)
                      (swift.Replica.getCmdDesc.syncSpecD γ γc γm x rp
                        (fun hstr => swift.Replica.getCmdDescWith.wp_coreD γ γc γm x
                          (by rw [hstr]; exact swift.CommandId.String.wp_proof)
                          (by rw [hstr]; exact swift.cmdStr_inj) swift.wp_cmapHasV
                          github_com.orcaman.concurrent_map.ConcurrentMap.wp_UpsertVL
                          (swift.Replica.handleMsg.seqSpecD.wp_linked γ γc γm x hstr hDL)
                          (swift.Replica.newDesc.wp_linked x γ γc γm hstr)
                          (swift.Replica.handleDesc.wp_linked γ γc γm x hstr hDL)))
                      (swift.MSync.marshal_proofG encoding.gob.NewEncoder.wp_proof
                        (encoding.gob.Encoder.EncodeW.wp_proof (encoding.gob.getCodec.wp_proof rfl))
                        kitCodecOkC_holds)))
                  (swift.Replica.wp_handleSyncD γ γc γm rp x
                    (swift.wp_NewReplyChan swift.wp_clientChecksum swift.wp_MReply_marshal)
                    -- round 47 (sv-swb, task 3): the sync entries' `getCmdDesc` (DescArms.lean)
                    (swift.Replica.getCmdDesc.syncSpecD γ γc γm x rp
                      (fun hstr => swift.Replica.getCmdDescWith.wp_coreD γ γc γm x
                        (by rw [hstr]; exact swift.CommandId.String.wp_proof)
                        (by rw [hstr]; exact swift.cmdStr_inj) swift.wp_cmapHasV
                        github_com.orcaman.concurrent_map.ConcurrentMap.wp_UpsertVL
                        (swift.Replica.handleMsg.seqSpecD.wp_linked γ γc γm x hstr hDL)
                        (swift.Replica.newDesc.wp_linked x γ γc γm hstr)
                        (swift.Replica.handleDesc.wp_linked γ γc γm x hstr hDL))))
                  replica.Sender.wp_SendTo swift.MNewLeaderAckN.marshal_proof) l r b
              -- round 25: the descriptor side's arms (DescArms.lean) over `wp_coreD` at
              -- `x.str = cmdStr` (D22 (1), `runInv_str`)
              getDesc := fun xid s => swift.runArm_getDescS rp γ γc γm x
                (fun hstr => swift.Replica.getCmdDescWith.wp_coreD γ γc γm x
                  (by rw [hstr]; exact swift.CommandId.String.wp_proof)
                  (by rw [hstr]; exact swift.cmdStr_inj) swift.wp_cmapHasV
                  github_com.orcaman.concurrent_map.ConcurrentMap.wp_UpsertVL
                  (swift.Replica.handleMsg.seqSpecD.wp_linked γ γc γm x hstr hDL)
                  (swift.Replica.newDesc.wp_linked x γ γc γm hstr)
                  (swift.Replica.handleDesc.wp_linked γ γc γm x hstr hDL)) xid s
              propose := fun gp => swift.runArm_propose rp γ γc γm x
                (fun hstr => swift.Replica.handleProposal.wp_proofN swift.CommandId.String.wp_proofI
                  swift.wp_cmapHasV swift.Replica.wp_getDepAndHashes
                  -- round 19 (C22/M3 applied): the total `recordLeaderHash`, proved
                  swift.Replica.wp_recordLeaderHash
                  _
                  -- round 25 (D22 (1)): `runInv` records `x.str = swift.cmdStr`; the descriptor
                  -- side's `getCmdDescWith.wp_proofD` (its own OPEN cases inside)
                  (swift.Replica.getCmdDescWith.wp_proofD γ γc γm x
                    (by rw [hstr]; exact swift.CommandId.String.wp_proof)
                    (by rw [hstr]; exact swift.cmdStr_inj)
                    swift.wp_cmapHasV
                    github_com.orcaman.concurrent_map.ConcurrentMap.wp_UpsertVL
                    (swift.Replica.newDesc.wp_linked x γ γc γm hstr)
                    (swift.Replica.handleMsg.seqSpecD.wp_linked γ γc γm x hstr hDL)
                    (swift.Replica.handleDesc.wp_linked γ γc γm x hstr hDL))
                  replica.wp_Leader dlog.Logger.wp_Fatal) gp
              leader := swift.runArm_leader replica.wp_Leader rp γ γc γm x
              -- round 25: `leaderAckHash` → `recordLeaderHash.specT` (C22/M3; witness `runAckW_lead`)
              ackHash := fun l fa f => swift.runArm_ackHash replica.wp_Leader
                swift.Replica.wp_recordLeaderHash rp γ γc γm x l fa f
              fastDesc := fun l fa f sq => swift.runArm_fastDescS rp γ γc γm x
                (fun hstr => swift.Replica.getCmdDescWith.wp_coreD γ γc γm x
                  (by rw [hstr]; exact swift.CommandId.String.wp_proof)
                  (by rw [hstr]; exact swift.cmdStr_inj) swift.wp_cmapHasV
                  github_com.orcaman.concurrent_map.ConcurrentMap.wp_UpsertVL
                  (swift.Replica.handleMsg.seqSpecD.wp_linked γ γc γm x hstr hDL)
                  (swift.Replica.newDesc.wp_linked x γ γc γm hstr)
                  (swift.Replica.handleDesc.wp_linked γ γc γm x hstr hDL)) l fa f sq
              slowDesc := fun l sa sl => swift.runArm_slowDescS rp γ γc γm x
                (fun hstr => swift.Replica.getCmdDescWith.wp_coreD γ γc γm x
                  (by rw [hstr]; exact swift.CommandId.String.wp_proof)
                  (by rw [hstr]; exact swift.cmdStr_inj) swift.wp_cmapHasV
                  github_com.orcaman.concurrent_map.ConcurrentMap.wp_UpsertVL
                  (swift.Replica.handleMsg.seqSpecD.wp_linked γ γc γm x hstr hDL)
                  (swift.Replica.newDesc.wp_linked x γ γc γm hstr)
                  (swift.Replica.handleDesc.wp_linked γ γc γm x hstr hDL)) l sa sl
              -- round 33: `handleSync` over `runInv` (RunArmSync.lean) from SyncLinkD's
              -- `wp_handleSyncD` (`specI = specIR`, SW4 step 2)
              sync := fun l m => swift.runArm_sync rp γ γc γm x
                (swift.Replica.wp_handleSyncD γ γc γm rp x
                  (swift.wp_NewReplyChan swift.wp_clientChecksum swift.wp_MReply_marshal)
                  -- round 47 (sv-swb, task 3): a committed command's descriptor (`*syncEntry`)
                  (swift.Replica.getCmdDesc.syncSpecD γ γc γm x rp
                    (fun hstr => swift.Replica.getCmdDescWith.wp_coreD γ γc γm x
                      (by rw [hstr]; exact swift.CommandId.String.wp_proof)
                      (by rw [hstr]; exact swift.cmdStr_inj) swift.wp_cmapHasV
                      github_com.orcaman.concurrent_map.ConcurrentMap.wp_UpsertVL
                      (swift.Replica.handleMsg.seqSpecD.wp_linked γ γc γm x hstr hDL)
                      (swift.Replica.newDesc.wp_linked x γ γc γm hstr)
                      (swift.Replica.handleDesc.wp_linked γ γc γm x hstr hDL)))) l m
              -- N2-loop: `drainRechecks` (DrainRechecks.lean) over the recheck arm
              drain := swift.runArm_drain rp γ γc γm x (fun xid => swift.runArm_getDescS rp γ γc γm x
                (fun hstr => swift.Replica.getCmdDescWith.wp_coreD γ γc γm x
                  (by rw [hstr]; exact swift.CommandId.String.wp_proof)
                  (by rw [hstr]; exact swift.cmdStr_inj) swift.wp_cmapHasV
                  github_com.orcaman.concurrent_map.ConcurrentMap.wp_UpsertVL
                  (swift.Replica.handleMsg.seqSpecD.wp_linked γ γc γm x hstr hDL)
                  (swift.Replica.newDesc.wp_linked x γ γc γm hstr)
                  (swift.Replica.handleDesc.wp_linked γ γc γm x hstr hDL)) xid go!"recheck")
            }))
        (swift.tableAllocH_proof (srv_errvarint_fact hG s) kitCodecOkC_holds
          (swift.newFastAck.wp_proofP (srv_pool_fact hG s))
          encoding.gob.NewDecoder.wp_proof
          (encoding.gob.Decoder.Decode.wp_proof rfl (encoding.gob.getCodec.wp_proof rfl)))
        replica.Replica.wp_ConnectToPeers replica.Replica.wp_ComputeClosestPeers
        replica.Replica.wp_WaitForClientConnections replica.Sender.wp_SendToAll
        swift.wp_MNewLeader_marshal
        (swift.newFastAck.wp_proofP (srv_pool_fact hG s))
        (swift.copyFastAck.wp_proofP (swift.newFastAck.wp_proofP (srv_pool_fact hG s))))

/-- **`ServersOk`**, linked (over L2's claim, group E's). -/
theorem servers_ok_linked (hclaim : ClaimHyp) : ServersOk := servers_ok_of (servers_hyps hclaim)

/-- **`ServersOk`** (the brief's name). -/
theorem servers_ok (hclaim : ClaimHyp) : ServersOk := servers_ok_linked hclaim

end link

end Perennial.github_com.imdea_software.swiftpaxos
