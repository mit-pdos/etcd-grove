/-
**The SwiftPaxos kit's link** (notes/dsv-swiftpaxos.md): the three machines' specs
(`cnode.Orch.spec`, `cnode.Client.spec`, `Server.spec`) from their proofs and their callees'
linked results, among them `swift.New`'s (the lab's `ServersLink.lean`, ported: the replica's
run loop over its arms) and the package facts the callees take, from the packages' facts
(`swift.pkgSt`, `replica.pkgSt`, `defs.pkgSt`). The kit's top-level `Link.lean`.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
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
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.SyncDLinked
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.RunArmsDesc
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.DrainRechecks
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.HandleProposalProof
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.NewDescLinked
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.DescLinked
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.DepHash
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.CmdStr
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.TableAllocLinked
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.replica.ConnLinked
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.Results
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.master.Results
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.dlog.Results
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.replica.defs.Results
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.replica.Results

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.client.Results
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.client.Claim
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.master.RunLoop
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.ClientMachine
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.ClientLeaders
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.ClientConnect
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.ClientOp
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.ClientNodeAddr
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.AwaitConf
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.OrchSend
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.OrchNew
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.OrchProof
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.Register
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.RegisterCodec
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.ServeProof
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.ModelProof
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.NetRpc.CodecProof
public import Net.Proof.net.rpc.Results
public import Net.Proof.net.rpc.HandleHTTP
public import Net.Proof.net.rpc.Server__HandleHTTP
public import Net.Proof.net.http.Handle
public import Net.Proof.net.http.Results
public import Net.Proof.net.http.Serve
public import Net.Proof.net.Listen
public import Net.Proof.net.Dial
public import Net.Proof.net.Listener__Accept
public import Net.Proof.net.Conn__Read
public import Net.Proof.net.Conn__Write
public import Net.Proof.net.Conn__Close
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.lib.remote.Link
public import Dsverify.Proof.rabia.examples.rabianet.ConnReadFull
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.OrchParts
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.slices.SortFuncOnLinked
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.UpdateLogsLinked
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.DepHashLinked
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.PutVarint
public import Dsverify.Proof.github_com.orcaman.concurrent_map.Linked
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.lib.LibDepsLinked
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.InternalDepsLinked
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.replica.QuorumOk
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.AliveQuorum
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.FillAckN
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.GetDescWith

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.EtcdGrove.dsvswiftpaxos

open Perennial Perennial.github_com.imdea_software.swiftpaxos
open Iris Iris.BI Iris.ProgramLogic Iris.Std Net Dsv
open Perennial.github_com.mit_pdos.etcd_grove.examples.lib.remote

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

-- The kit's hypotheses on its callees, closed (`lib/LibDepsLinked.lean`,
-- `InternalDepsLinked.lean`; CLAUDE.md, "Import tiers").
attribute [local instance] swiftBufioDeps_holds swiftNetDeps_holds swiftKitDeps_holds

section srv
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF]
  [SwiftHyps netDistGF] [math.rand.Hyps netDistGF] [os.signal.NoSignals usr1Sigs netDistGF]
variable [examples.swiftnet.Assumptions] [net.FieldAssumptions]

/-- The package states' facts `swift.New` uses, from `pkgStates`. -/
theorem srv_pkg_facts :
    swift.SrvPkgFacts (hG := hG) := by
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
theorem srv_errvarint_fact :
    swift.ErrVarintFact (hG := hG) := by
  have h : isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.swift ⊢ swift.pkgSt := by
    with_unfolding_all exact isPkgInit_access (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.swift
  refine h.trans ?_
  unfold swift.pkgSt
  iintro ⟨-, -, -, #He, -⟩
  iexact He

/-- The fast-ack pool (`swift.pkgSt`) on a server node. -/
theorem srv_pool_fact :
    swift.FastAckPoolFact (hG := hG) := by
  have h : isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.swift ⊢ swift.pkgSt := by
    with_unfolding_all exact isPkgInit_access (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.swift
  refine h.trans ?_
  unfold swift.pkgSt
  iintro ⟨-, -, -, -, #Hp⟩
  iexact Hp

/-- The hooks are nil (`swift.pkgSt`) on a server node: `runInv_alloc`'s `swift.HooksFact`. -/
theorem srv_hooks_fact :
    swift.HooksFact (hG := hG) := by
  have h : isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.swift ⊢ swift.pkgSt := by
    with_unfolding_all exact isPkgInit_access (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.swift
  unfold swift.HooksFact
  refine h.trans ?_
  unfold swift.pkgSt
  iintro ⟨#H1, #H2, -⟩
  iframe H1 H2

/-- **`swift.New`, linked** (the lab's `ServersLink.lean`'s `snew` case). -/
theorem wp_swiftNew : swift.New.spec (hG := hG) := by
    have hDL : swift.DescLinkH := ⟨swift.newFastAck.wp_proofP srv_pool_fact,
      swift.copyFastAck.wp_proofP (swift.newFastAck.wp_proofP srv_pool_fact)⟩
    -- the swift group's (Proof/swift/Link.lean): `swift.New`'s body is proved; its callees
    -- still open are marked (notes/prove-swift.md §10)
    exact swift.wp_New srv_pkg_facts
      (swift.wp_NewBatcher
        swift.wp_clientChecksum
        (swift.releaseFastAck.wp_proof srv_pool_fact)
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
          srv_hooks_fact
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
                    swift.CommandId.String.wp_proof slices.wp_SortFuncOn)
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
                      (swift.MSync.marshal_proofG encoding.gob.NewEncoder.wp_hyp encoding.gob.Encoder.EncodeW.wp_hyp)))
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
                  replica.Sender.wp_SendTo (swift.MNewLeaderAckN.marshal_proofP swift.PutVarint.wp_proof)
                  swift.replyChan.stop.wp_proof) l r b
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
        (swift.tableAllocH_proof srv_errvarint_fact
          (swift.newFastAck.wp_proofP srv_pool_fact)
          encoding.gob.NewDecoder.wp_hyp encoding.gob.Decoder.Decode.wp_hyp)
        replica.Replica.wp_ConnectToPeers replica.Replica.wp_ComputeClosestPeers
        replica.Replica.wp_WaitForClientConnections replica.Sender.wp_SendToAll
        swift.wp_MNewLeader_marshal
        (swift.newFastAck.wp_proofP srv_pool_fact)
        (swift.copyFastAck.wp_proofP (swift.newFastAck.wp_proofP srv_pool_fact)))

end srv

section machines
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF]
  [SwiftHyps netDistGF] [math.rand.Hyps netDistGF] [os.signal.NoSignals usr1Sigs netDistGF] [SwiftOsRandom netDistGF]
variable [examples.swiftnet.Assumptions] [net.FieldAssumptions]
variable [RpcHttpAddr netDistGF] [H : RpcHttpHyp netDistGF]

/-- The client node's package facts (`ClientPkgFacts`), from `swift.pkgSt` and `defs.pkgSt`. -/
theorem client_pkg_facts : swift.handler.ClientPkgFacts (hG := hG) := by
  refine ⟨?_, ?_⟩
  · have h : isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.swift ⊢ swift.pkgSt := by
      with_unfolding_all exact isPkgInit_access (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.swift
    refine h.trans ?_
    iintro #Hs
    ihave ⟨-, -, #H3⟩ := swift.pkgSt_hooks $$ Hs
    ihave ⟨%x, #Hx, %Hxn⟩ := swift.pkgSt_errVarint $$ Hs
    iframe H3
    iexists x
    iframe Hx
    ipureintro; exact Hxn
  · exact (srv_pkg_facts (hG := hG)).dfs

/-- The net callees (`SwNetDeps`), Net's. -/
theorem swNetDeps : SwNetDeps (hG := hG) :=
  ⟨net.Dial.wp_proof, net.Listen.wp_proof, net.Listener.Accept.wp_proof, net.Conn.Read.wp_proof,
    net.Conn.Write.wp_proof, net.Conn.Close.wp_proof, rabia.examples.rabianet.io.ReadFull.wp_proofLt⟩

/-- **Client machine `c`** (`Client(c)`), linked. -/
theorem wp_Client [ρ : RemoteGS] : cnode.Client.spec (hG := hG) :=
  cnode.Client.wp_proof
    (fun γ γk c hc => cnode.clientNode.wp_proof γ γk c hc
      (cnode.newClient.wp_proof γ c hc (awaitConf.wp_proof swNetDeps) cnode.atConf_proof
        cnode.atStart_proof client.claimGhost.wp_proof (cnode.Register.wp_proof net.rpc.SetCodec.wp)
        (cnode.Sys.changeLeaders.wp_proof γ c cnode.atRpc_proof replica.defs.wp_NewBeTheLeaderReply
          (fun c W a γc γm cc pa btl => master.wp_call_btl net.rpc.Client.Call.wp c W a γc γm cc pa btl)
          net.rpc.Client.Close.wp))
      (cnode.op.wp_proof γ γk c
        (cnode.Sys.connect.wp_proof γ c hc cnode.hostMaster_proof cnode.portMaster_proof
          client.wp_NewClientLog client.wp_NewBufferClient
          (client.BufferClient.wp_ConnectG client_pkg_facts) client.BufferClient.wp_DisconnectG
          (swift.wp_NewClient client_pkg_facts))
        (client.BufferClient.wp_Write dlog.Logger.wp_Println)
        (client.BufferClient.wp_Read dlog.Logger.wp_Println))
      examples.swiftnet.Codec.wp_proof
      EtcdGrove.remote.wp_ServeClient)
    cnode.Addrs_proof cnode.ClientAddrs_proof

/-- **The orchestrator** (`Orch()`), linked. -/
theorem wp_Orch [ρ : RemoteGS] : cnode.Orch.spec (hG := hG) :=
  cnode.Orch.wp_proof (fun γ => orch.New.wp_proof γ (sendConf.wp_proof swNetDeps) net.rpc.log.Println.wp
    orch.Conf.String.wp_proof orch.Conf.encode.wp_proof orch.mine.wp_proof orch.choose.wp_proof
    orch.plan.wp_proof)
    cnode.Addrs_proof cnode.ClientAddrs_proof examples.swiftnet.Model.wp_proof
    examples.swiftnet.Codec.wp_proof
    (examples.swiftnet.Gen.wp_proof github_com.goose_lang.primitive.wp_RandomUint64)
    EtcdGrove.remote.wp_Check

/-- **Server machine `i + 1`** (`Server(id)`), linked. -/
theorem wp_Server : Server.spec (hG := hG) :=
  Server.wp_proof
    (fun γ i hi => serve.wp_proof swNetDeps γ i hi (awaitConf.wp_proof swNetDeps)
      client.claimGhost.wp_proof (cnode.Register.wp_proof net.rpc.SetCodec.wp) master.wp_New
      (master.Master.wp_Run dlog.Logger.wp_Printf dlog.Logger.wp_Fatal
        replica.defs.wp_NewBeTheLeaderReply)
      (register.wp_proof swiftCodecLaws net.rpc.Client.Call.wp net.rpc.Client.Close.wp)
      setMaxDesc.wp_proof wp_swiftNew)
    cnode.Addrs_proof


end machines


section rpchttp
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF]
variable [examples.swiftnet.Assumptions] [net.FieldAssumptions]

/-- `RpcHttpHyp` holds: `Net/`'s specs of the net/rpc-over-HTTP calls, from `Net/`'s proofs
(`HandleHTTP` over net/http's `Handle`, and net/http's `Serve`: `Handle.wp` and `Serve.wp_rpc`,
proved; `Serve` over the interim context axioms). -/
theorem netRpcHttpHyp : RpcHttpHyp netDistGF :=
  ⟨net.rpc.DialHTTP.wp,
    net.rpc.HandleHTTP.wp_proof
      (net.rpc.Server.HandleHTTP.wp_proof net.http.Handle.wp net.rpc.Server.ServeHTTP.wp),
    net.rpc.Register.wp_fresh, net.http.Serve.wp_rpc⟩

end rpchttp

end Perennial.EtcdGrove.dsvswiftpaxos
