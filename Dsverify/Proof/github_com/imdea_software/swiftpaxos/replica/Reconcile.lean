/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/replica/Reconcile.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
From `replica.New`'s post (`replica.created`) to `ConnectToPeers`' pre (`replica.connPre`), in
two steps around what swift's `New` does in between (registering its messages in the table,
`NewSender`, `NewQuorumSystem`, then `go r.run()`):

* `replica.created_open`: `created` is the replica's fields: the read-only ones made persistent,
  the table (still owned, for the registrations), `State` and `PreferredPeerOrder` owned, and
  `replica.preConn` (the rest of what `ConnectToPeers` needs). Its persistent fields (`N`,
  `Shutdown`, `Logger`, `RPC`, ...) are what `NewQuorumSystem` (`N ↦□`), `NewSender`
  (`Shutdown ↦□`) and the logger calls take.
* `replica.connPre_intro`: `preConn`, the table once registered (persistent) with its
  `sp.tableOk`, the protocol's invariant, the logger's and configuration's facts and the node's
  address facts give `connPre`.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.replica.NewSpec
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.replica.ConnSpecs

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section defs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF]
variable [replica.Assumptions] [replica.defs.Assumptions] [rpc.Assumptions] [state.Assumptions]

/-- What `ConnectToPeers` needs of the replica's own fields (see the file header). -/
def replica.preConn (r : Loc) (γ : sp.Names) (lg cfgp : Loc) (N : Nat) (me : w32)
    (al : GoString) (asl : GoSlice) (tbl : Loc) : IProp netDistGF :=
  iprop(∃ (pc : Loc) (γpc : ChanNames) (pssl prsl pwsl alsl latsl ewsl : GoSlice) (cwm : GoMap),
    replica.fld r go!"Logger" ↦□ lg ∗ replica.fld r go!"N" ↦□ (W64 N) ∗
    replica.fld r go!"Id" ↦□ me ∗ replica.fld r go!"Config" ↦□ cfgp ∗
    replica.fld r go!"RPC" ↦□ tbl ∗
    replica.fld r go!"ProposeChan" ↦□ pc ∗ isChanBag γpc pc (sp.proposeP γ) ∗
    replica.fld r go!"Shutdown" ↦□ false ∗ replica.fld r go!"LRead" ↦□ false ∗
    replica.fld r go!"Dt" ↦□ null ∗ replica.fld r go!"Alias" ↦□ al ∗
    replica.fld r go!"PeerAddrList" ↦□ asl ∗
    replica.fld r go!"Peers" ↦□ pssl ∗ pssl ↦* List.replicate N interface.nil ∗
    replica.fld r go!"PeerReaders" ↦□ prsl ∗ prsl ↦* List.replicate N null ∗
    replica.fld r go!"PeerWriters" ↦□ pwsl ∗ pwsl ↦* List.replicate N null ∗
    replica.fld r go!"Alive" ↦□ alsl ∗ alsl ↦* List.replicate N false ∗
    replica.fld r go!"Latencies" ↦□ latsl ∗ latsl ↦* List.replicate N (W64 0) ∗
    replica.fld r go!"Ewma" ↦□ ewsl ∗ ewsl ↦* List.replicate N (W64 0) ∗
    replica.fld r go!"ClientWriters" ↦□ cwm ∗ cwm ↦$ (∅ : GMap w32 Loc) ∗
    replica.fld r go!"M" ↦ Perennial.zero_val sync.Mutex ∗
    replica.fld r go!"Listener" ↦ interface.nil ∗ replica.fld r go!"pendingClients" ↦ slice.nil)

/-- `New`'s post opened (see the file header). -/
theorem replica.created_open (r : Loc) (γ : sp.Names) (lg cfgp : Loc) (als : GoString) (me : w32)
    (N : Nat) (addrs : GoSlice) (thrifty exec : Bool) :
    replica.created r γ lg cfgp als me N addrs thrifty exec false ⊢
      |==> ∃ (v : replica.Replica) (pps : List w32),
        replica.preConn r γ lg cfgp N me als addrs v.RPC' ∗
        rpc.isTable v.RPC' (DFrac.own 1) (W8 9) ∅ ∗
        replica.fld r go!"State" ↦ v.State' ∗ state.ownState v.State' (fun _ => none) ∗
        replica.fld r go!"PreferredPeerOrder" ↦ v.PreferredPeerOrder' ∗
        v.PreferredPeerOrder' ↦* pps ∗
        ⌜pps.length = N ∧ ∀ p ∈ pps, 0 ≤ p.toInt ∧ p.toInt < N⌝ ∗
        replica.fld r go!"F" ↦□ v.F' ∗ replica.fld r go!"Thrifty" ↦□ thrifty ∗
        replica.fld r go!"Exec" ↦□ exec ∗ replica.fld r go!"Dreply" ↦□ v.Dreply' ∗
        replica.fld r go!"Beacon" ↦□ v.Beacon' ∗ replica.fld r go!"Durable" ↦□ v.Durable' ∗
        replica.fld r go!"Stats" ↦□ v.Stats' ∗ replica.fld r go!"StableStore" ↦□ v.StableStore' ∗
        replica.fld r go!"BeaconChan" ↦□ v.BeaconChan' := by
  unfold replica.created
  iintro ⟨%v, %γpc, %pps, Hv, %Hf, Hps, Hpr, Hpw, Hcw, Hal, Hpp, %Hpps, Hew, Hlat, Hst, Htbl,
    #Hbag⟩
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ := Hf
  iStructNamed Hv
  ipersist Logger
  ipersist N
  ipersist Id
  ipersist Config
  ipersist RPC
  ipersist ProposeChan
  ipersist Shutdown
  ipersist LRead
  ipersist Dt
  ipersist Alias
  ipersist PeerAddrList
  ipersist Peers
  ipersist PeerReaders
  ipersist PeerWriters
  ipersist Alive
  ipersist Latencies
  ipersist Ewma
  ipersist ClientWriters
  ipersist F
  ipersist Thrifty
  ipersist Exec
  ipersist Dreply
  ipersist Beacon
  ipersist Durable
  ipersist Stats
  ipersist StableStore
  ipersist BeaconChan
  imodintro
  iexists v, pps
  rw [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14] at *
  iframe Htbl State Hst PreferredPeerOrder Hpp F Thrifty Exec Dreply Beacon Durable Stats
    StableStore BeaconChan
  isplitl [Hps Hpr Hpw Hal Hlat Hew Hcw M Listener pendingClients]
  · unfold replica.preConn
    iexists v.ProposeChan', γpc, v.Peers', v.PeerReaders', v.PeerWriters', v.Alive',
      v.Latencies', v.Ewma', v.ClientWriters'
    iframe Logger N Id Config RPC ProposeChan Hbag Shutdown LRead Dt Alias PeerAddrList Peers Hps
      PeerReaders Hpr PeerWriters Hpw Alive Hal Latencies Hlat Ewma Hew ClientWriters Hcw M Listener
      pendingClients
  · ipureintro; exact Hpps

/-- `connPre` from `preConn` and what swift's `New` adds (see the file header). -/
theorem replica.connPre_intro (r : Loc) (γ : sp.Names) (γc γm γl : GName) (lg cfgp : Loc)
    (N : Nat) (me : w32) (al : GoString) (asl : GoSlice) (tbl : Loc) (fr : Bool) (nid : w8)
    (ents : GMap w8 rpc.Pair') (l : List GoString) (a ip : GoString)
    (hpure : l[me.toInt.toNat]? = some a ∧ replicaAddrs.contains a ∧ ip ++ [W8 58] <+: a ∧
      0 ≤ me.toInt ∧ me.toInt < N ∧ N ≤ 7 ∧ l.length = N ∧ (∀ a' ∈ l, a' ∈ replicaAddrs)) :
    replica.preConn r γ lg cfgp N me al asl tbl ∗ rpc.isTable tbl DFrac.discard nid ents ∗
      sp.tableOk γ γc γm ents ∗ sp.inv γ γc γm γl ∗ dlog.quiet lg ∗ config.plain cfgp fr ∗
      asl ↦*□ l ∗ lisProto (replica.wildOf a) (sp.inP γ γc γm) (sp.outQ γ γc γm) ∗
      ([∗list] a' ∈ replicaAddrs, addrProto a' (sp.inP γ γc γm) (sp.outQ γ γc γm)) ⊢
    replica.connPre r γ γc γm γl N me a ip := by
  iintro ⟨Hpre, #Htbl, #HtOk, #Hinv, #Hq, #Hplain, #Hl, #Hlp, #Haps⟩
  unfold replica.preConn
  icases Hpre with ⟨%pc, %γpc, %pssl, %prsl, %pwsl, %alsl, %latsl, %ewsl, %cwm, #HLg, #HN, #HId,
    #HCfg, #HRPC, #HPC, #Hbag, #HSd, #HLR, #HDt, #HAlias, #HAL, #HPs, Hps, #HPR, Hpr, #HPW, Hpw,
    #HAl, Hal, #HLat, Hlat, #HEw, Hew, #HCW, Hcw, HM, HLis, Hpc⟩
  unfold replica.connPre
  iexists lg, cfgp, tbl, pc, fr, nid, ents, γpc, asl, pssl, prsl, pwsl, alsl, latsl, ewsl, l, cwm,
    (List.replicate N (W64 0)), (List.replicate N (W64 0)), al
  iframe Hinv HLg Hq HN HId HCfg Hplain HRPC Htbl HtOk HPC Hbag HSd HLR HDt HAlias HAL Hl HPs Hps
    HPR Hpr HPW Hpw HAl Hal HLat Hlat HEw Hew HCW Hcw HM HLis Hpc Hlp Haps
  ipureintro
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hpure
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, by simp, by simp⟩

end defs

end Perennial.github_com.imdea_software.swiftpaxos
