/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/replica/NewSpec.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
`replica.New(alias, id, f, addrs, thrifty, exec, lread, config, l)` (internal spec): a fresh
replica struct, every field owned (`replica.created`): `N = len(addrs)` peers, none connected,
the table empty from `defs.RPC_TABLE`, an empty state machine, the propose channel a bag of
`sp.proposeP γ` (the ghost names `γ` are the caller's choice), no latency table (`LatencyConf`
is "": HUB-REQUEST R3 asks for its package state).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.replica.Defs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.state.Specs

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section defs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF]
variable [replica.Assumptions] [replica.defs.Assumptions] [rpc.Assumptions] [state.Assumptions]

/-- What `New` returns (see the file header). -/
def replica.created (r : Loc) (γ : sp.Names) (lg cfgp : Loc) (als : GoString) (me : w32)
    (N : Nat) (addrs : GoSlice) (thrifty exec lread : Bool) : IProp netDistGF :=
  iprop(∃ (v : replica.Replica) (γpc : ChanNames) (pps : List w32),
    r ↦ v ∗
    ⌜v.Logger' = lg ∧ v.N' = W64 N ∧ v.Id' = me ∧ v.Alias' = als ∧ v.PeerAddrList' = addrs ∧
      v.Config' = cfgp ∧ v.Shutdown' = false ∧ v.Thrifty' = thrifty ∧ v.Exec' = exec ∧
      v.LRead' = lread ∧ v.Dt' = null ∧ v.M' = Perennial.zero_val sync.Mutex ∧
      v.Listener' = interface.nil ∧ v.pendingClients' = slice.nil⌝ ∗
    v.Peers' ↦* List.replicate N (interface.nil : GoInterface) ∗
    v.PeerReaders' ↦* List.replicate N (null : Loc) ∗
    v.PeerWriters' ↦* List.replicate N (null : Loc) ∗
    v.ClientWriters' ↦$ (∅ : GMap w32 Loc) ∗
    v.Alive' ↦* List.replicate N false ∗
    v.PreferredPeerOrder' ↦* pps ∗
    ⌜pps.length = N ∧ ∀ p ∈ pps, 0 ≤ p.toInt ∧ p.toInt < N⌝ ∗
    v.Ewma' ↦* List.replicate N (W64 0) ∗ v.Latencies' ↦* List.replicate N (W64 0) ∗
    state.ownState v.State' (fun _ => none) ∗
    rpc.isTable v.RPC' (DFrac.own 1) (W8 9) ∅ ∗
    isChanBag γpc v.ProposeChan' (sp.proposeP γ))

/-- `New(...)` (see the file header). -/
abbrev replica.New.spec : Prop :=
  ∀ (als : GoString) (id f : w64) (addrs : GoSlice) (l : List GoString) (thrifty exec lread : Bool)
    (cfgp lg : Loc) (γ : sp.Names),
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.replica ∗
      addrs ↦*□ l ∗ ⌜0 ≤ sint.Z id ∧ sint.Z id < l.length ∧ l.length ≤ 7⌝ ∗
      typedPointsto (globalAddr replica.defs.LatencyConf) (go!"" : GoString) DFrac.discard }}
    (App (App (App (App (App (App (App (App (App (Val (@! replica.New)) (Val #als)) (Val #id))
      (Val #f)) (Val #addrs)) (Val #thrifty)) (Val #exec)) (Val #lread)) (Val #cfgp)) (Val #lg))
  {{ (r : Loc), RET #r;
      replica.created r γ lg cfgp als (W32 (sint.Z id)) l.length addrs thrifty exec lread }}

end defs

end Perennial.github_com.imdea_software.swiftpaxos
