import Lean

open Lean
def targets : List String := ["rnWorkerStartTok", "rnLoopTok", "rnLoopTokP", "RNNames", "newRaftNode.spec", "bootstrappedRaft.newRaftNode.spec", "raftNode.start.spec", "RNBoot.view", "isNotifyD", "notifyDInv", "notifyDMatch", "rnReplayHist", "rnLeadLaw", "rnRestartOk", "isNotify", "isNotify2", "taReplayField", "taReplayBatch", "rnApN", "rnApSnap", "rnApR", "rnReplayJob", "rnStopImage", "EtcdServer.applyAll.specBatch", "EtcdServer.applyAll.specSnapM", "EtcdServer.applyAll.spec", "raftNode.onStop.spec", "rnApP", "wal.stopImage", "EtcdServer.applySnapshot.specSnapM", "EtcdServer.applySnapshot.specKeep", "EtcdServer.applySnapshot.spec"]
def isRepo (env : Environment) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | some i => let m := (env.header.moduleNames[i.toNat]!).toString
      ["Proof.", "Spec.", "TrustedCode.", "GooseLang."].any (fun p => m.startsWith p)
  | none => false
partial def closure (env : Environment) (start : Array Name) : NameSet := Id.run do
  let mut seen : NameSet := NameSet.empty
  let mut todo := start
  while h : todo.size > 0 do
    let n := todo.back
    todo := todo.pop
    if seen.contains n then continue
    seen := seen.insert n
    if !isRepo env n then continue
    match env.find? n with
    | some (.defnInfo d) => for c in d.value.getUsedConstants do todo := todo.push c
                            for c in d.type.getUsedConstants do todo := todo.push c
    | some ci => for c in ci.type.getUsedConstants do todo := todo.push c
    | none => pure ()
  return seen
def main : IO Unit := do
  initSearchPath (← findSysroot)
  let env ← importModules ((["Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.InvCancellable", "Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.InvGrpcStart", "Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.NoRefusal", "Proof.go_etcd_io.etcd.client.v3.PerTypeAuth", "Proof.go_etcd_io.etcd.client.v3.streamKeyFromCtx", "Proof.go_etcd_io.etcd.client.v3.NewAuth", "Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.logUnaryRequestStats", "Proof.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__leaseTimeToLive", "Proof.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__monitorClusterVersions", "Proof.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__monitorStorageVersion", "Proof.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__rangeStream", "Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3alarm.NewAlarmStore", "Proof.go_etcd_io.etcd.server.v3.etcdserver.NewRaftLoggerZap", "Proof.go_etcd_io.etcd.server.v3.auth.NewAuthStore", "Proof.go_etcd_io.etcd.pkg.v3.contention.NewTimeoutDetector", "Proof.go_etcd_io.etcd.server.v3.lease.leasehttp.RenewHTTP", "Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3alarm.NewAlarmStore", "Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.WatchDist", "Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.KVPutDist", "Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.KVGetDist", "Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.KVCompactDist", "Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.LeaseGrantDist", "Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.LeaseGrantLiveDist", "Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.LeaseLeasesGrantedDist", "Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.LeaseLeasesLiveDist", "Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.ClientLeaseLeasesDist", "Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.ClientLeaseTTLDist", "Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.KVDeleteDist", "Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.TxnCommitDist", "Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.AuthAuthEnableDist", "Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.AuthRoleAddDist", "Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.AuthRoleGrantPermissionDist", "Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.AuthUserAddDist", "Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.AuthUserGrantRoleDist", "Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.BootDist", "Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.putgetk.Defs", "Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.ClientPutDist", "Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.KVDeleteOnDist", "Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.KVGetOnDist", "Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.KVPutOnDist", "Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.LeaseGrantOnDist", "Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.LeaseLeasesOnDist", "Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.LeaseRevokeOnDist", "Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.LeaseTimeToLiveOnDist", "Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.NewPeerHandlerDist", "Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.NewServerDist", "Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.NewUserDist", "Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.PeerServeDist", "Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.ServeDist", "Proof.go_etcd_io.etcd.server.v3.etcdserver.bootstrapDist", "Proof.go_etcd_io.etcd.server.v3.etcdserver.bootstrapOne", "Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.TxnCommitOnDist", "Proof.k8s_io.component_base.tracing.Start", "Proof.go_etcd_io.etcd.server.v3.etcdserver.BootOneDefs"] : List String).toArray.map fun m => ({module := m.toName} : Import)) Options.empty 
  let mut nax := 0
  for (n, ci) in env.constants.toList do
    match ci with
    | .axiomInfo a =>
      if isRepo env n then
        nax := nax + 1
        let cl := closure env (a.type.getUsedConstants)
        for t in targets do
          let hits := cl.toList.filter (fun c => (c.toString.endsWith ("EtcdGrove." ++ t)).or (c.toString == t))
          if !hits.isEmpty then IO.println s!"HIT {n} -> {hits}"
    | _ => pure ()
  IO.println s!"checked {nax} repo axioms"
