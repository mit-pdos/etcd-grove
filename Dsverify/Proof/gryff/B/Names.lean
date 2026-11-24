/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/B/Names.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit B3: the replica's ghost names (`Repl2Names`) as `NewReplica` makes them: the channel names of
the run loop's bags (the replica struct's channels, the EPaxos handler's, the generic replica's),
the escrow's name, and the fresh `xs`, `ptrs`, `crt`, `writers`, `boot`.
-/
module

public import Dsverify.Proof.gryff.Replica2.State

@[expose] public section

noncomputable section

namespace Perennial.gryff.unitB

open Iris Perennial.gryff.replica2

/-- The replica's channels' ghost names by kind (`replicaChans`' names): the struct's (`cR`, `cW`,
`cRMW` the client request channels; `fw` `forceWriteChan`; `s` the twelve `fastrpc` channels, in
the struct's order), the handler's 14 registered channels `hs` (`hKinds`' order), its
`instancesToRecover` (`γr`) and `executeOverwriteChan` (`γeo`), the generic replica's
`BeaconChan`, `OnClientConnect`, `DoneAdaptingChan`, `ProposeChan` (`proposeOwn`), and the client escrow's `esc`. -/
def chansOf (cR cW cRMW fw : ChanNames) (s : List ChanNames) (hs : List ChanNames)
    (γr γeo γbea γocc γda γprop esc : ChanNames) : String → ChanNames := fun kd =>
  match kd with
  | "read" => cR | "write" => cW | "rmw" => cRMW | "forceWrite" => fw
  | "read1" => s.getD 0 esc | "read2" => s.getD 1 esc | "write1" => s.getD 2 esc
  | "write2" => s.getD 3 esc | "write1Reply" => s.getD 4 esc | "w1timeout" => s.getD 5 esc
  | "w2timeout" => s.getD 6 esc | "write2Reply" => s.getD 7 esc
  | "read1Reply" => s.getD 10 esc | "read2Reply" => s.getD 11 esc
  | "prepare" => hs.getD 0 esc | "prepareReply" => hs.getD 1 esc | "preAccept" => hs.getD 2 esc
  | "preAcceptReply" => hs.getD 3 esc | "preAcceptOK" => hs.getD 4 esc
  | "accept" => hs.getD 5 esc | "acceptReply" => hs.getD 6 esc | "commit" => hs.getD 7 esc
  | "commitShort" => hs.getD 8 esc | "tryPreAccept" => hs.getD 9 esc
  | "tryPreAcceptReply" => hs.getD 10 esc | "executed" => hs.getD 11 esc
  | "preAcceptOKReply" => hs.getD 12 esc | "acceptOKReply" => hs.getD 13 esc
  | "recover" => γr | "executeOverwrite" => γeo
  | "propose" => γprop | "beacon" => γbea | "onClientConnect" => γocc | "doneAdapting" => γda
  | _ => esc

end Perennial.gryff.unitB
