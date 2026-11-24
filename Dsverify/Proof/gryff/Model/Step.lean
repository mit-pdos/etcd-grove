/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/Model/Step.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

A replica's step (`stepR`, with its result `StepRes`; `gStep` is its `Option`), dispatching like the run loop's `select` (`EPaxosRMWHandler.Loop`) and
the executor, and the global network `gNet` (`kahn.Net`, n = 3: the processes are the Gryff
replica ids 0, 1, 2).

| event | Go | model |
|---|---|---|
| `read` | `readChan` → `handleRead` → `StartRead` | `stepClientRead` |
| `write` | `writeChan` → `handleWrite` → `StartWrite` | `stepClientWrite` |
| `rmw` | `rmwChan` → `HandleRMW` → `handlePropose` | `stepClientRMW` |
| `read1` | `read1ChanProxied` → `handleRead1Proxied` | `stepRead1` |
| `read2` | `read2ChanProxied` → `handleRead2Proxied` | `stepRead2` |
| `write1` | `write1ChanProxied` → `handleWrite1Proxied` | `stepWrite1` |
| `write2` | `write2ChanProxied` → `handleWrite2Proxied` | `stepWrite2` |
| `read1Reply` | `read1ReplyChan` → `handleRead1Reply` | `stepRead1Reply` |
| `read2Reply` | `read2ReplyChan` → `handleRead2Reply` | `stepRead2Reply` |
| `write1Reply` | `write1ReplyChan` → `handleWrite1Reply` | `stepWrite1Reply` |
| `write2Reply` | `write2ReplyChan` → `handleWrite2Reply` | `stepWrite2Reply` |
| `forceWrite` | `forceWriteChan` → `handleForceWrite` | `stepForceWrite` |
| `prepare` | `prepareChan` → `handlePrepare` | `stepPrepare` |
| `preAccept` | `preAcceptChan` → `handlePreAccept` | `stepPreAccept` |
| `accept` | `acceptChan` → `handleAccept` | `stepAccept` |
| `commit` | `commitChan` → `handleCommit` | `stepCommit` |
| `prepareReply` | `prepareReplyChan` → `handlePrepareReply` | `stepPrepareReply` |
| `preAcceptReply` | `preAcceptReplyChan` → `handlePreAcceptReply` | `stepPreAcceptReply` |
| `preAcceptOK` | `preAcceptOKChan` → `handlePreAcceptOK` | `stepPreAcceptOK` |
| `acceptReply` | `acceptReplyChan` → `handleAcceptReply` | `stepAcceptReply` |
| `executed` | `executedChan` → `handleExecuted` | `handleExecuted` |
| `executeOverwrite` | `executeOverwriteChan` → `executeOverwrite` | `stepExecuteOverwrite` |
| `recover` | `instancesToRecover` → `startRecoveryForInstance` | `stepRecover` |
| `exec` | `executeCommands` → `executeCommand` → `strongconnect` | `stepExec` |

Cases of `Loop` without an event: `slowClockChan`, `BeaconChan`, `DoneAdaptingChan` (beacons
off: never fire), `commitShortChan`, `tryPreAcceptChan`, `tryPreAcceptReplyChan`,
`preAcceptOKReplyChan`, `acceptOKReplyChan`, `write1TimeoutChan`, `write2ConcurrentTimeoutChan`
(never sent to), `OnClientConnect` (statistics only: no state change; not modelled).
-/
module

public import Dsverify.Proof.gryff.Model.StepGryff
public import Dsverify.Proof.gryff.Model.StepRecovery
public import Dsverify.Proof.gryff.Model.StepExec

@[expose] public section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.model

/-- Replica `k`'s step with its result (`k` is its id, already in its state: `RState.init`). -/
noncomputable def stepR (_k : Fin 3) (s : RState) : Ev → StepRes
  | .read rid cid k d => stepClientRead s rid cid k d
  | .write rid cid k v d => stepClientWrite s rid cid k v d
  | .rmw rid cid k d oldV newV => stepClientRMW s rid cid k d oldV newV
  | .forceWrite => stepForceWrite s
  | .recover q i => stepRecover s q i
  | .exec q i => stepExec s q i
  | .msg (.read1 m) => stepRead1 s m
  | .msg (.read2 m) => stepRead2 s m
  | .msg (.write1 m) => stepWrite1 s m
  | .msg (.write2 m) => stepWrite2 s m
  | .msg (.read1Reply m) => stepRead1Reply s m
  | .msg (.read2Reply m) => stepRead2Reply s m
  | .msg (.write1Reply m) => stepWrite1Reply s m
  | .msg (.write2Reply m) => stepWrite2Reply s m
  | .msg (.prepare m) => stepPrepare s m
  | .msg (.preAccept m) => stepPreAccept s m
  | .msg (.accept m) => stepAccept s m
  | .msg (.commit m) => stepCommit s m
  | .msg (.prepareReply m) => stepPrepareReply s m
  | .msg (.preAcceptReply m) => stepPreAcceptReply s m
  | .msg (.preAcceptOK m) => stepPreAcceptOK s m
  | .msg (.acceptReply m) => stepAcceptReply s m
  | .msg (.executed m) => handleExecuted s m
  | .msg (.executeOverwrite m) => stepExecuteOverwrite s m

/-- Replica `k`'s step as the `kahn.Net` takes it: every failure (`never`, `disabled`, `dead`) is
`none`, "not enabled". -/
noncomputable def gStep (k : Fin 3) (s : RState) (e : Ev) : Option (RState × List Out) :=
  (stepR k s e).toOption

/-- The three replicas as a Kahn network. -/
noncomputable def gNet : kahn.Net where
  n := 3
  S := RState
  E := Ev
  M := Msg
  X := Ext
  init := fun k => RState.init k.val
  step := gStep
  recv := Ev.recv

end Perennial.gryff.model
