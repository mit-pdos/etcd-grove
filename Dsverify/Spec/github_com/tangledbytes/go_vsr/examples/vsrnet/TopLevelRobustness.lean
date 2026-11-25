/-
**The vr kit** (dsverify-lab's vr kit, run vsr-bump-1, on examples/lib/remote; notes/dsv-vr.md):
twelve machines, none of which crashes -- the orchestrator (`Configure`: it chooses and sends the
configuration (3 or 5 replicas, the timeouts) to every other machine; then `remote.Check` of six
clients' operations, 8 each, against the key-value store with pending puts, porcupine over kit.go's
`Model()`), six client machines (each `remote.ServeClient`, an operation a request of its go-vsr
client to the replicas, `Op`) and five servers (each a go-vsr replica if the configuration has it,
the key-value store `vsrkv`) -- deployed at `vrKitAddrs` (`DistDeploy`: the addresses distinct and
valid, no connection, no listener). In every execution of fewer than `2 ^ 63` steps, with any
number of threads, no thread of any machine is stuck and none has a top-level panic (`Robust`,
`Robustness/Statement.lean`). Since the orchestrator panics unless porcupine accepts the history,
this says porcupine accepts every history, under every fault the net extension allows.

**No premise** beyond the deployment: every package initializer is proved (`encoding/json`'s the
main tree's, J1 of mit-pdos/etcd-grove#24, and its first run on a machine, the registry fresh,
`BootLinked.lean`; `log/slog`'s from the model's code), and so is every library spec the proof uses:
`Unmarshal`, `SetCodec`, `NewEncoder`/`Encoder.Encode` on a connection at the model's encoder
(`encRepModel`) and `NewDecoder`/`Decoder.Decode` of a frame on a connection at the model's decoder
(`decRepModel`) (the main tree's proofs, and `Proof/events/DecodeFrame.lean` over them), the
kit's registered codec and its named types' own generated methods (`vsrnet.TypeMethods`), a
connection as an `io.Reader` (Net's `net.conn_readerOk` with Perennial's `io.ReadFull`, which asks
the reader's precondition only of the reads it makes, mit-pdos/perennial#688), `log/slog`'s specs
(from the model).
Proved in `Dsverify/Proof/github_com/tangledbytes/go_vsr/examples/vsrnet/TopLevelRobustness.lean`.
-/
module

public import Dsverify.Proof.github_com.tangledbytes.go_vsr.examples.vsrnet.TopLevelDefs

@[expose] public section

noncomputable section

set_option linter.iris.style.nameCheck false

namespace Perennial

open Iris Iris.BI Net

namespace github_com.tangledbytes.go_vsr.examples.vsrnet

open github_com.mit_pdos.etcd_grove.examples.lib.remote.counter (remoteGF)

attribute [local instance] netExts netExtsSemantics netExtsInterp netExts_hasNet

/-- See the file header. -/
def vr_remote_robust.spec : Prop :=
  ∀ [GoGlobalContext] [lctx : GoLocalContext] [sem : go.Semantics]
    [orch_sem : cmd.orch.Assumptions]
    [client0_sem : cmd.client0.Assumptions]
    [client1_sem : cmd.client1.Assumptions]
    [client2_sem : cmd.client2.Assumptions]
    [client3_sem : cmd.client3.Assumptions]
    [client4_sem : cmd.client4.Assumptions]
    [client5_sem : cmd.client5.Assumptions]
    [server1_sem : cmd.server1.Assumptions]
    [server2_sem : cmd.server2.Assumptions]
    [server3_sem : cmd.server3.Assumptions]
    [server4_sem : cmd.server4.Assumptions]
    [server5_sem : cmd.server5.Assumptions]
    [field_sem : net.FieldAssumptions] [go.BasicIntoValInj],
    ∀ (σ : Nat → state) (g : GlobalState) (threads : Nat),
    DistDeploy vrKitAddrs (system σ) g →
    Robustness.Robust [] (system σ) g threads (2 ^ 63)

end github_com.tangledbytes.go_vsr.examples.vsrnet
end Perennial
