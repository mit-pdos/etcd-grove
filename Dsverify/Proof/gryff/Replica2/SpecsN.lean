/-
# Stage 2: the replica's code-level specs proved by unit N's connection code

`Replica.serveClient.wp` and `Replica.WaitForClientConnections.wp` (moved out of
`Replica2/Specs.lean`, which the handler proofs import, so that those do not wait on the
connection proofs): statements unchanged, proved by `N/Serve.lean` and `N/ClientConn.lean` over
`Net/`. (`NewReplicaDurable.wp`, also moved out, is `N/Boot`'s.)
-/
module

public import Dsverify.Proof.gryff.N.ClientConn
public import Dsverify.Proof.gryff.N.Boot

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.replica2

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net proto

attribute [local instance] GooseGlobalGS.gooseInvGS

section specs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [π : NetProtoGS] [sem : go.Semantics]
variable [gA : examples.gryffnet.Assumptions] [fa : src.fastrpc.Assumptions] [wire.BufioSpecs GF]
variable [wire.BinaryVarintHyps GF] [net.Assumptions] [net.FieldAssumptions] [netN.NetSpecs GF]
variable [io.Assumptions]

/-- **`serveClient(conn, reader, hs)`** (client `hs`'s requests at `k`; its caller took the
branch `hs & PeerHandshake == 0`, so `hs < peerMark`): registers the connection's writer
(`writerIs`), then each request read gets its token (`clientReqsOk_elim`, `req_mint`) and goes,
with it, on its kind's channel (`reqChanP`). The element's `Ev.Producible` comes from the parsed
bytes: `clientReqsOk_elim`'s `reqBytesD hs req i m` fixes `K' = 0`, `D'.Key' = -1` (so
`sint.Z (depOf D').key < 0`) and `ClientId' = hs`, and `hs < peerMark = 2^31` gives
`0 ≤ sint.Z hs`. -/
theorem Replica.serveClient.wp (γ : GryffNames GF) (ρ : Repl2Names) (k : Fin 3) (r gR : Loc)
    (conn : GoInterface) (rd : Loc) (hs : w32) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.genericsmr ∗ isReplica γ ρ k r ∗
        r.[src.gryff.Replica, go!"Replica"] ↦□ gR ∗ clientConnIn γ ρ k conn rd hs ∗
        ⌜hs < peerMark⌝ }}
      (App (App (App (genM gR go!"serveClient") (Val #conn)) (Val #rd)) (Val #hs))
    {{ RET #(); True }} := by
  exact serveClient_wp γ ρ k r gR conn rd hs

/-- `WaitForClientConnections()` (`run`'s goroutine): each accepted connection to
`clientListener`, whose handshake check hands it to `serveClient`. -/
theorem Replica.WaitForClientConnections.wp (γ : GryffNames GF) (ρ : Repl2Names) (k : Fin 3)
    (r gR : Loc) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.genericsmr ∗ isReplica γ ρ k r ∗
        r.[src.gryff.Replica, go!"Replica"] ↦□ gR ∗ listenerOwn γ ρ k gR }}
      (App (genM gR go!"WaitForClientConnections") (Val #()))
    {{ RET #(); True }} := by
  exact WaitForClientConnections_wp γ ρ k r gR

/-- `NewReplicaDurable(id, nodes, false, true, true, false, "", false)` (`gryff.NewReplica`). -/
theorem NewReplicaDurable.wp (id : w64) (sl : GoSlice) (nodes : List GoString) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.genericsmr ∗ sl ↦* nodes }}
      (App (App (App (App (App (App (App (App (Val (@! src.genericsmr.NewReplicaDurable))
        (Val #id)) (Val #sl)) (Val #false)) (Val #true)) (Val #true)) (Val #false))
        (Val #(go!""))) (Val #false))
    {{ (gR : Loc), RET #gR; genericBuilt gR id nodes [] [] }} := by
  unfold genericBuilt; exact NewReplicaDurable_wp id sl nodes

end specs

end Perennial.gryff.replica2
