/-
**Hypothesis** `RpcEnvHyp GF`: what the initializations of `net/rpc` and `net/http` leave on a
machine, which a net/rpc client over HTTP reads (`DialHTTP.spec`'s `cliEnv`, `httpEnv`,
`connected`). In this port `net/rpc` and `net/http` are names-only packages
(`Dsverify/Proof/net/{rpc,http}/Init.lean`: their `InitHyp`s assert only that the initializers
run, their facts are `True`), so these package variables' values are not facts of `isPkgInit`;
the class states them, as Go's initialization sets them (`models/net/rpc/client.go`'s
`ErrShutdown = errors.New("connection is shut down")`, `errFrame`, `debugLog = false`,
`connected = "200 Connected to Go RPC"`, and the packages `net/rpc` imports, `io`, `sync`,
`internal/poll`, initialized first; `net/http` imports `bufio` and `io`). A premise of
`gryff_remote_robust`, never an instance. It goes away when `Net/` gives net/rpc's package
initialization (Upamanyu's C2 item on #24), next to `RpcBootHyp`.
-/
module

public import Dsverify.Proof.gryff.Rpc.RpcHttpHyps
public import Net.Spec.net.rpc.DialHTTP

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.gryff

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net

/-- See the file header. -/
class RpcEnvHyp [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt]
    [go_gctx : GoGlobalContext] (GF : BundledGFunctors) [hG : HeapGS HasLC.hasLC GF]
    [go.Semantics] [net.rpc.Assumptions] [net.FieldAssumptions] [π : NetProtoGS] : Prop where
  /-- net/rpc's initialization leaves the client's package variables. -/
  rpc_env : isPkgInit (PROP := IProp GF) pkg_id.net.rpc ⊢
    net.rpc.cliEnv ∗ globalAddr net.rpc.connected ↦□ net.rpc.connectedStatus
  /-- net/http's initialization leaves its imports initialized. -/
  http_env : isPkgInit (PROP := IProp GF) pkg_id.net.http ⊢ net.http.httpEnv

section
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [net.rpc.Assumptions] [net.FieldAssumptions] [π : NetProtoGS]

/-- What `rpc.DialHTTP` asks besides the address (persistent). -/
def dialEnv : IProp GF :=
  iprop(⌜receiptBound GF ≤ 2 ^ 64⌝ ∗ net.rpc.cliEnv ∗ net.http.httpEnv ∗
    globalAddr net.rpc.connected ↦□ net.rpc.connectedStatus)

instance dialEnv_persistent : Persistent (dialEnv (GF := GF)) := by
  unfold dialEnv; infer_instance

theorem dialEnv_of_init [E : RpcEnvHyp GF] (hb : receiptBound GF ≤ 2 ^ 64) :
    isPkgInit (PROP := IProp GF) pkg_id.net.rpc ∗ isPkgInit (PROP := IProp GF) pkg_id.net.http ⊢
      dialEnv := by
  iintro ⟨#Hr, #Hh⟩
  unfold dialEnv
  ihave ⟨#Hc, #Hcon⟩ := E.rpc_env $$ Hr
  ihave #He := E.http_env $$ Hh
  iframe Hc Hcon He
  ipureintro; exact hb

end

end Perennial.gryff
