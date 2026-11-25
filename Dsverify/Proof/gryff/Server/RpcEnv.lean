/-
What a net/rpc client over HTTP reads on a server machine (`DialHTTP.spec`'s `cliEnv`, `httpEnv`,
`connected`: `dialEnv`), and the kit's services' error answers (`withErr_errOk`). These package
variables' values come from the machine's boot (`rpcInitRes`, `httpInitRes`: `serverBoot`,
`cmd/server*/Boot.lean`, from net/rpc's and net/http's first initializations).
-/
module

public import Dsverify.Proof.gryff.Rpc.RpcHttp
public import Dsverify.Proof.gryff.Rpc.Defs
public import Net.Spec.net.rpc.DialHTTP

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.gryff

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net

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

/-- A service accepting error answers (`withErr`) meets `errOk` (swiftpaxos's `withErr_errOk`). -/
theorem withErr_errOk (S : net.rpc.MethodSpec GF) : ⊢ net.rpc.errOk (withErr S) := by
  unfold net.rpc.errOk withErr
  iintro !> %m %args %Φ %msg %Hmsg HS
  icases HS with ⟨-, Herr⟩
  imodintro
  iapply Herr $$ %msg %(net.rpc.srvErrMsg_ne msg Hmsg)

end

end Perennial.gryff
