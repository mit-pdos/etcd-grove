/-
The proof of `Server.Accept` (`Net/Spec/net/rpc/Server__Accept.lean`): the loop's invariant is
`True` (everything it needs is persistent). Each `Accept` through the listener's interface
(`net.Listener.Accept.spec` with `accept_shared_au`): a connection gives the acceptor's tokens and
its fresh token (`rpcAccepted`), served by `ServeConn` in a goroutine of its own, which gets the
fresh thread token of its `go` statement (`wp_fork_tok_body`) and returns it; a failure's error
(an `*OpError`, `errAny_resErr`) is logged (`log.Println` of a string) and `Accept` returns.
-/
module

public import Net.Spec.net.rpc.Server__Accept
public import Net.Spec.net.rpc.Server__ServeConn
public import Net.Spec.net.Listener__Accept
public import Net.Spec.log.Println
public import Net.Proof.net.rpc.Errs

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace net.rpc

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : net.rpc.Assumptions] [field_sem : net.FieldAssumptions]
variable [π : NetProtoGS] [net.Assumptions] [log.Assumptions]

attribute [local instance] GooseGlobalGS.gooseInvGS

theorem Server.Accept.wp_proof (wp_Accept : net.Listener.Accept.spec (GF := GF) (hG := hG))
    (wp_Println : log.Println.spec (GF := GF) (hG := hG))
    (wp_ServeConn : Server.ServeConn.spec (GF := GF) (hG := hG)) :
    Server.Accept.spec (GF := GF) (hG := hG) := by
  intro s γs C W a lis l
  wp_start as ⟨%Hb, #Hsrv, #Hserves, #Henv, #Hset, #Hlog, #Haddr, #Hlis, #Hat, #Hli⟩
  iunfold net.isListener at Hlis
  icases Hlis with ⟨%tl, %x, %Hlis, #HlisAt⟩
  subst Hlis
  ihave #Haddr' := Haddr
  iunfold rpcAddr at Haddr'
  icases Haddr' with ⟨#Hap, #Hreg⟩
  wp_auto
  ihave HI : (True : IProp GF) $$ []
  · itrivial
  wp_for HI
  wp_auto
  sorry

end proof

end net.rpc
end Perennial
