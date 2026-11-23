/-
`server.Accept(lis)` (`server.go`) on this node's listener `l` at the rpc address `a` (`lis` its
`Listener`, shared: `lisInv`), on a server whose registrations serve `a` (`srvServes`) with a
registered codec meeting `C`: it accepts connections (`Listener.Accept.spec` with the library's
`accept_shared_au`: each connection's acceptor's end and tokens) and serves each in a goroutine
of its own (`ServeConn`, with the fresh thread token of its `go` statement), until an `Accept`
fails, which it logs (`log.Println`) before it returns. Proved in
`Net/Proof/net/rpc/Server__Accept.lean`.
-/
module

public import Net.Proof.net.rpc.ServerDefs
public import Perennial.Proof.log.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Net

namespace net.rpc

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : net.rpc.Assumptions] [field_sem : net.FieldAssumptions]
variable [π : NetProtoGS] [log.Assumptions]

/-- See the file header. -/
abbrev Server.Accept.spec : Prop :=
  ∀ (s : Loc) (γs : GName) (C : CodecSpec GF) (W : RpcWorld GF) (a : GoString)
    (lis : GoInterface) (l : w64),
  {{ ⌜threadBound GF ≤ 2 ^ 31⌝ ∗ isServer s γs ∗ srvServes γs C W a ∗ srvEnv ∗ codecSet C ∗
      isPkgInit (PROP := IProp GF) pkg_id.log ∗ rpcAddr (Gg := hG.goose_globalGS) W a ∗
      net.isListener (GF := GF) lis l ∗ netLisAt (extLocalGS netExt (L := hG.goose_localGS)) l a ∗
      lisInv (Gg := hG.goose_globalGS) (extLocalGS netExt (L := hG.goose_localGS)) l a }}
    (App (Val (s @!! go.GoType.PointerType net.rpc.Server.ty @!! go!"Accept")) (Val #lis))
  {{ RET #(); True }}

end spec

end net.rpc
end Perennial
