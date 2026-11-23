/-
The proof of `Server.ServeConn` (`Net/Spec/net/rpc/Server__ServeConn.lean`): a new server codec
over the connection (`newServerCodec`, its `rwc` kept for good), then `ServeCodec`.
-/
module

public import Net.Spec.net.rpc.Server__ServeConn
public import Net.Spec.net.rpc.Server__ServeCodec
public import Net.Spec.net.rpc.newServerCodec

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
variable [π : NetProtoGS]

theorem Server.ServeConn.wp_proof (wp_newServerCodec : newServerCodec.spec (GF := GF) (hG := hG))
    (wp_ServeCodec : Server.ServeCodec.spec (GF := GF) (hG := hG)) :
    Server.ServeConn.spec (GF := GF) (hG := hG) := by
  intro s γs C W a t cn la ra
  wp_start as ⟨%Hb, #Hsrv, #Hserves, #Henv, #Hset, #Hconn, Hacc, Htok⟩
  wp_auto
  wp_apply wp_newServerCodec as %sc ⟨Hrwc, Hwerr, Hrerr, Hclosed⟩
  ipersist Hrwc
  wp_apply wp_ServeCodec s γs C W a sc t cn la ra $$ [$Hsrv $Hserves $Henv $Hset Hwerr Hrerr Hclosed
      Hacc Htok] as Htok
  · isplitr
    · ipureintro; exact Hb
    isplitr
    · iunfold srvCodecAt; iframe Hrwc Hconn
    isplitr [Htok]
    · iunfold srvCodecOwn; iframe Hwerr Hrerr Hclosed Hacc
    iexact Htok
  iapply HΦ
  iexact Htok

end proof

end net.rpc
end Perennial
