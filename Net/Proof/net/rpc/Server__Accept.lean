/-
The proof of `Server.Accept` (`Net/Spec/net/rpc/Server__Accept.lean`): the loop's invariant is
`True` (everything it needs is persistent). Each `Accept` through the listener's interface
(`net.Listener.Accept.spec` with `accept_addrs_shared_rdl_au`, at the address it was dialed to): a connection gives the acceptor's tokens,
its fresh token and its read deadline's token, not set (`rpcAccepted`), served by `ServeConn` in a goroutine of its own, which gets the
fresh thread token of its `go` statement (`wp_fork_tok_body`) and returns it; a failure's error
(an `*OpError`, `errAny_resErr`) is logged (`log.Println` of a string) and `Accept` returns.
-/
module

public import Net.Spec.net.rpc.Server__Accept
public import Net.Spec.net.rpc.Server__ServeConn
public import Net.Spec.net.Listener__Accept
public import Net.Proof.net.AtAddr
public import Perennial.Spec.log.Println
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
  intro s γs C W la lis l
  wp_start as ⟨%Hb, #Hsrv, #Hall, #Henv, #Hset, #Hlog, #Hlis, #Hon, #Hli⟩
  iunfold net.isListener at Hlis
  icases Hlis with ⟨%tl, %x, %Hlis, #HlisAt⟩
  subst Hlis
  ihave #Hap : □ (∀ a, ⌜addrOk a = true ∧ lisAccepts la a⌝ →
      addrProto (Gg := hG.goose_globalGS) a (reqProto (Gg := hG.goose_globalGS) W a)
        (respProto (Gg := hG.goose_globalGS) W a)) $$ [Hall]
  · imodintro
    iintro %a %ha
    ihave ⟨Ha, -⟩ := Hall $$ %a %ha
    iunfold rpcAddr at Ha
    iunfold rpcAddrP at Ha
    icases Ha with ⟨Hp, -, -⟩
    iexact Hp
  wp_auto
  ihave HI : (True : IProp GF) $$ []
  · itrivial
  wp_for HI
  wp_apply wp_Accept tl l x la (fun _ => iprop(True))
      (fun a cn => iprop(connEnd (Gg := hG.goose_globalGS) cn true
        (respProto (Gg := hG.goose_globalGS) W a)
        (reqProto (Gg := hG.goose_globalGS) W a) [] [] ∗ connFresh (Gg := hG.goose_globalGS) cn true ∗
        rdlTok (Gg := hG.goose_globalGS) cn true false))
      $$ [$HlisAt $Hon]
    as %c %err (⟨%Herr, %cn, %a, %Ha, #Hc, Hend, Hfr, Hrdl⟩ | ⟨%k, -, #HE⟩)
  · iapply accept_addrs_shared_rdl_au la (reqProto (Gg := hG.goose_globalGS) W)
      (respProto (Gg := hG.goose_globalGS) W) $$ Hap Hli
  · -- a connection: served in a goroutine of its own
    subst Herr
    iunfold net.isConn at Hc
    icases Hc with ⟨%t, %la', %ra, %Hct, #Hca⟩
    subst Hct
    wp_auto
    iunfold connEnd at Hend
    icases Hend with ⟨Hsend, Hrecv⟩
    wp_bind (Fork _)
    iapply wp_fork_tok_body $$ [Hsend Hrecv Hfr Hrdl]
    · inext
      iintro Htok
      ihave ⟨#Haddr, #Hserves⟩ := Hall $$ %a %Ha
      iunfold rpcAddr at Haddr
      iunfold rpcAddrP at Haddr
      icases Haddr with ⟨-, -, ⟨%Hhs, %HhsA⟩⟩
      wp_apply wp_ServeConn s γs C W a t cn la' ra
        $$ [$Hsrv $Hserves $Henv $Hset $Hca Hsend Hrecv Hfr Hrdl Htok] as Htok
      · isplitr
        · ipureintro; exact Hb
        isplitr [Htok]
        · iunfold rpcAccepted; rw [Hhs, HhsA]; iexists []; iframe Hsend Hrecv Hfr
          isplitr
          · ipureintro; exact List.nil_prefix
          ileft; iexact Hrdl
        iexact Htok
      iframe Htok
      ipureintro; exact isPanic_intoVal ()
    inext
    wp_auto
    wp_for_post
    iframe
  · -- `Accept` failed: logged, and the loop ends
    ihave #Ha := errAny_resErr $$ HE
    ihave #Ha' := Ha
    iunfold models_lab.errAny at Ha'
    icases Ha' with ⟨%e, %He, -, #HW⟩
    subst He
    wp_auto
    wp_bind (App (Val #(methods _ go!"Error" _)) (Val #()))
    iapply HW
    inext
    iintro %msg
    wp_auto
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %sl ⟨Hsl, -⟩
    wp_apply wp_Println _ _ _ (fmt.ArgsWf.cons_string _ _ fmt.ArgsWf.nil) $$ [$Hlog $Hsl] as -
    wp_for_post
    iapply HΦ
    itrivial

end proof

end net.rpc
end Perennial
