/-
`Server.Accept` at a valid address (`Server.Accept.specAddr`: a listener at `a` itself, `netLisAt`,
serving `rpcAddr W a`), as an instance of its canonical spec (`Net/Spec/net/rpc/Server__Accept.lean`,
for a listener at a valid address or a wildcard): a listener at a valid address takes only the
connections dialed to it (`lisAccepts_addrOk`). Not a spec of its own: it follows from the canonical
spec it is given (as `Net/Proof/net/AtAddr.lean`'s).
-/
module

public import Net.Spec.net.rpc.Server__Accept

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace net.rpc

section instances
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : net.rpc.Assumptions]
variable [π : NetProtoGS] [log.Assumptions]

/-- `Server.Accept.spec` at the valid address `a` (the shape before wildcard listeners). -/
abbrev Server.Accept.specAddr : Prop :=
  ∀ (s : Loc) (γs : GName) (C : CodecSpec GF) (W : RpcWorld GF) (a : GoString)
    (lis : GoInterface) (l : w64),
  {{ ⌜threadBound GF ≤ 2 ^ 31⌝ ∗ isServerAny s γs ∗ srvServes γs C W a ∗ srvEnv ∗ codecSet C ∗
      isPkgInit (PROP := IProp GF) pkg_id.log ∗ rpcAddr (Gg := hG.goose_globalGS) W a ∗
      net.isListener (GF := GF) lis l ∗ netLisAt (extLocalGS netExt (L := hG.goose_localGS)) l a ∗
      lisInv (Gg := hG.goose_globalGS) (extLocalGS netExt (L := hG.goose_localGS)) l a }}
    (App (Val (s @!! go.GoType.PointerType net.rpc.Server.ty @!! go!"Accept")) (Val #lis))
  {{ RET #(); True }}

theorem Server.Accept.spec_addr (h : Server.Accept.spec (GF := GF) (hG := hG)) :
    Server.Accept.specAddr (GF := GF) (hG := hG) := by
  intro s γs C W a lis l
  iintro %Φ ⟨%Hb, #Hsrv, #Hserves, #Henv, #Hset, #Hlog, #Haddr, #Hlis, #Hat, #Hli⟩ HΦ
  ihave #Hon := netLisAt_on _ l a $$ Hat
  ihave %Hok : ⌜addrOk a = true⌝ $$ [Hat]
  · iunfold netLisAt at Hat
    icases Hat with ⟨-, %Hok⟩
    ipureintro; exact Hok
  iapply h s γs C W a lis l $$ [] HΦ
  iframe Hsrv Henv Hset Hlog Hlis Hon Hli
  isplitr
  · ipureintro; exact Hb
  imodintro
  iintro %a' %ha'
  have e : a = a' := (lisAccepts_addrOk Hok).mp ha'.2
  subst e
  iframe Haddr Hserves

end instances

end net.rpc
end Perennial
