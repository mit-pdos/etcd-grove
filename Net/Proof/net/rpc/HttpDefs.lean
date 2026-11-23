/-
The vocabulary of net/rpc's HTTP client (`DialHTTPPath`): the model's `connectReader` (the reader
`DialHTTPPath` reads the server's `CONNECT` answer through, `models/net/rpc/client.go`) over the
dialer's end of a connection registered in a world `W`, before any request.

* `crAt cr t cn a la ra` (persistent): `cr`'s `r` field is the `*TCPConn` `t`, the dialer's end of
  `cn` to `a` (`connAt`).
* `crSt W a cn γ cr γe r`: `cr` has delivered `r`, the connection's reader at `r` (`recvTok`), a
  prefix of the answer (`connectAns`: the acceptor writes nothing beyond it before a request, and
  the dialer, holding its half of the request list at `[]`, has written none); its `failed` flag,
  and the once-cell `γe` (`ghostMapElem`, key `()`): unwritten (`none`, owned) while `cr` has not
  failed, `some r` (persistent) once it failed at `r`.
* `crErr γe r err`: `cr` failed at `r` (persistent): no byte after it (`crErr_final`), what
  `http.ReadResponse.spec`'s finality law asks.
-/
module

public import Net.Proof.net.rpc.ClientDefs
public import Proof.io.ReaderStream

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace net.rpc

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : net.rpc.Assumptions] [field_sem : net.FieldAssumptions]
variable [π : NetProtoGS]

attribute [local instance] GooseGlobalGS.gooseInvGS

/-- See the file header. -/
def crAt (cr t : Loc) (cn : Nat) (a : GoString) (la ra : GoInterface) : IProp GF :=
  iprop(structFieldRef net.rpc.connectReader go!"r" cr ↦□
      interface.mkOk (go.GoType.PointerType net.TCPConn.ty) #t ∗
    net.connAt (GF := GF) t cn false a la ra)

instance crAt_persistent (cr t : Loc) (cn : Nat) (a : GoString) (la ra : GoInterface) :
    Persistent (crAt (GF := GF) cr t cn a la ra) := by
  unfold crAt; infer_instance

/-- See the file header. -/
def crSt (W : RpcWorld GF) (a : GoString) (cn : Nat) (γ : RpcConnNames) (cr : Loc) (γe : GName)
    (r : List w8) : IProp GF :=
  iprop(∃ f : Bool, structFieldRef net.rpc.connectReader go!"failed" cr ↦ f ∗
    recvTok (Gg := hG.goose_globalGS) cn false (respProto W a) r ∗
    isRpcConn (Gg := hG.goose_globalGS) W a cn γ ∗
    monoListAuthOwn γ.reqs (1 : Qp).half ([] : List RpcReq) ∗ ⌜r <+: connectAns⌝ ∗
    ((⌜f = true⌝ ∗ ghostMapElem γe () .discard (some r : Option (List w8))) ∨
      (⌜f = false⌝ ∗ ghostMapElem γe () (DFrac.own 1) (none : Option (List w8)))))

/-- See the file header. -/
def crErr (γe : GName) (r : List w8) (_err : GoInterface) : IProp GF :=
  ghostMapElem γe () .discard (some r : Option (List w8))

instance crErr_persistent (γe : GName) (r : List w8) (err : GoInterface) :
    Persistent (crErr (GF := GF) γe r err) := by
  unfold crErr; infer_instance

/-- After `cr` failed at `r`, it stays at `r`. -/
theorem crErr_final (W : RpcWorld GF) (a : GoString) (cn : Nat) (γ : RpcConnNames) (cr : Loc)
    (γe : GName) (r r' : List w8) (err : GoInterface) :
    crErr γe r err ∗ crSt W a cn γ cr γe r' ⊢ ⌜r <+: r' → r' = r⌝ := by
  iintro ⟨#He, Hst⟩
  iunfold crSt at Hst
  icases Hst with ⟨%f, -, -, -, -, -, Hc⟩
  iunfold crErr at He
  icases Hc with (⟨-, Hc⟩ | ⟨-, Hc⟩)
  · ihave %Hg := ghostMapElem_agree _ _ _ _ _ _ $$ He Hc
    ipureintro
    intro _
    exact (Option.some.inj Hg).symm
  · ihave %Hg := ghostMapElem_agree _ _ _ _ _ _ $$ He Hc
    cases Hg

end defs

end net.rpc
end Perennial
