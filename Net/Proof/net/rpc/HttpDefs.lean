/-
The vocabulary of net/rpc's HTTP client (`DialHTTPPath`): the model's `connectReader` (the reader
`DialHTTPPath` reads the server's `CONNECT` answer through, `models/net/rpc/client.go`) over the
dialer's end of a connection registered in a world `W`, before any request.

* `crAt cr t cn a la ra` (persistent): `cr`'s `r` field is the `*TCPConn` `t`, the dialer's end of
  `cn` to `a` (`connAt`).
* `crSt W a cn γ cr γe r`: `cr` has delivered `r`, the connection's reader at `R` (`recvTok`), a
  prefix of the answer (`connectAns`: the acceptor writes nothing beyond it before a request, and
  the dialer, holding its half of the request list at `[]`, has written none); its `failed` flag,
  and the once-cell `γe` (a monotone list): empty while `cr` has not failed, and then `R = r`;
  `[r]` once it failed at `r` (its lower bound persistent; after the failure `cr` reads the
  connection on into a buffer of its own: `r <+: R`).
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
  iprop(∃ (f : Bool) (R : List w8), structFieldRef net.rpc.connectReader go!"failed" cr ↦ f ∗
    recvTok (Gg := hG.goose_globalGS) cn false (respProto W a) R ∗
    isRpcConn (Gg := hG.goose_globalGS) W a cn γ ∗
    monoListAuthOwn γ.reqs (1 : Qp).half ([] : List RpcReq) ∗ ⌜r <+: R ∧ R <+: connectAns⌝ ∗
    ((⌜f = true⌝ ∗ monoListAuthOwn γe 1 [r]) ∨
      (⌜f = false ∧ R = r⌝ ∗ monoListAuthOwn γe 1 ([] : List (List w8)))))

/-- See the file header. -/
def crErr (γe : GName) (r : List w8) (_err : GoInterface) : IProp GF :=
  monoListLbOwn γe [r]

instance crErr_persistent (γe : GName) (r : List w8) (err : GoInterface) :
    Persistent (crErr (GF := GF) γe r err) := by
  unfold crErr; infer_instance

/-- After `cr` failed at `r`, it stays at `r`. -/
theorem crErr_final (W : RpcWorld GF) (a : GoString) (cn : Nat) (γ : RpcConnNames) (cr : Loc)
    (γe : GName) (r r' : List w8) (err : GoInterface) :
    crErr γe r err ∗ crSt W a cn γ cr γe r' ⊢ ⌜r <+: r' → r' = r⌝ := by
  iintro ⟨#He, Hst⟩
  iunfold crSt at Hst
  icases Hst with ⟨%f, %R, -, -, -, -, -, Hc⟩
  iunfold crErr at He
  icases Hc with (⟨-, Hc⟩ | ⟨-, Hc⟩)
  · ihave %Hv := mono_list_auth_lb_valid _ _ _ _ $$ Hc He
    obtain ⟨-, Hp⟩ := Hv
    ipureintro
    intro _
    obtain ⟨t, ht⟩ := Hp
    cases t with
    | nil => simpa using ht.symm
    | cons _ _ => simp at ht
  · ihave %Hv := mono_list_auth_lb_valid _ _ _ _ $$ Hc He
    obtain ⟨-, Hp⟩ := Hv
    exact absurd (List.prefix_nil.1 Hp) (by simp)

/-- Before any request (the dialer's half of the request list at `[]`), what the dialer reads of the
acceptor is a prefix of the handshake's answer: no answer is recorded (`connInv`: an answer's index
is below the requests taken). -/
theorem resp_before_req (W : RpcWorld GF) (a : GoString) (cn : Nat) (γ : RpcConnNames)
    (R : List w8) :
    isRpcConn (Gg := hG.goose_globalGS) W a cn γ ∗
      monoListAuthOwn γ.reqs (1 : Qp).half ([] : List RpcReq) ∗ £ 1 ∗
      protoPrefix (respProto (Gg := hG.goose_globalGS) W a) cn R ⊢
    |={⊤}=> monoListAuthOwn γ.reqs (1 : Qp).half ([] : List RpcReq) ∗ ⌜R <+: W.hsAns a⌝ := by
  iintro ⟨#Hrpc, Hh, Hlc, #Hpp⟩
  iunfold protoPrefix at Hpp
  icases Hpp with (%Hnil | ⟨%ext, %Hext, #HP⟩)
  · subst Hnil; iframe Hh; imodintro; ipureintro; exact List.nil_prefix
  iunfold respProto at HP
  icases HP with ⟨%γ', %Rs, #Hrpc', #Hels, ⟨%HRs, %Hpre⟩, -⟩
  ihave #Hrpc0 := Hrpc
  iunfold isRpcConn at Hrpc0 Hrpc'
  icases Hrpc0 with ⟨#He, #Hinv⟩
  icases Hrpc' with ⟨#He', -⟩
  iunfold regElem at He He'
  ihave %Hg := ghostMapElem_agree _ _ _ _ _ _ $$ He He'
  subst Hg
  cases Rs with
  | nil =>
    iframe Hh; imodintro; ipureintro
    simpa [respsWire, framesOf] using Hext.trans Hpre
  | cons x Rs =>
    ihave #Hx := BigSepL.bigSepL_lookup
      (Φ := fun _ (x : Ans) => ghostMapElem (GF := GF) γ.ans x.idx .discard (some (x.msg, x.reply)))
      (show (x :: Rs)[0]? = some x from rfl) $$ Hels
    iinv Hinv with Hi Hclose
    imod lc_fupd_elim_later (E := ⊤ \ ↑connN) $$ Hlc Hi with Hi
    iunfold connInv at Hi
    icases Hi with ⟨%L', %k, %A, Hh', Hctr, HA, Hfr, ⟨%Hk, %HA⟩, Hnamed, Hdeps, Hans⟩
    ihave %Hag := monoListAuthOwn_agree _ _ _ _ _ $$ Hh Hh'
    obtain ⟨-, rfl⟩ := Hag
    ihave %Hl := ghost_map_lookup $$ HA Hx
    exfalso
    have h1 := HA x.idx (by
      rw [show A.lookup x.idx = PartialMap.get? A x.idx from rfl]
      exact Option.isSome_iff_exists.2 ⟨_, Hl⟩)
    simp at Hk
    omega

end defs

end net.rpc
end Perennial
