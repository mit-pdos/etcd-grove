/-
The vocabulary of net/rpc's HTTP client (`DialHTTPPath`): the dialer's end of a connection registered
in a world `W`, read before any request through `bufio.NewReader(conn)`, as Go's `DialHTTPPath` does
(the net extension's sticky read errors, D1 v3.5: no byte after a read error but a deadline's
timeout, and the dialer sets no read deadline).

* `crSt W a cn γ γe r`: the dialer's end has read `r` (`recvTok`), a prefix of the answer
  (`connectAns`: the acceptor writes nothing beyond it before a request, and the dialer, holding its
  half of the request list at `[]`, has written none) or of net/http's `400` answer (`badReqAns`,
  `hsErr`: the server could not read the handshake); its read deadline not set (`rdlTok cn false
  false`); and the once-cell `γe` (a monotone list): empty while no read has failed, `[r]` once one
  failed at `r`, and then the end reads nothing more (`readDead`, `read_after_dead_au`).
* `crErr γe r err`: a read failed at `r` (persistent): no byte after it (`crErr_final`), what
  `http.ReadResponse.spec`'s finality law asks; its error is `errLeaf` (`io.EOF`'s `*errorString`
  or an `*OpError`), what `http.ReadResponse.spec_errs` passes on.
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
def crSt (W : RpcWorld GF) (a : GoString) (cn : Nat) (γ : RpcConnNames) (γe : GName)
    (r : List w8) : IProp GF :=
  iprop(recvTok (Gg := hG.goose_globalGS) cn false (respProto W a) r ∗
    rdlTok (Gg := hG.goose_globalGS) cn false false ∗
    isRpcConn (Gg := hG.goose_globalGS) W a cn γ ∗
    monoListAuthOwn γ.reqs (1 : Qp).half ([] : List RpcReq) ∗ ⌜r <+: connectAns ∨ r <+: badReqAns⌝ ∗
    ((monoListAuthOwn γe 1 [r] ∗ readDead (Gg := hG.goose_globalGS) cn false) ∨
      monoListAuthOwn γe 1 ([] : List (List w8))))

/-- See the file header. -/
def crErr (γe : GName) (r : List w8) (err : GoInterface) : IProp GF :=
  iprop(monoListLbOwn γe [r] ∗ ⌜models_lab.errLeaf err⌝)

instance crErr_persistent (γe : GName) (r : List w8) (err : GoInterface) :
    Persistent (crErr (GF := GF) γe r err) := by
  unfold crErr; infer_instance

/-- After `cr` failed at `r`, it stays at `r`. -/
theorem crErr_final (W : RpcWorld GF) (a : GoString) (cn : Nat) (γ : RpcConnNames)
    (γe : GName) (r r' : List w8) (err : GoInterface) :
    crErr γe r err ∗ crSt W a cn γ γe r' ⊢ ⌜r <+: r' → r' = r⌝ := by
  iintro ⟨#He, Hst⟩
  iunfold crSt at Hst
  icases Hst with ⟨-, -, -, -, -, Hc⟩
  iunfold crErr at He
  icases He with ⟨#He, -⟩
  icases Hc with (⟨Hc, -⟩ | Hc)
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
acceptor is a prefix of the handshake's answer or of the error answer (`hsErr`): no answer is recorded (`connInv`: an answer's index
is below the requests taken). -/
theorem resp_before_req (W : RpcWorld GF) (a : GoString) (cn : Nat) (γ : RpcConnNames)
    (R : List w8) :
    isRpcConn (Gg := hG.goose_globalGS) W a cn γ ∗
      monoListAuthOwn γ.reqs (1 : Qp).half ([] : List RpcReq) ∗ £ 1 ∗
      protoPrefix (respProto (Gg := hG.goose_globalGS) W a) cn R ⊢
    |={⊤}=> monoListAuthOwn γ.reqs (1 : Qp).half ([] : List RpcReq) ∗
      ⌜R <+: W.hsAns a ∨ R <+: hsErr (W.hsAns a)⌝ := by
  iintro ⟨#Hrpc, Hh, Hlc, #Hpp⟩
  iunfold protoPrefix at Hpp
  icases Hpp with (%Hnil | ⟨%ext, %Hext, #HP⟩)
  · subst Hnil; iframe Hh; imodintro; ipureintro; exact Or.inl List.nil_prefix
  iunfold respProto at HP
  icases HP with (⟨%γ', %Rs, #Hrpc', #Hels, ⟨%HRs, %Hpre⟩, -⟩ | %Herr)
  rotate_left
  · iframe Hh; imodintro; ipureintro; exact Or.inr (Hext.trans Herr)
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
    exact Or.inl (by simpa [respsWire, framesOf] using Hext.trans Hpre)
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
