/-
The ghost lemmas of the rpc client (`ClientDefs.lean`, `Proto.lean`): appending a request to its
connection (`req_append`: the deposit and the request's names go to the connection's invariant,
the protocol fact of the request stream comes out), and an unsent request is never answered
(`unsent_reqSent`).
-/
module

public import Net.Proof.net.rpc.ClientDefs
public import Net.Proof.net.rpc.ProtoGhost

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace net.rpc

theorem reqsWire_append (L : List RpcReq) (r : RpcReq) :
    reqsWire (L ++ [r]) = reqsWire L ++ reqWire (W64 L.length) r.sm r.body := by
  simp [reqsWire, List.mapIdx_append]

section ghost
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : net.rpc.Assumptions] [field_sem : net.FieldAssumptions]
variable [π : NetProtoGS]

attribute [local instance] GooseGlobalGS.gooseInvGS

theorem answerRes_app (L : List RpcReq) (r : RpcReq) (i : Nat)
    (o : Option (GoString × List w8)) :
    answerRes (GF := GF) L i o ⊢ answerRes (L ++ [r]) i o := by
  rcases o with _ | ⟨msg, reply⟩
  · unfold answerRes; iintro _; itrivial
  · unfold answerRes
    iintro ⟨%r', %Hr', H⟩
    iexists r'
    iframe H
    ipureintro
    obtain ⟨hi, -⟩ := List.getElem?_eq_some_iff.1 Hr'
    rw [List.getElem?_append_left hi]
    exact Hr'

/-- The dialer appends its request `r` (number `L.length`, its names recorded with its token
`ap`, its deposit `S M eb Φ` for a service of the address) to the connection: its half of the
request list grows, and the request stream with the request's wire meets the protocol. -/
theorem req_append (W : RpcWorld GF) (a : GoString) (cn : Nat) (γ : RpcConnNames)
    (L : List RpcReq) (sm svc M : GoString) (S : MethodSpec GF) (eb : List w8)
    (Φ : List w8 → GoString → IProp GF) (post col ap : GName)
    (hL : ∀ r ∈ L, reqOk r) (hlen : L.length + 1 ≤ 2 ^ 64)
    (hsm : sm.length + 16 < 2 ^ 63) (heb : eb.length < 2 ^ 63)
    (hsv : splitSM sm = some (svc, M) ∧ W.SS a svc = some S) :
    isRpcConn (Gg := hG.goose_globalGS) W a cn γ ∗ £ 1 ∗
      monoListAuthOwn γ.reqs (1 : Qp).half L ∗
      ghostMapElem γ.nm L.length .discard (post, col, ap) ∗ token ap ∗
      savedPredOwn post .discard (fun p : List w8 × GoString => Φ p.1 p.2) ∗ S M eb Φ ⊢
    |={⊤}=> monoListAuthOwn γ.reqs (1 : Qp).half (L ++ [(sm, eb, post, col)]) ∗
      □ reqProto (Gg := hG.goose_globalGS) W a cn
        (reqsWire L ++ reqWire (W64 L.length) sm eb) := by
  iintro ⟨#Hrpc, Hlc, Hhalf, #Hnm, Hap, #Hpost, HS⟩
  ihave #Hrpc' := Hrpc
  iunfold isRpcConn at Hrpc'
  icases Hrpc' with ⟨#Hre, #Hinv⟩
  iinv Hinv with Hi Hclose
  imod lc_fupd_elim_later (E := ⊤ \ ↑connN) $$ Hlc Hi with Hi
  iunfold connInv at Hi
  icases Hi with ⟨%L', %k, %A, Hh', Hctr, HA, Hfr, ⟨%Hk, %HA⟩, Hnamed, Hdeps, Hans⟩
  ihave %Hag := monoListAuthOwn_agree _ _ _ _ _ $$ Hhalf Hh'
  obtain ⟨-, rfl⟩ := Hag
  ihave Hf := (ml_halves (Gg := hG.goose_globalGS) γ.reqs L).2 $$ [$Hhalf $Hh']
  imod monoListAuthOwn_update_app [(sm, eb, post, col)] $$ Hf with ⟨Hf, #Hlb⟩
  icases (ml_halves (Gg := hG.goose_globalGS) γ.reqs _).1 $$ Hf with ⟨Hhalf, Hh'⟩
  imod Hclose $$ [Hh' Hctr HA Hfr Hnamed Hdeps Hans Hap HS] with -
  · inext
    iunfold connInv
    iexists L ++ [(sm, eb, post, col)], k, A
    iframe Hh' Hctr HA Hfr
    isplitr
    · ipureintro
      refine ⟨by simp; omega, HA⟩
    isplitl [Hnamed Hap]
    · iapply BigSepL.bigSepL_append.2
      iframe Hnamed
      iapply BigSepL.bigSepL_singleton.2
      iunfold reqNamed
      iexists ap
      simp only [Nat.zero_add]
      iframe Hnm Hap
    isplitl [Hdeps HS]
    · rw [List.drop_append_of_le_length Hk]
      iapply BigSepL.bigSepL_append.2
      iframe Hdeps
      iapply BigSepL.bigSepL_singleton.2
      iunfold reqDeposit
      iexists svc, M, S, Φ
      iframe Hpost HS
      ipureintro; exact hsv
    iapply BigSepM.bigSepM_mono (fun _ => answerRes_app L _ _ _) $$ Hans
  imodintro
  iframe Hhalf
  imodintro
  iunfold reqProto
  iexists γ, L ++ [(sm, eb, post, col)]
  iframe Hrpc Hlb
  ipureintro
  refine ⟨?_, by simp; omega, ?_⟩
  · intro r hr
    rcases List.mem_append.1 hr with hr | hr
    · exact hL r hr
    · simp at hr; subst hr; exact ⟨hsm, heb⟩
  · rw [reqsWire_append]; exact List.prefix_refl _

/-- A request kept unsent (its token) was never written. -/
theorem unsent_reqSent (W : RpcWorld GF) (a : GoString) (cn : Nat) (γ : RpcConnNames)
    (o : Option Nat) :
    isRpcConn (Gg := hG.goose_globalGS) W a cn γ ∗ £ 1 ∗ unsent γ o ∗ reqSent γ o ⊢
      |={⊤}=> False := by
  rcases o with _ | s
  · unfold reqSent; iintro ⟨-, -, -, %H⟩; exact H.elim
  iintro ⟨#Hrpc, Hlc, Hun, Hsent⟩
  unfold unsent reqSent
  icases Hun with ⟨%p, %c, %ap, #Hnm, Hap⟩
  icases Hsent with ⟨%L, #Hlb, %Hs⟩
  iunfold isRpcConn at Hrpc
  icases Hrpc with ⟨#Hre, #Hinv⟩
  iinv Hinv with Hi Hclose
  imod lc_fupd_elim_later (E := ⊤ \ ↑connN) $$ Hlc Hi with Hi
  iunfold connInv at Hi
  icases Hi with ⟨%L', %k, %A, Hh', -, -, -, -, Hnamed, -, -⟩
  ihave %Hpre := mono_list_auth_lb_valid _ _ _ _ $$ Hh' Hlb
  obtain ⟨-, Hpre⟩ := Hpre
  have hs : s < L'.length := Nat.lt_of_lt_of_le Hs Hpre.length_le
  obtain ⟨r, hr⟩ : ∃ r, L'[s]? = some r := ⟨L'[s], List.getElem?_eq_getElem hs⟩
  ihave Hr := BigSepL.bigSepL_lookup (Φ := fun i r => reqNamed (Gg := hG.goose_globalGS) γ i r)
    hr $$ Hnamed
  iunfold reqNamed at Hr
  icases Hr with ⟨%ap', #Hnm', Hap'⟩
  icombine Hnm Hnm' gives %Heq
  simp only [Prod.mk.injEq] at Heq
  obtain ⟨-, -, -, rfl⟩ := Heq
  iexfalso
  iapply token_exclusive $$ Hap Hap'

end ghost

end net.rpc
end Perennial
