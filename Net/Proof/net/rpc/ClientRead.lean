/-
The reader's ghost lemmas (`Client.input`): what a response it read answers (`resp_hdr`, after a
header frame; `resp_body`, after its body frame too), and trading a pending call's collection
token for its answer's continuation (`ans_trade`, which also shows the request was written,
`reqSent`). Over the protocol of `Proto.lean`.
-/
module

public import Net.Proof.net.rpc.ClientGhost

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace net.rpc

theorem frameOf_ne_nil (p : List w8) : frameOf p ≠ [] := by
  intro h; have := frameOf_length p; rw [h, List.length_nil] at this; omega

section ghost
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : net.rpc.Assumptions] [field_sem : net.FieldAssumptions]
variable [π : NetProtoGS]

attribute [local instance] GooseGlobalGS.gooseInvGS

/-- The answers a reader's bytes `R` meet (their protocol fact, `recvTok_proto`): some `Rs` of the
connection `γ`, with their elements. -/
theorem resp_of_read (W : RpcWorld GF) (a : GoString) (cn : Nat) (γ : RpcConnNames)
    (R : List w8) (hR : R ≠ []) :
    isRpcConn (Gg := hG.goose_globalGS) W a cn γ ∗
      protoPrefix (respProto (Gg := hG.goose_globalGS) W a) cn R ⊢
    ∃ Rs : List Ans, ⌜(∀ x ∈ Rs, ansOk x) ∧ R <+: W.hsAns a ++ respsWire Rs⌝ ∗
      [∗list] x ∈ Rs, ghostMapElem γ.ans x.idx .discard (some (x.msg, x.reply)) := by
  iintro ⟨#Hrpc, #Hpp⟩
  iunfold protoPrefix at Hpp
  icases Hpp with (%Hnil | ⟨%ext, %Hext, #HP⟩)
  · exact absurd Hnil hR
  iunfold respProto at HP
  icases HP with ⟨%γ', %Rs, #Hrpc', #Hels, ⟨%HRs, %Hpre⟩, -⟩
  iunfold isRpcConn at Hrpc Hrpc'
  icases Hrpc with ⟨#He, -⟩
  icases Hrpc' with ⟨#He', -⟩
  iunfold regElem at He He'
  ihave %Hg := ghostMapElem_agree _ _ _ _ _ _ $$ He He'
  subst Hg
  iexists Rs
  iframe Hels
  ipureintro; exact ⟨HRs, Hext.trans Hpre⟩

/-- After the frames of the answers `C` and a header frame `hdr`: the answer it heads. -/
theorem resp_hdr (W : RpcWorld GF) (a : GoString) (cn : Nat) (γ : RpcConnNames) (C : List Ans)
    (hdr : List w8) (hC : ∀ x ∈ C, ansOk x) (hh : hdr.length < 2 ^ 63) :
    isRpcConn (Gg := hG.goose_globalGS) W a cn γ ∗
      protoPrefix (respProto (Gg := hG.goose_globalGS) W a) cn
        (W.hsAns a ++ framesOf (C.flatMap ansPls) ++ frameOf hdr) ⊢
    ∃ x : Ans, ⌜(ansPls x)[0]? = some hdr ∧ ansOk x⌝ ∗
      ghostMapElem γ.ans x.idx .discard (some (x.msg, x.reply)) := by
  iintro H
  icases resp_of_read W a cn γ _ (by simp [frameOf_ne_nil]) $$ H with ⟨%Rs, ⟨%HRs, %Hpre⟩, #Hels⟩
  obtain ⟨x, hx, hx0⟩ := ans_next C Rs [] hdr [] 0 (by omega) rfl hC HRs (by simp) hh
    (by simpa [List.append_assoc, List.prefix_append_right_inj] using Hpre)
  iexists x
  ihave Hx := BigSepL.bigSepL_lookup
    (Φ := fun _ (x : Ans) => ghostMapElem (GF := GF) γ.ans x.idx .discard (some (x.msg, x.reply)))
    hx $$ Hels
  iframe Hx
  ipureintro; exact ⟨hx0, HRs x (List.mem_of_getElem? hx)⟩

/-- After the frames of the answers `C`, a header frame `hdr` and a body frame `b`: the answer
they are. -/
theorem resp_body (W : RpcWorld GF) (a : GoString) (cn : Nat) (γ : RpcConnNames) (C : List Ans)
    (hdr b : List w8) (hC : ∀ x ∈ C, ansOk x) (hh : hdr.length < 2 ^ 63)
    (hb : b.length < 2 ^ 63) :
    isRpcConn (Gg := hG.goose_globalGS) W a cn γ ∗
      protoPrefix (respProto (Gg := hG.goose_globalGS) W a) cn
        (W.hsAns a ++ framesOf (C.flatMap ansPls) ++ frameOf hdr ++ frameOf b) ⊢
    ∃ y : Ans, ⌜ansPls y = [hdr, b] ∧ ansOk y⌝ ∗
      ghostMapElem γ.ans y.idx .discard (some (y.msg, y.reply)) := by
  iintro H
  icases resp_of_read W a cn γ _ (by simp [frameOf_ne_nil]) $$ H with ⟨%Rs, ⟨%HRs, %Hpre⟩, #Hels⟩
  obtain ⟨x, hx, hx0⟩ := ans_next C Rs [] hdr (frameOf b) 0 (by omega) rfl hC HRs (by simp) hh
    (by simpa [List.append_assoc, List.prefix_append_right_inj] using Hpre)
  obtain ⟨x', hx', hx1⟩ := ans_next C Rs [hdr] b [] 1 (by omega) rfl hC HRs (by simpa using hh)
    hb (by simpa [framesOf_append, framesOf_cons, framesOf_nil, List.append_assoc,
      List.prefix_append_right_inj] using Hpre)
  rw [hx] at hx'
  cases hx'
  iexists x
  ihave Hx := BigSepL.bigSepL_lookup
    (Φ := fun _ (x : Ans) => ghostMapElem (GF := GF) γ.ans x.idx .discard (some (x.msg, x.reply)))
    hx $$ Hels
  iframe Hx
  ipureintro
  refine ⟨?_, HRs x (List.mem_of_getElem? hx)⟩
  simp only [ansPls, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.some.injEq] at hx0 hx1
  simp only [ansPls, hx0, hx1]

/-- The reader trades a pending call's collection token `col` (its names recorded for the request
`i`) for the answer's continuation `Φ reply msg`; the request was written. -/
theorem ans_trade (W : RpcWorld GF) (a : GoString) (cn : Nat) (γ : RpcConnNames) (i : Nat)
    (msg : GoString) (reply : List w8) (post col ap : GName)
    (Φ : List w8 → GoString → IProp GF) :
    isRpcConn (Gg := hG.goose_globalGS) W a cn γ ∗ £ 1 ∗ £ 1 ∗
      ghostMapElem γ.ans i .discard (some (msg, reply)) ∗ token col ∗
      ghostMapElem γ.nm i .discard (post, col, ap) ∗
      savedPredOwn post .discard (fun p : List w8 × GoString => Φ p.1 p.2) ⊢
    |={⊤}=> Φ reply msg ∗ reqSent γ (some i) := by
  iintro ⟨#Hrpc, Hlc1, Hlc2, #Hans, Hcol, #Hnm, #Hpost⟩
  iunfold isRpcConn at Hrpc
  icases Hrpc with ⟨#Hre, #Hinv⟩
  iinv Hinv with Hi Hclose
  imod lc_fupd_elim_later (E := ⊤ \ ↑connN) $$ Hlc1 Hi with Hi
  iunfold connInv at Hi
  icases Hi with ⟨%L, %k, %A, Hh, Hctr, HA, Hfr, %Hk, Hnamed, Hdeps, Hansm⟩
  ihave %HAi := ghost_map_lookup $$ HA Hans
  icases (BigSepM.bigSepM_lookup_acc (Φ := fun i o => answerRes (Gg := hG.goose_globalGS) L i o)
    (by rw [gmap_get?_eq]; exact HAi)).1 $$ Hansm with ⟨Hres, Hback⟩
  iunfold answerRes at Hres
  icases Hres with ⟨%r, %Hr, Hesc⟩
  icases (BigSepL.bigSepL_lookup_acc (Φ := fun i r => reqNamed (Gg := hG.goose_globalGS) γ i r) Hr).1 $$ Hnamed
    with ⟨Hnr, Hnback⟩
  iunfold reqNamed at Hnr
  icases Hnr with ⟨%ap', #Hnm', Hap'⟩
  ihave %Heq := ghostMapElem_agree _ _ _ _ _ _ $$ Hnm Hnm'
  simp only [Prod.mk.injEq] at Heq
  obtain ⟨rfl, rfl, rfl⟩ := Heq
  ihave #Hlb := monoListLbOwn_get $$ Hh
  icases Hesc with (Hesc | Htk)
  rotate_left
  · iexfalso; iapply token_exclusive $$ Hcol Htk
  iunfold replyEscrow at Hesc
  icases Hesc with ⟨%Φ', #Hpost', HΦ'⟩
  imod Hclose $$ [Hh Hctr HA Hfr Hdeps Hback Hnback Hap' Hcol] with -
  · inext
    iunfold connInv
    iexists L, k, A
    iframe Hh Hctr HA Hfr Hdeps
    isplitr
    · ipureintro; exact Hk
    isplitl [Hnback Hap']
    · ihave Hnr : reqNamed (Gg := hG.goose_globalGS) γ i r $$ [Hap']
      · iunfold reqNamed
        iexists _
        iframe Hnm Hap'
      ihave Hnl := Hnback $$ %r Hnr
      obtain ⟨hi, hri⟩ := List.getElem?_eq_some_iff.1 Hr
      have hset : L.set i r = L := hri ▸ List.set_getElem_self hi
      rw [hset]
      iexact Hnl
    iapply Hback
    iunfold answerRes
    iexists r
    isplitr
    · ipureintro; exact Hr
    iright; iexact Hcol
  ihave Hag := saved_pred_agree _ _ _ (fun p : List w8 × GoString => Φ p.1 p.2)
    (fun p : List w8 × GoString => Φ' p.1 p.2) (reply, msg) $$ Hpost Hpost'
  imod lc_fupd_elim_later $$ Hlc2 Hag with #Hag
  imodintro
  isplitl [HΦ']
  · iapply internal_eq_rewrite_wand $$ Hag HΦ'
  unfold reqSent
  iexists L
  iframe Hlb
  ipureintro
  exact (List.getElem?_eq_some_iff.1 Hr).1

end ghost

end net.rpc
end Perennial
