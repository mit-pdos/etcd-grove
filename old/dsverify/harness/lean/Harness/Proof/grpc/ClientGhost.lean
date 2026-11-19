/-
The ghost lemmas of the grpc model's client (`ClientDefs.lean`): allocating a transport's ghost
state and registering its connection, appending a client frame, parsing an answer frame, the
bound on a call's number, and collecting a call's continuation.
-/
module

public import Harness.Proof.grpc.ClientDefs

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode NetConn
open net.rpc (framesOf frameOf)

namespace google_golang_org.grpc

/-! ## Pure facts -/

theorem cmsgs_snoc (L : List CFrame) (f : CFrame) :
    cmsgs (L ++ [f]) = cmsgs L ++ [f.msg L.length] := by
  simp [cmsgs, List.mapIdx_append]

theorem sint_nat_lt (x : w64) : sint.nat x < 2 ^ 63 := by
  unfold sint.nat; have := BitVec.toInt_lt (x := x); simp at this; omega

theorem cl_prefix_getElem? {A : Type} {L L' : List A} {i : Nat} {r : A} (h : L <+: L')
    (hi : L[i]? = some r) : L'[i]? = some r := by
  obtain ⟨t, rfl⟩ := h
  grind

section ghost
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netConnExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [net.Assumptions] [net.model.Assumptions] [google_golang_org.grpc.Assumptions]

theorem ml_halves {A : Type} [Pos.Countable A] (γ : GName) (l : List A) :
    monoListAuthOwn (GF := GF) γ 1 l ⊣⊢
      monoListAuthOwn γ (1 : Qp).half l ∗ monoListAuthOwn γ (1 : Qp).half l := by
  have := (monoListAuthOwn_fractional (GF := GF) γ l).fractional (1 : Qp).half (1 : Qp).half
  rwa [Qp.half_add_half] at this

/-- Two halves of a mono-list agree, and grow together. -/
theorem ml_halves_update {A : Type} [Pos.Countable A] (γ : GName) {l1 l2 l' : List A}
    (h : l1 <+: l') :
    ⊢ monoListAuthOwn (GF := GF) γ (1 : Qp).half l1 -∗ monoListAuthOwn γ (1 : Qp).half l2 ==∗
      ⌜l1 = l2⌝ ∗ monoListAuthOwn γ (1 : Qp).half l' ∗ monoListAuthOwn γ (1 : Qp).half l' ∗
      monoListLbOwn γ l' := by
  iintro H1 H2
  ihave %Hag := monoListAuthOwn_agree _ _ _ _ _ $$ H1 H2
  obtain ⟨-, rfl⟩ := Hag
  ihave Hf := (ml_halves γ l1).2 $$ [$H1 $H2]
  imod monoListAuthOwn_update l' h $$ Hf with ⟨Hf, #Hlb⟩
  icases (ml_halves γ l').1 $$ Hf with ⟨H1, H2⟩
  imodintro
  iframe
  isplitr
  · ipureintro; rfl
  iexact Hlb

/-- Shutting the transport down (whatever its flag was). -/
theorem sdl_shut (γn : TNames) (sd : Bool) :
    ⊢ monoListAuthOwn (GF := GF) γn.sdl 1 (if sd then [()] else []) ==∗
      monoListAuthOwn γn.sdl 1 [()] ∗ shutLb γn := by
  iintro H
  cases sd <;> simp only [Bool.false_eq_true, ↓reduceIte]
  · imod monoListAuthOwn_update [()] (by simp) $$ H with ⟨H, #Hl⟩
    imodintro; iframe; unfold shutLb; iexact Hl
  · ihave #Hl := monoListLbOwn_get _ _ _ $$ H
    imodintro; iframe; unfold shutLb; iexact Hl

theorem sdl_shut0 (γn : TNames) :
    ⊢ monoListAuthOwn (GF := GF) γn.sdl 1 ([] : List Unit) ==∗
      monoListAuthOwn γn.sdl 1 [()] ∗ shutLb γn := by
  have := sdl_shut (GF := GF) γn false
  simpa using this

/-- The pending map after deleting an entry. -/
theorem pend_delete (γn : TNames) (m : GMap w64 Loc) (sd : Bool) (s : w64) :
    (pendAlive (GF := GF) γn m ∨ (token γn.dead ∗ ⌜m = ∅ ∧ sd = true⌝)) ⊢
      pendAlive γn (GMap.delete s m) ∨ (token γn.dead ∗ ⌜GMap.delete s m = ∅ ∧ sd = true⌝) := by
  iintro (H | ⟨Hd, %h⟩)
  · ileft
    unfold pendAlive
    cases hm : m !! s with
    | none => rw [GMap.delete_notin m s hm]; iexact H
    | some pc =>
      icases (BigSepM.bigSepM_delete (show get? m s = some pc from hm)).1 $$ H with ⟨-, H⟩
      iexact H
  · iright; iframe
    ipureintro
    obtain ⟨rfl, h2⟩ := h
    refine ⟨?_, h2⟩
    exact GMap.delete_notin _ s (GMap.lookup_empty s)

/-- The dialer registers its new connection `cid` (with the end's fresh token): fresh names,
an invariant with no frames, and the dialer's half of the frame list. -/
theorem conn_register (W : GrpcWorld GF) (a : GoString) (cid : w64) :
    ⊢ inv regN (regInv W) -∗ connFresh cid false ={⊤}=∗
      ∃ γ : GConnNames, isGConn W a cid γ ∗
        monoListAuthOwn γ.reqs (1 : Qp).half ([] : List CFrame) := by
  iintro #Hreg Hfr
  imod mono_list_own_alloc (GF := GF) ([] : List CFrame) with ⟨%γr, Hr, -⟩
  imod ghostVar_alloc (GF := GF) (0 : Nat) with ⟨%γk, Hk⟩
  imod ghost_map_alloc_empty (GF := GF) (K := Nat) (V := Option (w64 × GoString × List w8))
    with ⟨%γa, Ha⟩
  icases (ml_halves γr _).1 $$ Hr with ⟨Hr1, Hr2⟩
  icases (ghostVar_split_half γk 1 _).1 $$ Hk with ⟨Hk1, Hk2⟩
  let γ : GConnNames := (γr, γk, γa)
  imod inv_alloc connN ⊤ (connInv W a cid γ) $$ [Hr1 Hk1 Hk2 Ha] with #Hc
  · inext
    unfold connInv
    iexists [], 0, ∅
    iframe
    isplitr
    · ipureintro; simp
    isplitr
    · rw [List.drop_nil]; iapply BigSepL.bigSepL_nil.2; itrivial
    iapply BigSepM.bigSepM_empty.2; itrivial
  iinv Hreg with Hi Hclose
  unfold regInv
  icases Hi with ⟨%M, >HM, >Hfs⟩
  cases hM : M !! cid with
  | some n =>
    icases (BigSepM.bigSepM_delete (show get? M cid = some n from hM)).1 $$ Hfs with ⟨Hf2, -⟩
    iexfalso
    iapply connFresh_excl cid false
    iframe
  | none =>
    imod ghost_map_insert_persist cid γ hM $$ HM with ⟨HM, #He⟩
    imod Hclose $$ [HM Hfs Hfr] with -
    · inext
      iexists M.insert cid γ
      iframe
      iapply (BigSepM.bigSepM_insert (show get? M cid = none from hM)).2
      iframe
    imodintro
    iexists γ
    unfold isGConn regElem
    iframe
    iframe #

/-- A new transport's ghost state, over its connection's names `γ` (no frames yet, the dialer
holding its half). -/
theorem transport_alloc (γ : GConnNames) :
    ⊢ monoListAuthOwn (GF := GF) γ.reqs (1 : Qp).half ([] : List CFrame) ={⊤}=∗
      ∃ γn : TNames, ⌜γn.conn = γ⌝ ∗ inv tN (tInv γn) ∗
        monoListAuthOwn γn.cl (1 : Qp).half ([] : List CFrame) ∗
        monoListAuthOwn γn.sdl 1 ([] : List Unit) ∗ token γn.dead := by
  iintro Hreqs
  imod mono_list_own_alloc (GF := GF) ([] : List CFrame) with ⟨%γcl, Hcl, -⟩
  imod mono_list_own_alloc (GF := GF) ([] : List Unit) with ⟨%γs, Hs, -⟩
  imod token_alloc (GF := GF) with ⟨%γd, Hd⟩
  icases (ml_halves γcl _).1 $$ Hcl with ⟨Hcl1, Hcl2⟩
  let γn : TNames := ⟨γ, γcl, γs, γd⟩
  imod inv_alloc tN ⊤ (tInv γn) $$ [Hreqs Hcl1] with #Hinv
  · inext
    unfold tInv
    iexists []
    iframe
    ipureintro; simp
  imodintro
  iexists γn
  iframe
  isplitr
  · ipureintro; rfl
  iexact Hinv

/-- Appending client frame `f` (the holder of `sending`, while up, with fewer than `2 ^ 64 - 1`
frames): the connection's list and the transport's copy grow, the frame's deposit goes to the
connection. -/
theorem append_frame (W : GrpcWorld GF) (a : GoString) (cid : w64) (γn : TNames)
    (L : List CFrame) (f : CFrame) (hL : (W64 L.length : w64) ≠ W64 18446744073709551615) :
    ⊢ inv tN (tInv γn) -∗ isGConn W a cid γn.conn -∗
      monoListAuthOwn γn.cl (1 : Qp).half L -∗ frameDeposit W a f ={⊤}=∗
      ⌜L.length + 1 < 2 ^ 64⌝ ∗
      monoListAuthOwn γn.cl (1 : Qp).half (L ++ [f]) ∗ monoListLbOwn γn.conn.reqs (L ++ [f]) := by
  unfold isGConn
  iintro #Hti ⟨-, #Hconn⟩ Hcl Hdep
  iinv Hti with Hi Hclose1
  unfold tInv
  icases Hi with ⟨%L1, >Hreqs, >Hcl1, >%HL1⟩
  ihave %Hag0 := monoListAuthOwn_agree _ _ _ _ _ $$ Hcl Hcl1
  obtain ⟨-, rfl⟩ := Hag0
  have hL' : L.length + 1 < 2 ^ 64 := by
    rcases Nat.lt_or_ge (L.length + 1) (2 ^ 64) with h | h
    · exact h
    · exfalso; apply hL
      have : L.length = 2 ^ 64 - 1 := by omega
      rw [this]; rfl
  iinv Hconn with Hj Hclose2
  · exact mask_ndot_ne' grpcN "conn" "transport" (by decide)
  unfold connInv
  icases Hj with ⟨%L2, %k, %A, >Hreqs2, Hctr, HA, Hclaim, >%Hk, Hdeps, Hans⟩
  imod ml_halves_update γn.cl (List.prefix_append L [f]) $$ Hcl Hcl1 with ⟨-, Hcl, Hcl1, -⟩
  imod ml_halves_update γn.conn.reqs (List.prefix_append L [f]) $$ Hreqs Hreqs2
    with ⟨%H2, Hreqs, Hreqs2, #Hlb⟩
  subst H2
  imod Hclose2 $$ [Hreqs2 Hctr HA Hclaim Hdeps Hans Hdep] with -
  · inext
    iexists L ++ [f], k, A
    iframe
    isplitr
    · ipureintro
      refine ⟨by simp; omega, fun i hi => ?_⟩
      obtain ⟨h1, fm, b, post, col, h2⟩ := Hk.2 i hi
      refine ⟨h1, fm, b, post, col, ?_⟩
      exact cl_prefix_getElem? (List.prefix_append L [f]) h2
    isplitl [Hdeps Hdep]
    · rw [List.drop_append_of_le_length Hk.1]
      iapply BigSepL.bigSepL_snoc.2
      iframe
    · iapply BigSepM.bigSepM_mono (fun {i o} hio => ?_) $$ Hans
      unfold answerRes
      rcases o with _ | ⟨code, msg, rep⟩
      · exact .rfl
      · iintro ⟨%fm, %b, %post, %col, %hL, H⟩
        iexists fm, b, post, col
        iframe
        ipureintro
        exact ⟨cl_prefix_getElem? (List.prefix_append L [f]) hL.1, hL.2⟩
  imod Hclose1 $$ [Hreqs Hcl1] with -
  · inext
    iexists L ++ [f]
    iframe
    ipureintro; simp; omega
  imodintro
  iframe
  isplitr
  · ipureintro; exact hL'
  iexact Hlb

/-- An answer's call number is below `2 ^ 64` (from the connection's invariant: an answered
call is one of its frames, and the transport's invariant bounds their number). -/
theorem ans_bound (W : GrpcWorld GF) (a : GoString) (cid : w64) (γn : TNames) (i : Nat)
    (x : w64 × GoString × List w8) :
    ⊢ inv tN (tInv γn) -∗ isGConn W a cid γn.conn -∗
      ghostMapElem γn.conn.ans i .discard (some x) ={⊤}=∗ ⌜i < 2 ^ 64⌝ := by
  unfold isGConn
  iintro #Hti ⟨-, #Hconn⟩ #Hel
  iinv Hti with Hi Hclose1
  unfold tInv
  icases Hi with ⟨%L1, >Hreqs, >Hcl1, >%HL1⟩
  iinv Hconn with Hj Hclose2
  · exact mask_ndot_ne' grpcN "conn" "transport" (by decide)
  unfold connInv
  icases Hj with ⟨%L2, %k, %A, >Hreqs2, Hctr, >HA, Hclaim, >%Hk, Hdeps, Hans⟩
  ihave %HAi := ghost_map_lookup $$ HA Hel
  ihave %Hag := monoListAuthOwn_agree _ _ _ _ _ $$ Hreqs Hreqs2
  obtain ⟨-, rfl⟩ := Hag
  have hi := (Hk.2 i (by show (A.lookup i).isSome = true; rw [HAi]; rfl)).1
  imod Hclose2 $$ [Hreqs2 Hctr HA Hclaim Hdeps Hans] with -
  · inext; iexists L1, k, A; iframe; ipureintro; exact Hk
  imod Hclose1 $$ [Hreqs Hcl1] with -
  · inext; iexists L1; iframe; ipureintro; exact HL1
  imodintro
  ipureintro; omega

/-- The reader's next frame `p` after the answer frames `Q` it read: the payload of an answer of
the connection, with its persistent record. -/
theorem resp_parse (W : GrpcWorld GF) (a : GoString) (cid : w64) (Q : List (List w8))
    (p : List w8) (hQ : ∀ q ∈ Q, q.length < 2 ^ 63) (hp : p.length < 2 ^ 63) :
    recvTok cid false (respProto W a) (framesOf Q ++ frameOf p) ⊢
      recvTok cid false (respProto W a) (framesOf Q ++ frameOf p) ∗
      ∃ (γ : GConnNames) (x : Ans), isGConn W a cid γ ∗
        ghostMapElem γ.ans x.1 .discard (some x.2) ∗ ⌜respMsg x = p⌝ := by
  iintro H
  ihave ⟨H, Hp⟩ := recvTok_proto cid false _ _ $$ H
  iframe H
  unfold protoPrefix
  icases Hp with (%Hnil | ⟨%ext, %Hext, #HP⟩)
  · exfalso
    have := congrArg List.length Hnil
    simp [net.rpc.frameOf_length] at this
  unfold respProto
  icases HP with ⟨%γ, %Rs, #Hc, #HRs, %HRsp⟩
  obtain ⟨-, hb, hpre⟩ := HRsp
  obtain ⟨-, hget⟩ := net.rpc.framesOf_next hQ hb hp (Hext.trans hpre)
  rw [List.getElem?_map] at hget
  cases hR : Rs[Q.length]? with
  | none => rw [hR] at hget; cases hget
  | some x =>
    rw [hR] at hget
    iexists γ, x
    iframe Hc
    isplitl
    · iapply BigSepL.bigSepL_mem (List.mem_of_getElem? hR) $$ HRs
    ipureintro
    exact Option.some.inj hget

/-- The names of a connection are unique. -/
theorem cl_isGConn_agree (W : GrpcWorld GF) (a : GoString) (cid : w64) (γ γ' : GConnNames) :
    ⊢ isGConn W a cid γ -∗ isGConn W a cid γ' -∗ ⌜γ = γ'⌝ := by
  iintro Hc Hc'
  unfold isGConn regElem
  icases Hc with ⟨Hr, -⟩
  icases Hc' with ⟨Hr', -⟩
  iapply ghostMapElem_agree _ _ _ _ _ _ $$ Hr Hr'

/-- The reader collects the answer `(code, msg, rep)` of call `i` (frame `L[i]`) with the call's
collection token: for status `OK`, the call's `Φ rep`. -/
theorem collect (W : GrpcWorld GF) (a : GoString) (cid : w64) (γ : GConnNames)
    (L : List CFrame) (i : Nat) (fm : GoString) (b : List w8) (post col : GName) (code : w64)
    (msg : GoString) (rep : List w8) (Φ : List w8 → IProp GF)
    (hr : L[i]? = some (.call fm b post col)) :
    ⊢ isGConn W a cid γ -∗ monoListLbOwn γ.reqs L -∗
      ghostMapElem γ.ans i .discard (some (code, msg, rep)) -∗ token col -∗
      savedPredOwn post .discard Φ -∗ £ 1 -∗ £ 1
      ={⊤}=∗ (if code = W64 0 then Φ rep else iprop(True)) ∗
        ⌜code = W64 0 ∨ uint.Z code < 2 ^ 32⌝ := by
  unfold isGConn
  iintro ⟨-, #Hconn⟩ #HLr #Ha Htok #Hpost Hlc1 Hlc2
  iinv Hconn with Hj Hclose
  imod lc_fupd_elim_later $$ Hlc1 Hj with Hj
  unfold connInv
  icases Hj with ⟨%L', %k, %A, Hreqs, Hctr, HA, Hclaim, %Hk, Hdeps, Hans⟩
  ihave %HA := ghost_map_lookup $$ HA Ha
  ihave %HLrL := mono_list_auth_lb_valid _ _ _ _ $$ Hreqs HLr
  have hLi : L'[i]? = some (.call fm b post col) := cl_prefix_getElem? HLrL.2 hr
  icases (BigSepM.bigSepM_delete (show get? A i = some (some (code, msg, rep)) from HA)).1 $$ Hans
    with ⟨Hai, Hans⟩
  unfold answerRes
  icases Hai with ⟨%fm', %b', %post', %col', %hr'', Hesc⟩
  obtain ⟨hr', hcode⟩ := hr''
  rw [hLi] at hr'
  cases hr'
  by_cases hc : code = W64 0
  · subst hc
    rw [if_pos rfl]
    icases Hesc with (Hesc | Htok2)
    rotate_left
    · iexfalso; iapply token_exclusive $$ Htok Htok2
    imod Hclose $$ [Hreqs Hctr HA Hclaim Hdeps Hans Htok] with -
    · inext
      iexists L', k, A
      iframe
      isplitr
      · ipureintro; exact Hk
      iapply (BigSepM.bigSepM_delete (show get? A i = some (some (W64 0, msg, rep)) from HA)).2
      iframe
      dsimp only
      iexists fm, b, post, col
      isplitr
      · ipureintro; exact ⟨hLi, hcode⟩
      iright; iexact Htok
    unfold replyEscrow
    icases Hesc with ⟨%Φ', #Hpost', HΦ'⟩
    ihave Hag := saved_pred_agree _ _ _ Φ Φ' rep $$ Hpost Hpost'
    imod lc_fupd_elim_later $$ Hlc2 Hag with #Hag
    imodintro
    simp only [↓reduceIte]
    isplitl
    · iapply internal_eq_rewrite_wand $$ Hag HΦ'
    · ipureintro; simp
  · rw [if_neg hc] at *
    simp only [hc, ↓reduceIte]
    imod Hclose $$ [Hreqs Hctr HA Hclaim Hdeps Hans Hesc] with -
    · inext
      iexists L', k, A
      iframe
      isplitr
      · ipureintro; exact Hk
      iapply (BigSepM.bigSepM_delete (show get? A i = some (some (code, msg, rep)) from HA)).2
      iframe
      dsimp only
      iexists fm, b, post, col
      rw [if_neg hc]
      isplitr
      · ipureintro; exact ⟨hLi, hcode⟩
      iexact Hesc
    imodintro; isplitl; itrivial; ipureintro; simp only [hc, false_or] at hcode ⊢; exact hcode

end ghost

end google_golang_org.grpc

end Perennial
