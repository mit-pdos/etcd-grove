/-
The grpc server's ghost lemmas over a connection's invariant (`connInv`, `Proto.lean`), and the
invariant of a served connection's writer (`serverConn`'s `mu`), as the net/rpc model's
(`Harness/Proof/net/rpc/ServerGhost.lean`).

* `req_parse`: a frame the reader reads after the frames of its first `k` client frames is the
  payload of client frame `k` of the connection (from the dialer's protocol).
* `claim_role`: with the acceptor's fresh token, the reader claims its half of `ctr` (at `0`).
* `take_call`: the reader takes call `k` once: its deposit, and `ans k ↦ none` (own);
  `skip_cancel`: it passes cancellation `k`.
* `answer`: the run answers call `k` with `(code, msg, reply)`: `ans k ↦□ some (...)`; for status
  OK the continuation of the reply goes to the invariant (`replyEscrow`).
* `respDone W a cid σ Wb`: the bytes `Wb` written so far are frames of answers `Rs`, each with its
  persistent answer and its writer token `σ ↪ i`; `resp_next` extends it by one answer.
-/
module

public import Harness.Proof.grpc.Wire

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode NetConn
open net.rpc (frameOf framesOf framesOf_next framesOf_append frameOf_length)

namespace google_golang_org.grpc

/-! ## Pure facts -/

theorem prefix_getElem? {L L' : List CFrame} {i : Nat} {r : CFrame} (h : L <+: L')
    (hi : L[i]? = some r) : L'[i]? = some r := by
  obtain ⟨t, rfl⟩ := h
  grind

theorem cmsgs_getElem? (L : List CFrame) (i : Nat) :
    (cmsgs L)[i]? = L[i]?.map (fun f => f.msg i) := by
  unfold cmsgs; simp [List.getElem?_mapIdx]

/-! ## Ghost lemmas -/

section ghost
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netConnExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

attribute [local instance] GooseGlobalGS.gooseInvGS

instance isGConn_persistent (W : GrpcWorld GF) (a : GoString) (cid : w64) (γ : GConnNames) :
    Persistent (isGConn W a cid γ) := by
  unfold isGConn regElem; infer_instance

instance respProto_persistent (W : GrpcWorld GF) (a : GoString) (cid : w64) (bs : List w8) :
    Persistent (respProto W a cid bs) := by
  unfold respProto; infer_instance

instance reqProto_persistent (W : GrpcWorld GF) (a : GoString) (cid : w64) (bs : List w8) :
    Persistent (reqProto W a cid bs) := by
  unfold reqProto; infer_instance

instance grpcAddr_persistent (W : GrpcWorld GF) (a : GoString) :
    Persistent (grpcAddr W a) := by
  unfold grpcAddr; infer_instance

/-- A mono-list authority and a lower bound: the bound is a prefix. -/
theorem auth_lb_prefix (γ : GName) (q : Qp) (l1 l2 : List CFrame) :
    monoListAuthOwn (GF := GF) γ q l1 ∗ monoListLbOwn γ l2 ⊢
      (monoListAuthOwn γ q l1 ∗ monoListLbOwn γ l2) ∗ ⌜l2 <+: l1⌝ :=
  persistent_entails_left (Q := iprop(⌜l2 <+: l1⌝ : IProp GF)) (by
    iintro ⟨Ha, Hb⟩
    icases mono_list_auth_lb_valid γ q l1 l2 $$ Ha Hb with %h
    ipureintro; exact h.2)

theorem claim_role (W : GrpcWorld GF) (a : GoString) (cid : w64) (γ : GConnNames)
    (E : CoPset) (hE : ↑connN ⊆ E) :
    ⊢ inv connN (connInv W a cid γ) -∗ connFresh cid true ={E}=∗
      ghostVar γ.ctr (1 : Qp).half 0 := by
  iintro #Hinv Hfr
  unfold connInv
  iinv Hinv with ⟨%L, %k, %A, >Hreqs, >Hctr, >Hans, >Hrole, >%Hk, Hdeps, Hres⟩ Hclose
  icases Hrole with (H0 | Hfr2)
  · imod Hclose $$ [Hreqs Hctr Hans Hfr Hdeps Hres] with -
    · inext; iexists L, k, A; iframe; ipureintro; exact Hk
    imodintro; iexact H0
  · iexfalso
    iapply connFresh_excl cid true
    iframe

theorem take_call (W : GrpcWorld GF) (a : GoString) (cid : w64) (γ : GConnNames) (k : Nat)
    (L : List CFrame) (fm : GoString) (b : List w8) (post col : GName)
    (hr : L[k]? = some (.call fm b post col)) (E : CoPset) (hE : ↑connN ⊆ E) :
    ⊢ inv connN (connInv W a cid γ) -∗ ghostVar γ.ctr (1 : Qp).half k -∗
      monoListLbOwn γ.reqs L ={E}=∗
      ghostVar γ.ctr (1 : Qp).half (k + 1) ∗ ▷ frameDeposit W a (.call fm b post col) ∗
      ghostMapElem γ.ans k (DFrac.own 1) (none : Option (w64 × GoString × List w8)) := by
  iintro #Hinv Hmy #Hlb
  unfold connInv
  iinv Hinv with ⟨%L', %k', %A, >Hreqs, >Hctr, >Hans, >Hrole, >%Hk, Hdeps, Hres⟩ Hclose
  icombine Hctr Hmy gives %Heq
  obtain ⟨_, Heq⟩ := Heq
  subst Heq
  ihave ⟨⟨Hreqs, -⟩, %Hpre⟩ := auth_lb_prefix γ.reqs _ L' L $$ [Hreqs Hlb]
  · iframe Hreqs Hlb
  have hr' := prefix_getElem? Hpre hr
  have hkL : k' < L'.length := (List.getElem?_eq_some_iff.1 hr').1
  have hdrop : L'.drop k' = CFrame.call fm b post col :: L'.drop (k' + 1) := by
    rw [List.drop_eq_getElem_cons hkL]
    congr
    exact (List.getElem?_eq_some_iff.1 hr').2
  rw [hdrop]
  icases Hdeps with ⟨Hdep, Hdeps⟩
  have hAk : A.lookup k' = none := by
    cases h : A.lookup k' with
    | none => rfl
    | some v =>
      have := (Hk.2 k' (by show (A.lookup k').isSome = true; simp [h])).1
      omega
  imod ghost_map_insert k' (none : Option (w64 × GoString × List w8)) hAk $$ Hans with ⟨Hans, Hel⟩
  imod ghostVar_update_halves (k' + 1) γ.ctr k' k' $$ Hctr Hmy with ⟨Hctr, Hmy⟩
  imod Hclose $$ [Hreqs Hctr Hans Hrole Hdeps Hres] with -
  · inext
    iexists L', k' + 1, A.insert k' none
    iframe Hreqs Hctr Hans Hrole Hdeps
    isplitr
    · ipureintro
      refine ⟨hkL, fun i hi => ?_⟩
      by_cases hik : i = k'
      · subst hik; exact ⟨by omega, fm, b, post, col, hr'⟩
      · have : (A !! i).isSome := by
          rwa [GMap.lookup_insert_ne _ _ (Ne.symm hik)] at hi
        have := Hk.2 i this
        exact ⟨by omega, this.2⟩
    · iapply (BigSepM.bigSepM_insert (by rw [gmap_get?_eq]; exact hAk)).2
      iframe Hres
      unfold answerRes
      itrivial
  imodintro
  iframe Hmy Hdep Hel

theorem skip_cancel (W : GrpcWorld GF) (a : GoString) (cid : w64) (γ : GConnNames) (k : Nat)
    (L : List CFrame) (t : w64) (hr : L[k]? = some (.cancel t)) (E : CoPset)
    (hE : ↑connN ⊆ E) :
    ⊢ inv connN (connInv W a cid γ) -∗ ghostVar γ.ctr (1 : Qp).half k -∗
      monoListLbOwn γ.reqs L ={E}=∗ ghostVar γ.ctr (1 : Qp).half (k + 1) := by
  iintro #Hinv Hmy #Hlb
  unfold connInv
  iinv Hinv with ⟨%L', %k', %A, >Hreqs, >Hctr, >Hans, >Hrole, >%Hk, Hdeps, Hres⟩ Hclose
  icombine Hctr Hmy gives %Heq
  obtain ⟨_, Heq⟩ := Heq
  subst Heq
  ihave ⟨⟨Hreqs, -⟩, %Hpre⟩ := auth_lb_prefix γ.reqs _ L' L $$ [Hreqs Hlb]
  · iframe Hreqs Hlb
  have hr' := prefix_getElem? Hpre hr
  have hkL : k' < L'.length := (List.getElem?_eq_some_iff.1 hr').1
  have hdrop : L'.drop k' = CFrame.cancel t :: L'.drop (k' + 1) := by
    rw [List.drop_eq_getElem_cons hkL]
    congr
    exact (List.getElem?_eq_some_iff.1 hr').2
  rw [hdrop]
  icases Hdeps with ⟨-, Hdeps⟩
  imod ghostVar_update_halves (k' + 1) γ.ctr k' k' $$ Hctr Hmy with ⟨Hctr, Hmy⟩
  imod Hclose $$ [Hreqs Hctr Hans Hrole Hdeps Hres] with -
  · inext
    iexists L', k' + 1, A
    iframe Hreqs Hctr Hans Hrole Hdeps Hres
    ipureintro
    refine ⟨hkL, fun i hi => ?_⟩
    have := Hk.2 i hi
    exact ⟨by omega, this.2⟩
  imodintro
  iexact Hmy

/-- What the run of call `k` escrows with its answer `(code, msg, reply)`. -/
def answerEscrow (post : GName) (code : w64) (reply : List w8) : IProp GF :=
  if code = W64 0 then replyEscrow post reply else iprop(True)

theorem answer_aux (post : GName) (code : w64) (reply : List w8) :
    answerEscrow (GF := GF) post code reply ⊢
      (if code = W64 0 then replyEscrow post reply else iprop(True)) := by
  unfold answerEscrow; iintro H; iexact H

theorem answer (W : GrpcWorld GF) (a : GoString) (cid : w64) (γ : GConnNames) (k : Nat)
    (L : List CFrame) (fm : GoString) (b : List w8) (post col : GName) (code : w64)
    (msg : GoString) (reply : List w8) (hr : L[k]? = some (.call fm b post col))
    (hcode : code = W64 0 ∨ uint.Z code < 2 ^ 32) (E : CoPset) (hE : ↑connN ⊆ E) :
    ⊢ inv connN (connInv W a cid γ) -∗
      ghostMapElem γ.ans k (DFrac.own 1) (none : Option (w64 × GoString × List w8)) -∗
      monoListLbOwn γ.reqs L -∗ answerEscrow post code reply ={E}=∗
      ghostMapElem γ.ans k .discard (some (code, msg, reply)) := by
  iintro #Hinv Hel #Hlb Hesc
  ihave Hesc := answer_aux post code reply $$ Hesc
  unfold connInv
  iinv Hinv with ⟨%L', %k', %A, >Hreqs, >Hctr, >Hans, >Hrole, >%Hk, Hdeps, Hres⟩ Hclose
  icombine Hel Hans gives %HA
  ihave ⟨⟨Hreqs, -⟩, %Hpre⟩ := auth_lb_prefix γ.reqs _ L' L $$ [Hreqs Hlb]
  · iframe Hreqs Hlb
  have hr' := prefix_getElem? Hpre hr
  imod ghost_map_update (some (code, msg, reply)) $$ Hans Hel with ⟨Hans, Hel⟩
  imod ghostMapElem_persist $$ Hel with #Hel
  imod Hclose $$ [Hreqs Hctr Hans Hrole Hdeps Hres Hesc] with -
  · inext
    iexists L', k', A.insert k (some (code, msg, reply))
    iframe Hreqs Hctr Hans Hrole Hdeps
    isplitr
    · ipureintro
      refine ⟨Hk.1, fun i hi => ?_⟩
      by_cases hik : i = k
      · subst hik; exact Hk.2 i (by show (A.lookup i).isSome = true; simp [HA])
      · exact Hk.2 i (by rwa [GMap.lookup_insert_ne _ _ (Ne.symm hik)] at hi)
    · ihave ⟨-, Hback⟩ := BigSepM.bigSepM_insert_acc (by rw [gmap_get?_eq]; exact HA) $$ Hres
      iapply Hback
      unfold answerRes
      iexists fm, b, post, col
      isplitr
      · ipureintro; exact ⟨hr', hcode⟩
      ileft
      iexact Hesc
  imodintro
  iexact Hel

/-- A frame the reader reads after the frames `qs` of its first client frames is the payload of
the connection's next client frame. -/
theorem req_parse (W : GrpcWorld GF) (a : GoString) (cid : w64) (qs : List (List w8))
    (p : List w8) (hqs : ∀ q ∈ qs, q.length < 2 ^ 63) (hp : p.length < 2 ^ 63) :
    recvTok cid true (reqProto W a) (framesOf qs ++ frameOf p) ⊢
      recvTok cid true (reqProto W a) (framesOf qs ++ frameOf p) ∗
      ∃ (γ : GConnNames) (L : List CFrame) (f : CFrame), isGConn W a cid γ ∗
        monoListLbOwn γ.reqs L ∗ ⌜L[qs.length]? = some f ∧ f.msg qs.length = p⌝ := by
  iintro H
  ihave ⟨H, Hp⟩ := recvTok_proto cid true _ _ $$ H
  iframe H
  unfold protoPrefix
  icases Hp with (%Hnil | ⟨%ext, %Hext, #HP⟩)
  · exfalso
    have := congrArg List.length Hnil
    simp [frameOf_length] at this
  unfold reqProto
  icases HP with ⟨%γ, %L, #Hc, #Hlb, %Hbd⟩
  have h1 : framesOf qs ++ frameOf p <+: framesOf (cmsgs L) := Hext.trans Hbd.2
  obtain ⟨_, hget⟩ := framesOf_next hqs Hbd.1 hp h1
  rw [cmsgs_getElem?] at hget
  cases hL : L[qs.length]? with
  | none => rw [hL] at hget; cases hget
  | some f =>
    rw [hL] at hget
    iexists γ, L, f
    iframe Hc Hlb
    ipureintro
    exact ⟨hL, Option.some.inj hget⟩

/-- The response bytes `Wb` written so far: frames of answers `Rs` (distinct calls, each with
its persistent answer and the writer token `σ ↪ i` of its run). -/
def respDone (W : GrpcWorld GF) (a : GoString) (cid : w64) (σ : GName) (Wb : List w8) :
    IProp GF :=
  iprop(⌜Wb = []⌝ ∨
    ∃ (γ : GConnNames) (Rs : List Ans),
      isGConn W a cid γ ∗
      ([∗list] x ∈ Rs, ghostMapElem γ.ans x.1 .discard (some x.2)) ∗
      ([∗list] x ∈ Rs, ghostMapElem σ x.1 (DFrac.own 1) ()) ∗
      ⌜(Rs.map Prod.fst).Nodup ∧ (∀ q ∈ Rs.map respMsg, q.length < 2 ^ 63) ∧
        Wb = framesOf (Rs.map respMsg)⌝)

theorem toks_ne (σ : GName) (k : Nat) (Rs : List Ans) :
    ⊢ (ghostMapElem σ k (DFrac.own 1) () : IProp GF) -∗
      ([∗list] x ∈ Rs, ghostMapElem σ x.1 (DFrac.own 1) ()) -∗ ⌜k ∉ Rs.map Prod.fst⌝ := by
  induction Rs with
  | nil => iintro - -; ipureintro; simp
  | cons x Rs ih =>
    iintro Hk Hl
    icases BigSepL.bigSepL_cons.1 $$ Hl with ⟨Hx, Hl⟩
    ihave %Hne := ghostMapElem_ne σ k x.1 (DFrac.own 1) () () $$ Hk Hx
    ihave %IH := ih $$ Hk Hl
    ipureintro
    simp only [List.map_cons, List.mem_cons, not_or]
    exact ⟨Hne, IH⟩

theorem toks_ne' (σ : GName) (k : Nat) (Rs : List Ans) :
    (ghostMapElem σ k (DFrac.own 1) () : IProp GF) ∗
        ([∗list] x ∈ Rs, ghostMapElem σ x.1 (DFrac.own 1) ()) ⊢
      ((ghostMapElem σ k (DFrac.own 1) () : IProp GF) ∗
        ([∗list] x ∈ Rs, ghostMapElem σ x.1 (DFrac.own 1) ())) ∗ ⌜k ∉ Rs.map Prod.fst⌝ :=
  persistent_entails_left (Q := iprop(⌜k ∉ Rs.map Prod.fst⌝ : IProp GF)) (by
    iintro ⟨Hk, Hl⟩
    iapply toks_ne σ k Rs $$ Hk Hl)

/-- The names of a connection are unique. -/
theorem isGConn_agree (W : GrpcWorld GF) (a : GoString) (cid : w64) (γ γ' : GConnNames) :
    ⊢ isGConn W a cid γ -∗ isGConn W a cid γ' -∗ ⌜γ = γ'⌝ := by
  iintro Hc Hc'
  unfold isGConn regElem
  icases Hc with ⟨Hr, -⟩
  icases Hc' with ⟨Hr', -⟩
  iapply ghostMapElem_agree _ _ _ _ _ _ $$ Hr Hr'

/-- A connection's invariant, from its persistent description. -/
theorem isGConn_inv (W : GrpcWorld GF) (a : GoString) (cid : w64) (γ : GConnNames) :
    isGConn W a cid γ ⊢ inv connN (connInv W a cid γ) := by
  unfold isGConn
  iintro ⟨-, #H⟩
  iexact H

/-- The run of call `k` (answered `(code, msg, reply)`) writes its frame: the stream's protocol
holds of it, and the writer's record grows by the answer, with the run's token. -/
theorem resp_next (W : GrpcWorld GF) (a : GoString) (cid : w64) (γ : GConnNames) (σ : GName)
    (Wb : List w8) (k : Nat) (code : w64) (msg : GoString) (reply : List w8)
    (hlen : (respMsg (k, code, msg, reply)).length < 2 ^ 63) :
    ⊢ isGConn W a cid γ -∗ respDone W a cid σ Wb -∗ ghostMapElem σ k (DFrac.own 1) () -∗
      ghostMapElem γ.ans k .discard (some (code, msg, reply)) -∗
      □ respProto W a cid (Wb ++ frameOf (respMsg (k, code, msg, reply))) ∗
      respDone W a cid σ (Wb ++ frameOf (respMsg (k, code, msg, reply))) := by
  iintro #Hc Hd Htok #Hans
  unfold respDone
  icases Hd with (%HWb | ⟨%γ', %Rs, #Hc0, #HRs, HtRs, %HRs⟩)
  · have hpure : ([((k, code, msg, reply) : Ans)].map Prod.fst : List Nat).Nodup ∧
        (∀ q ∈ [((k, code, msg, reply) : Ans)].map respMsg, q.length < 2 ^ 63) ∧
        Wb ++ frameOf (respMsg (k, code, msg, reply)) =
          framesOf ([((k, code, msg, reply) : Ans)].map respMsg) := by
      refine ⟨by simp, by simpa using hlen, ?_⟩
      simp [HWb, framesOf]
    isplitl []
    · imodintro
      unfold respProto
      iexists γ, [(k, code, msg, reply)]
      iframe Hc
      isplitl
      · iapply BigSepL.bigSepL_singleton.2
        iexact Hans
      · ipureintro
        exact ⟨hpure.1, hpure.2.1, hpure.2.2 ▸ List.prefix_refl _⟩
    · iright
      iexists γ, [(k, code, msg, reply)]
      iframe Hc
      isplitl []
      · iapply BigSepL.bigSepL_singleton.2
        iexact Hans
      isplitl [Htok]
      · iapply BigSepL.bigSepL_singleton.2
        iexact Htok
      ipureintro; exact hpure
  · ihave %Hγ := isGConn_agree W a cid γ γ' $$ Hc Hc0
    subst Hγ
    ihave ⟨⟨Htok, HtRs⟩, %Hnot⟩ := toks_ne' σ k Rs $$ [Htok HtRs]
    · iframe Htok HtRs
    have hpure : ((Rs ++ [(k, code, msg, reply)]).map Prod.fst : List Nat).Nodup ∧
        (∀ q ∈ (Rs ++ [((k, code, msg, reply) : Ans)]).map respMsg, q.length < 2 ^ 63) ∧
        Wb ++ frameOf (respMsg (k, code, msg, reply)) =
          framesOf ((Rs ++ [((k, code, msg, reply) : Ans)]).map respMsg) := by
      obtain ⟨hnd, hbd, hwb⟩ := HRs
      refine ⟨?_, ?_, ?_⟩
      · rw [List.map_append, List.nodup_append]
        refine ⟨hnd, by simp, ?_⟩
        intro x hx y hy
        simp only [List.map_cons, List.map_nil, List.mem_singleton] at hy
        subst hy
        intro hxy; subst hxy; exact Hnot hx
      · intro q hq
        rw [List.map_append] at hq
        rcases List.mem_append.1 hq with hq | hq
        · exact hbd q hq
        · simp at hq; subst hq; exact hlen
      · rw [hwb, List.map_append, framesOf_append]
        simp [framesOf]
    isplitl []
    · imodintro
      unfold respProto
      iexists γ, Rs ++ [(k, code, msg, reply)]
      iframe Hc
      isplitl
      · iapply BigSepL.bigSepL_snoc.2
        iframe HRs Hans
      · ipureintro
        exact ⟨hpure.1, hpure.2.1, hpure.2.2 ▸ List.prefix_refl _⟩
    · iright
      iexists γ, Rs ++ [(k, code, msg, reply)]
      iframe Hc
      isplitl []
      · iapply BigSepL.bigSepL_snoc.2
        iframe HRs Hans
      isplitl [Htok HtRs]
      · iapply BigSepL.bigSepL_snoc.2
        iframe Htok HtRs
      ipureintro; exact hpure

end ghost

end google_golang_org.grpc

end Perennial
