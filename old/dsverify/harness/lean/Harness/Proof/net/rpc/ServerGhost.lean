/-
The server's ghost lemmas over a connection's invariant (`connInv`, `Proto.lean`), and the
invariant of a connection's response writer (`connWriter`, `server.go`).

* `req_parse`: a frame the reader reads after the request head and the frames of its first `k`
  requests is the payload of request `k` of the connection (from the dialer's protocol).
* `claim_role`: with the acceptor's fresh token, the reader claims its half of `ctr` (at `0`).
* `take_req`: the reader takes request `k` once: its deposit, and `ans k ↦ none` (own).
* `answer`: the run answers request `k`: `ans k ↦□ some (msg, reply)`; the continuation of the
  reply and the message goes to the invariant (`replyEscrow`) for the client to collect, whatever
  the message.
* `respDone W a cid σ Wb`: the response bytes `Wb` written so far meet `respProto`, as frames of
  answers `Rs` each with its writer token `σ ↪ i` (the run's, so no index is answered twice);
  `resp_next` extends it by one answer.
-/
module

public import Harness.Proof.net.rpc.WireSpec

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode NetConn

namespace net.rpc

/-! ## Pure facts -/

theorem srv_respMsg_stable {L L' : List RpcReq} (x : Nat × GoString × List w8)
    (hx : x.1 < L.length) (h : L <+: L') : respMsg L x = respMsg L' x := by
  unfold respMsg
  obtain ⟨t, rfl⟩ := h
  rw [List.getElem?_append_left hx]

theorem srv_prefix_getElem? {L L' : List RpcReq} {i : Nat} {r : RpcReq} (h : L <+: L')
    (hi : L[i]? = some r) : L'[i]? = some r := by
  obtain ⟨t, rfl⟩ := h
  grind

/-! ## Ghost lemmas -/

section ghost
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netConnExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

attribute [local instance] GooseGlobalGS.gooseInvGS

instance isRpcConn_persistent' (W : RpcWorld GF) (a : GoString) (cid : w64)
    (γ : RpcConnNames) : Persistent (isRpcConn W a cid γ) := by
  unfold isRpcConn regElem; infer_instance

instance respProto_persistent' (W : RpcWorld GF) (a : GoString) (cid : w64) (bs : List w8) :
    Persistent (respProto W a cid bs) := by
  unfold respProto; infer_instance

/-- A mono-list authority and its lower bound. -/
theorem monoList_auth_lb (γ : GName) (q : Qp) (l : List RpcReq) :
    monoListAuthOwn (GF := GF) γ q l ⊢ monoListAuthOwn γ q l ∗ monoListLbOwn γ l :=
  persistent_entails_left (Q := monoListLbOwn (GF := GF) γ l) (monoListLbOwn_get γ q l)

theorem claim_role (W : RpcWorld GF) (a : GoString) (cid : w64) (γ : RpcConnNames)
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

/-- A mono-list authority and a lower bound: the bound is a prefix. -/
theorem auth_lb_prefix (γ : GName) (q : Qp) (l1 l2 : List RpcReq) :
    monoListAuthOwn (GF := GF) γ q l1 ∗ monoListLbOwn γ l2 ⊢
      (monoListAuthOwn γ q l1 ∗ monoListLbOwn γ l2) ∗ ⌜l2 <+: l1⌝ :=
  persistent_entails_left (Q := iprop(⌜l2 <+: l1⌝ : IProp GF)) (by
    iintro ⟨Ha, Hb⟩
    icases mono_list_auth_lb_valid γ q l1 l2 $$ Ha Hb with %h
    ipureintro; exact h.2)

theorem take_req (W : RpcWorld GF) (a : GoString) (cid : w64) (γ : RpcConnNames) (k : Nat)
    (L : List RpcReq) (r : RpcReq) (hr : L[k]? = some r) (E : CoPset) (hE : ↑connN ⊆ E) :
    ⊢ inv connN (connInv W a cid γ) -∗ ghostVar γ.ctr (1 : Qp).half k -∗
      monoListLbOwn γ.reqs L ={E}=∗
      ghostVar γ.ctr (1 : Qp).half (k + 1) ∗ ▷ reqDeposit W a r ∗
      ghostMapElem γ.ans k (DFrac.own 1) (none : Option (GoString × List w8)) := by
  iintro #Hinv Hmy #Hlb
  unfold connInv
  iinv Hinv with ⟨%L', %k', %A, >Hreqs, >Hctr, >Hans, >Hrole, >%Hk, Hdeps, Hres⟩ Hclose
  icombine Hctr Hmy gives %Heq
  obtain ⟨_, Heq⟩ := Heq
  subst Heq
  ihave ⟨⟨Hreqs, -⟩, %Hpre⟩ := auth_lb_prefix γ.reqs _ L' L $$ [Hreqs Hlb]
  · iframe Hreqs Hlb
  have hr' := srv_prefix_getElem? Hpre hr
  have hkL : k' < L'.length := (List.getElem?_eq_some_iff.1 hr').1
  have hdrop : L'.drop k' = r :: L'.drop (k' + 1) := by
    rw [List.drop_eq_getElem_cons hkL]
    congr
    exact (List.getElem?_eq_some_iff.1 hr').2
  rw [hdrop]
  icases Hdeps with ⟨Hdep, Hdeps⟩
  have hAk : A.lookup k' = none := by
    cases h : A.lookup k' with
    | none => rfl
    | some v =>
      have := Hk.2 k' (by show (A.lookup k').isSome = true; simp [h])
      omega
  imod ghost_map_insert k' (none : Option (GoString × List w8)) hAk $$ Hans with ⟨Hans, Hel⟩
  imod ghostVar_update_halves (k' + 1) γ.ctr k' k' $$ Hctr Hmy with ⟨Hctr, Hmy⟩
  imod Hclose $$ [Hreqs Hctr Hans Hrole Hdeps Hres] with -
  · inext
    iexists L', k' + 1, A.insert k' none
    iframe Hreqs Hctr Hans Hrole Hdeps
    isplitr
    · ipureintro
      refine ⟨hkL, fun i hi => ?_⟩
      by_cases hik : i = k'
      · omega
      · have : (A !! i).isSome := by
          rwa [GMap.lookup_insert_ne _ _ (Ne.symm hik)] at hi
        have := Hk.2 i this
        omega
    · iapply (BigSepM.bigSepM_insert (by rw [gmap_get?_eq]; exact hAk)).2
      iframe Hres
      unfold answerRes
      itrivial
  imodintro
  iframe Hmy Hdep Hel

theorem answer (W : RpcWorld GF) (a : GoString) (cid : w64) (γ : RpcConnNames) (k : Nat)
    (L : List RpcReq) (r : RpcReq) (msg : GoString) (reply : List w8) (hr : L[k]? = some r)
    (E : CoPset) (hE : ↑connN ⊆ E) :
    ⊢ inv connN (connInv W a cid γ) -∗
      ghostMapElem γ.ans k (DFrac.own 1) (none : Option (GoString × List w8)) -∗
      monoListLbOwn γ.reqs L -∗ replyEscrow r reply msg ={E}=∗
      ghostMapElem γ.ans k .discard (some (msg, reply)) := by
  iintro #Hinv Hel #Hlb Hesc
  unfold connInv
  iinv Hinv with ⟨%L', %k', %A, >Hreqs, >Hctr, >Hans, >Hrole, >%Hk, Hdeps, Hres⟩ Hclose
  icombine Hel Hans gives %HA
  ihave ⟨⟨Hreqs, -⟩, %Hpre⟩ := auth_lb_prefix γ.reqs _ L' L $$ [Hreqs Hlb]
  · iframe Hreqs Hlb
  have hr' := srv_prefix_getElem? Hpre hr
  imod ghost_map_update (some (msg, reply)) $$ Hans Hel with ⟨Hans, Hel⟩
  imod ghostMapElem_persist $$ Hel with #Hel
  imod Hclose $$ [Hreqs Hctr Hans Hrole Hdeps Hres Hesc] with -
  · inext
    iexists L', k', A.insert k (some (msg, reply))
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
      iexists r
      isplitr
      · ipureintro; exact hr'
      ileft; iexact Hesc
  imodintro
  iexact Hel

/-- A frame the reader reads after the head and the frames `qs` of its first requests is the
payload of the connection's next request. -/
theorem req_parse (W : RpcWorld GF) (a : GoString) (cid : w64) (qs : List (List w8))
    (p : List w8) (hqs : ∀ q ∈ qs, q.length < 2 ^ 63) (hp : p.length < 2 ^ 63) :
    recvTok cid true (reqProto W a) (rpcHead ++ framesOf qs ++ frameOf p) ⊢
      recvTok cid true (reqProto W a) (rpcHead ++ framesOf qs ++ frameOf p) ∗
      ∃ (γ : RpcConnNames) (L : List RpcReq) (r : RpcReq), isRpcConn W a cid γ ∗
        monoListLbOwn γ.reqs L ∗ ⌜L[qs.length]? = some r ∧ reqMsg r = p⌝ := by
  iintro H
  ihave ⟨H, Hp⟩ := recvTok_proto cid true _ _ $$ H
  iframe H
  unfold protoPrefix
  icases Hp with (%Hnil | ⟨%ext, %Hext, #HP⟩)
  · exfalso
    have := congrArg List.length Hnil
    simp [frameOf_length] at this
  unfold reqProto net.http.httpReqP
  icases HP with (%Hpre | ⟨%rest, %Hrest, #Hb⟩)
  · exfalso
    have := (Hext.trans Hpre).length_le
    simp only [rpcHead, List.length_append, frameOf_length] at this
    omega
  unfold reqBodyProto
  icases Hb with ⟨%γ, %L, #Hc, #Hlb, %Hbd⟩
  have h1 : framesOf qs ++ frameOf p <+: framesOf (L.map reqMsg) := by
    subst Hrest
    rw [List.append_assoc] at Hext
    exact ((List.prefix_append_right_inj _).1 Hext).trans Hbd.2
  obtain ⟨_, hget⟩ := framesOf_next hqs Hbd.1 hp h1
  rw [List.getElem?_map] at hget
  cases hL : L[qs.length]? with
  | none => rw [hL] at hget; cases hget
  | some r =>
    rw [hL] at hget
    iexists γ, L, r
    iframe Hc Hlb
    ipureintro
    exact ⟨hL, Option.some.inj hget⟩

/-- An answer of a response stream, as `respProto` names it: the request's index, the error
message, the reply. -/
abbrev SrvAns := Nat × GoString × List w8

/-- The response bytes `Wb` written so far meet `respProto`: `connectedBytes`, or frames of
answers `Rs` (distinct, each with its persistent answer and the writer token `σ ↪ i` that the run
of request `i` gave up when writing it). -/
def respDone (W : RpcWorld GF) (a : GoString) (cid : w64) (σ : GName) (Wb : List w8) :
    IProp GF :=
  iprop(⌜Wb = connectedBytes⌝ ∨
    ∃ (γ : RpcConnNames) (L : List RpcReq) (Rs : List SrvAns),
      isRpcConn W a cid γ ∗ monoListLbOwn γ.reqs L ∗
      ([∗list] x ∈ Rs, ghostMapElem γ.ans x.1 .discard (some x.2)) ∗
      ([∗list] x ∈ Rs, ghostMapElem σ x.1 (DFrac.own 1) ()) ∗
      ⌜(Rs.map Prod.fst).Nodup ∧ (∀ x ∈ Rs, x.1 < L.length) ∧
        (∀ q ∈ Rs.map (respMsg L), q.length < 2 ^ 63) ∧
        Wb = connectedBytes ++ framesOf (Rs.map (respMsg L))⌝)

theorem toks_ne (σ : GName) (k : Nat) (Rs : List SrvAns) :
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

theorem toks_ne' (σ : GName) (k : Nat) (Rs : List SrvAns) :
    (ghostMapElem σ k (DFrac.own 1) () : IProp GF) ∗
        ([∗list] x ∈ Rs, ghostMapElem σ x.1 (DFrac.own 1) ()) ⊢
      ((ghostMapElem σ k (DFrac.own 1) () : IProp GF) ∗
        ([∗list] x ∈ Rs, ghostMapElem σ x.1 (DFrac.own 1) ())) ∗ ⌜k ∉ Rs.map Prod.fst⌝ :=
  persistent_entails_left (Q := iprop(⌜k ∉ Rs.map Prod.fst⌝ : IProp GF)) (by
    iintro ⟨Hk, Hl⟩
    iapply toks_ne σ k Rs $$ Hk Hl)

theorem respMsg_of (L : List RpcReq) (k : Nat) (r : RpcReq) (msg : GoString)
    (reply : List w8) (hr : L[k]? = some r) :
    respMsg L (k, msg, reply) = msgOf r.seq msg reply := by
  unfold respMsg; simp [hr]

/-- The names of a connection are unique. -/
theorem isRpcConn_agree (W : RpcWorld GF) (a : GoString) (cid : w64) (γ γ' : RpcConnNames) :
    ⊢ isRpcConn W a cid γ -∗ isRpcConn W a cid γ' -∗ ⌜γ = γ'⌝ := by
  iintro Hc Hc'
  unfold isRpcConn regElem
  icases Hc with ⟨Hr, -⟩
  icases Hc' with ⟨Hr', -⟩
  iapply ghostMapElem_agree _ _ _ _ _ _ $$ Hr Hr'

/-- Two lower bounds of a connection's requests are prefixes of a third. -/
theorem lb_extend (W : RpcWorld GF) (a : GoString) (cid : w64) (γ : RpcConnNames)
    (L1 L2 : List RpcReq) (E : CoPset) (hE : ↑connN ⊆ E) :
    ⊢ isRpcConn W a cid γ -∗ monoListLbOwn γ.reqs L1 -∗ monoListLbOwn γ.reqs L2 ={E}=∗
      ∃ L' : List RpcReq, monoListLbOwn γ.reqs L' ∗ ⌜L1 <+: L' ∧ L2 <+: L'⌝ := by
  iintro Hc #H1 #H2
  unfold isRpcConn
  icases Hc with ⟨-, #Hinv⟩
  unfold connInv
  iinv Hinv with ⟨%L', %k', %A, >Hreqs, >Hctr, >HA, >Hrole, >%Hk, Hdeps, Hres⟩ Hclose
  ihave ⟨Hreqs, #HlbL'⟩ := monoList_auth_lb γ.reqs _ L' $$ Hreqs
  ihave ⟨⟨Hreqs, -⟩, %Hp1⟩ := auth_lb_prefix γ.reqs _ L' L1 $$ [Hreqs H1]
  · iframe Hreqs H1
  ihave ⟨⟨Hreqs, -⟩, %Hp2⟩ := auth_lb_prefix γ.reqs _ L' L2 $$ [Hreqs H2]
  · iframe Hreqs H2
  imod Hclose $$ [Hreqs Hctr HA Hrole Hdeps Hres] with -
  · inext; iexists L', k', A; iframe; ipureintro; exact Hk
  imodintro
  iexists L'
  iframe HlbL'
  ipureintro; exact ⟨Hp1, Hp2⟩

/-- The run of request `k` (answered `(msg, reply)`) writes its frame: the stream's protocol
holds of it, and the writer's record grows by the answer, with the run's token. -/
theorem resp_next (W : RpcWorld GF) (a : GoString) (cid : w64) (γ : RpcConnNames) (σ : GName)
    (Wb : List w8) (k : Nat) (L : List RpcReq) (r : RpcReq) (msg : GoString) (reply : List w8)
    (hr : L[k]? = some r) (hlen : (msgOf r.seq msg reply).length < 2 ^ 63)
    (E : CoPset) (hE : ↑connN ⊆ E) :
    ⊢ isRpcConn W a cid γ -∗ respDone W a cid σ Wb -∗ ghostMapElem σ k (DFrac.own 1) () -∗
      ghostMapElem γ.ans k .discard (some (msg, reply)) -∗ monoListLbOwn γ.reqs L ={E}=∗
      □ respProto W a cid (Wb ++ frameOf (msgOf r.seq msg reply)) ∗
      respDone W a cid σ (Wb ++ frameOf (msgOf r.seq msg reply)) := by
  iintro #Hc Hd Htok #Hans #Hlb
  unfold respDone
  icases Hd with (%HWb | ⟨%γ', %L0, %Rs, #Hc0, #Hlb0, #HRs, HtRs, %HRs⟩)
  · imod lb_extend W a cid γ L L E hE $$ Hc Hlb Hlb with ⟨%L', #HlbL', %Hpp⟩
    obtain ⟨Hpre, -⟩ := Hpp
    have hr' := srv_prefix_getElem? Hpre hr
    have hkL : k < L'.length := (List.getElem?_eq_some_iff.1 hr').1
    have hm := respMsg_of L' k r msg reply hr'
    have hpure : ([(k, msg, reply)].map Prod.fst : List Nat).Nodup ∧
        (∀ x ∈ [((k, msg, reply) : SrvAns)], x.1 < L'.length) ∧
        (∀ q ∈ [((k, msg, reply) : SrvAns)].map (respMsg L'), q.length < 2 ^ 63) ∧
        Wb ++ frameOf (msgOf r.seq msg reply) =
          connectedBytes ++ framesOf ([((k, msg, reply) : SrvAns)].map (respMsg L')) := by
      refine ⟨by simp, by simpa using hkL, by simpa [hm] using hlen, ?_⟩
      simp [HWb, hm, framesOf]
    imodintro
    isplitl []
    · imodintro
      unfold respProto
      iright
      iexists γ, L', [(k, msg, reply)]
      iframe Hc HlbL'
      isplitl
      · iapply BigSepL.bigSepL_singleton.2
        iexact Hans
      · ipureintro
        exact ⟨hpure.1, hpure.2.1, hpure.2.2.1, hpure.2.2.2 ▸ List.prefix_refl _⟩
    · iright
      iexists γ, L', [(k, msg, reply)]
      iframe Hc HlbL'
      isplitl []
      · iapply BigSepL.bigSepL_singleton.2
        iexact Hans
      isplitl [Htok]
      · iapply BigSepL.bigSepL_singleton.2
        iexact Htok
      ipureintro; exact hpure
  · -- the same connection names
    ihave %Hγ := isRpcConn_agree W a cid γ γ' $$ Hc Hc0
    subst Hγ
    imod lb_extend W a cid γ L L0 E hE $$ Hc Hlb Hlb0 with ⟨%L', #HlbL', %Hpp⟩
    obtain ⟨Hpre, Hpre0⟩ := Hpp
    ihave ⟨⟨Htok, HtRs⟩, %Hnot⟩ := toks_ne' σ k Rs $$ [Htok HtRs]
    · iframe Htok HtRs
    have hr' := srv_prefix_getElem? Hpre hr
    have hkL : k < L'.length := (List.getElem?_eq_some_iff.1 hr').1
    have hm := respMsg_of L' k r msg reply hr'
    have hstab : Rs.map (respMsg L0) = Rs.map (respMsg L') :=
      List.map_congr_left (fun y hy => srv_respMsg_stable y (HRs.2.1 y hy) Hpre0)
    have hpure : ((Rs ++ [(k, msg, reply)]).map Prod.fst : List Nat).Nodup ∧
        (∀ x ∈ Rs ++ [((k, msg, reply) : SrvAns)], x.1 < L'.length) ∧
        (∀ q ∈ (Rs ++ [((k, msg, reply) : SrvAns)]).map (respMsg L'), q.length < 2 ^ 63) ∧
        Wb ++ frameOf (msgOf r.seq msg reply) =
          connectedBytes ++ framesOf ((Rs ++ [((k, msg, reply) : SrvAns)]).map (respMsg L')) := by
      obtain ⟨hnd, hlt, hbd, hwb⟩ := HRs
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [List.map_append, List.nodup_append]
        refine ⟨hnd, by simp, ?_⟩
        intro x hx y hy
        simp only [List.map_cons, List.map_nil, List.mem_singleton] at hy
        subst hy
        intro hxy; subst hxy; exact Hnot hx
      · intro x hx
        rcases List.mem_append.1 hx with hx | hx
        · exact Nat.lt_of_lt_of_le (hlt x hx) Hpre0.length_le
        · simp at hx; subst hx; exact hkL
      · intro q hq
        rw [List.map_append, ← hstab] at hq
        rcases List.mem_append.1 hq with hq | hq
        · exact hbd q hq
        · simp [hm] at hq; subst hq; exact hlen
      · rw [hwb, hstab, List.map_append, framesOf_append]
        simp [hm, framesOf, List.append_assoc]
    imodintro
    isplitl []
    · imodintro
      unfold respProto
      iright
      iexists γ, L', Rs ++ [(k, msg, reply)]
      iframe Hc HlbL'
      isplitl
      · iapply BigSepL.bigSepL_snoc.2
        iframe HRs Hans
      · ipureintro
        exact ⟨hpure.1, hpure.2.1, hpure.2.2.1, hpure.2.2.2 ▸ List.prefix_refl _⟩
    · iright
      iexists γ, L', Rs ++ [(k, msg, reply)]
      iframe Hc HlbL'
      isplitl []
      · iapply BigSepL.bigSepL_snoc.2
        iframe HRs Hans
      isplitl [Htok HtRs]
      · iapply BigSepL.bigSepL_snoc.2
        iframe Htok HtRs
      ipureintro; exact hpure

/-- A connection's invariant, from its persistent description. -/
theorem isRpcConn_inv (W : RpcWorld GF) (a : GoString) (cid : w64) (γ : RpcConnNames) :
    isRpcConn W a cid γ ⊢ inv connN (connInv W a cid γ) := by
  unfold isRpcConn
  iintro ⟨-, #H⟩
  iexact H

/-- The invariant of a connection's `connWriter` `w` (its mutex's): `broken`, and while not
broken, the writer's token of the response stream, whose bytes meet `respDone`. -/
def cwInv (W : RpcWorld GF) (a : GoString) (cid : w64) (σ : GName) (w : Loc) : IProp GF :=
  iprop(∃ broken : Bool, structFieldRef net.rpc.connWriter go!"broken" w ↦ broken ∗
    (if broken then iprop(True) else
      ∃ Wb : List w8, sendTok cid true (respProto W a) Wb ∗ respDone W a cid σ Wb))

end ghost

end net.rpc

end Perennial
