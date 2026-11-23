/-
The server's ghost lemmas over a connection's invariant (`connInv`, `Proto.lean`): what a request
it reads is (`req_hdr`, after a header frame: the reader takes the request, its deposit and the
right to answer it once; `req_body`, after its body frame: the request's argument bytes), and the
answer a response records (`answer`, from the right to answer and the continuation's
`Φ reply msg`; `resp_step`, the response written: the acceptor's protocol fact and the record
`ansRec` grown by the answer). Ported from dsverify-lab's `Harness/Proof/net/rpc/ServerGhost.lean`
(`348a866`), over the model's two-frame wire.
-/
module

public import Net.Proof.net.rpc.ServerDefs

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace net.rpc

/-! ## Pure facts of the requests' wire -/

theorem reqWire_mapIdx (n : Nat) : ∀ L : List RpcReq,
    (L.mapIdx fun i r => reqWire (W64 ((n + i : Nat) : Int)) r.sm r.body).flatten =
      framesOf (reqPlsFrom n L)
  | [] => by simp [reqPlsFrom, framesOf]
  | r :: L => by
    rw [List.mapIdx_cons, List.flatten_cons, reqPlsFrom, framesOf_cons, framesOf_cons]
    have ih := reqWire_mapIdx (n + 1) L
    have hf : (fun (i : Nat) (r : RpcReq) => reqWire (W64 ((n + (i + 1) : Nat) : Int)) r.sm r.body) =
        (fun i r => reqWire (W64 ((n + 1 + i : Nat) : Int)) r.sm r.body) := by
      funext i r; rw [Nat.add_comm i 1, Nat.add_assoc]
    rw [hf, ih, Nat.add_zero, reqWire, List.append_assoc]

theorem reqsWire_framesOf (L : List RpcReq) : reqsWire L = framesOf (reqPls L) := by
  have := reqWire_mapIdx 0 L
  simp only [Nat.zero_add] at this
  exact this

theorem reqPlsFrom_getElem? : ∀ (n : Nat) (L : List RpcReq) (k j : Nat), j < 2 →
    (reqPlsFrom n L)[2 * k + j]? =
      (L[k]?).bind (fun r => [reqHdr (W64 ((n + k : Nat) : Int)) r.sm, r.body][j]?)
  | _, [], _, _, _ => by simp [reqPlsFrom]
  | n, r :: L, 0, j, hj => by
    rcases j with _ | _ | j
    · simp [reqPlsFrom]
    · simp [reqPlsFrom]
    · omega
  | n, r :: L, k + 1, j, hj => by
    rw [show 2 * (k + 1) + j = (2 * k + j) + 1 + 1 by omega]
    simp only [reqPlsFrom, List.getElem?_cons_succ]
    rw [reqPlsFrom_getElem? (n + 1) L k j hj]
    simp [show n + 1 + k = n + (k + 1) by omega]

theorem reqHdr_length (seq : w64) (sm : GoString) : (reqHdr seq sm).length = 16 + sm.length := by
  simp [reqHdr, strEnc_length, u64Le_length]; omega

theorem reqPlsFrom_ok : ∀ (n : Nat) (L : List RpcReq), (∀ r ∈ L, reqOk r) →
    ∀ q ∈ reqPlsFrom n L, q.length < 2 ^ 63
  | _, [], _ => by simp [reqPlsFrom]
  | n, r :: L, h => by
    intro q hq
    simp only [reqPlsFrom, List.mem_cons] at hq
    obtain ⟨h1, h2⟩ := h r (by simp)
    rcases hq with rfl | rfl | hq
    · rw [reqHdr_length]; omega
    · exact h2
    · exact reqPlsFrom_ok (n + 1) L (fun r' hr' => h r' (by simp [hr'])) q hq

/-- A request header decodes uniquely (its string shorter than `2 ^ 63`). -/
theorem reqHdr_inj {seq seq' : w64} {sm sm' : GoString} (h1 : sm.length < 2 ^ 63)
    (h1' : sm'.length < 2 ^ 63) (h : reqHdr seq sm = reqHdr seq' sm') : seq = seq' ∧ sm = sm' := by
  simp only [reqHdr] at h
  obtain ⟨hs, h⟩ := List.append_inj h (by simp [u64Le_length])
  have h' : strEnc sm ++ [] = strEnc sm' ++ [] := by simpa using h
  exact ⟨u64Le_inj hs, (strEnc_append_inj h1 h1' h').1⟩

/-- The payload after the frames `ps` (`2 * k + j` of them) of a prefix of the requests `L`'s wire:
the `j`-th of request `k`. -/
theorem req_next (L : List RpcReq) (ps : List (List w8)) (p : List w8) (k j : Nat) (hj : j < 2)
    (hps : ps.length = 2 * k + j) (hL : ∀ r ∈ L, reqOk r) (hb : ∀ q ∈ ps, q.length < 2 ^ 63)
    (hp : p.length < 2 ^ 63) (h : framesOf (ps ++ [p]) <+: reqsWire L) :
    ∃ r, L[k]? = some r ∧ [reqHdr (W64 k) r.sm, r.body][j]? = some p := by
  rw [reqsWire_framesOf] at h
  have hpf := framesOf_parse ps (reqPls L) p [] hb hp (reqPlsFrom_ok 0 L hL)
    (by rw [List.append_nil]; rw [framesOf_append, framesOf_cons, framesOf_nil, List.append_nil] at h
        exact h)
  have hidx : (reqPls L)[2 * k + j]? = some p := by
    obtain ⟨t, ht⟩ := hpf
    rw [← ht, List.getElem?_append_left (by simp; omega), List.getElem?_append_right (by omega),
      hps, Nat.sub_self]
    rfl
  unfold reqPls at hidx
  rw [reqPlsFrom_getElem? 0 L k j hj, Nat.zero_add] at hidx
  cases hr : L[k]? with
  | none => rw [hr] at hidx; cases hidx
  | some r => rw [hr] at hidx; exact ⟨r, rfl, hidx⟩

theorem ansPls_frames (x : Ans) :
    framesOf (ansPls x) = respWire (W64 x.idx) x.sm x.msg x.reply := by
  simp [ansPls, framesOf, respWire]

theorem framesOf_snoc_ne (ps : List (List w8)) (h : List w8) : framesOf (ps ++ [h]) ≠ [] := by
  intro e
  have := congrArg List.length e
  simp [framesOf_append, framesOf_cons, frameOf_length] at this

theorem respsWire_snoc (Rs : List Ans) (x : Ans) :
    respsWire (Rs ++ [x]) = respsWire Rs ++ respWire (W64 x.idx) x.sm x.msg x.reply := by
  unfold respsWire
  rw [List.flatMap_append, framesOf_append, List.flatMap_singleton, ansPls_frames]

/-! ## The last dot (`readRequestHeader`'s loop) -/

theorem find_rev_range_of (p : Nat → Bool) (i : Nat) (hi : p i = true) :
    ∀ n, i < n → (∀ j, i < j → j < n → p j = false) →
      ((List.range n).reverse.find? p) = some i
  | 0, h, _ => absurd h (Nat.not_lt_zero _)
  | n + 1, h, hj => by
    rw [List.range_succ, List.reverse_append, List.reverse_singleton, List.singleton_append,
      List.find?_cons]
    by_cases hn : n = i
    · subst hn; simp [hi]
    · rw [hj n (by omega) (by omega)]
      exact find_rev_range_of p i hi n (by omega) (fun j h1 h2 => hj j h1 (by omega))

/-- The loop's dot is the last one. -/
theorem lastDotIdx_of (s : GoString) (i : Nat) (hi : i < s.length) (hd : s[i]? = some (W8 46))
    (hj : ∀ j, i < j → j < s.length → s[j]? ≠ some (W8 46)) : lastDotIdx s = some i := by
  unfold lastDotIdx
  exact find_rev_range_of _ i (by simp [hd]) s.length hi
    (fun j h1 h2 => by simpa using hj j h1 h2)

/-- A last dot is a dot. -/
theorem lastDotIdx_some (s : GoString) (i : Nat) (h : lastDotIdx s = some i) :
    i < s.length ∧ s[i]? = some (W8 46) := by
  unfold lastDotIdx at h
  have hm := List.mem_of_find?_eq_some h
  have hp := List.find?_some h
  simp only [List.mem_reverse, List.mem_range] at hm
  exact ⟨hm, by simpa using hp⟩

/-! ## Ghost lemmas -/

section ghost
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : net.rpc.Assumptions] [field_sem : net.FieldAssumptions]
variable [π : NetProtoGS]

attribute [local instance] GooseGlobalGS.gooseInvGS

/-! ### Read errors -/

theorem rdErr_newVar (X msg : GoString) (e : GoInterface) (hm : msg ≠ []) :
    errors.newVar (GF := GF) X msg ⊢ globalAddr X ↦□ e -∗ rdErr e := by
  iintro #Hv #He
  ihave #Hn := errNE_newVar X msg e hm $$ Hv He
  iunfold errors.newVar at Hv
  icases Hv with ⟨%x, #Hx, -⟩
  icombine He Hx gives %Heq
  subst Heq
  iunfold rdErr
  iframe Hn
  ipureintro; exact ⟨_, x, rfl⟩

/-- A frame read's failure (the server codec's reads') is a sticky read error. -/
theorem rdErr_read (la ra eof ueof ed ef : GoInterface) (first : Bool) (got : List w8)
    (err : GoInterface) :
    errors.newVar (GF := GF) net.rpc.errFrame go!"rpc: malformed frame" ∗
      globalAddr net.rpc.errFrame ↦□ ef ∗ isPkgInit (PROP := IProp GF) pkg_id.io ∗
      globalAddr io.EOF ↦□ eof ∗ globalAddr io.ErrUnexpectedEOF ↦□ ueof ∗
      (⌜err = ef⌝ ∨ readErr la ra eof ueof ed first got err) ⊢ rdErr err := by
  iintro ⟨#HefV, #Hef, #Hio, #Heof, #Hueof, #HE⟩
  icases HE with (%He | #HE)
  · subst He; iapply rdErr_newVar _ _ _ (by simp) $$ HefV Hef
  iunfold readErr at HE
  icases HE with (⟨%He, -⟩ | %He | ⟨%k, #HE⟩)
  · subst He
    ihave #HEOF := io.eof_of_init $$ Hio
    iapply rdErr_newVar _ _ _ (by simp) $$ HEOF Heof
  · subst He
    ihave #Hi := io.isInit_access $$ Hio
    icases Hi with ⟨-, -, -, -, -, #HU, -⟩
    iapply rdErr_newVar _ _ _ (by simp) $$ HU Hueof
  · ihave #Hn := errNE_resErr $$ HE
    ihave %Hnet := net.resErr_netErr _ _ _ _ _ _ _ $$ HE
    obtain ⟨-, Hne⟩ := Hnet
    obtain ⟨pe, rfl⟩ := Hne (by simp)
    iunfold rdErr
    iframe Hn
    ipureintro; exact ⟨_, pe, rfl⟩

/-- `err.Error()` of a sticky read error: some message. -/
theorem wp_rdErr_Error (T : go.GoType) (l : Loc) (Φ : val → IProp GF) :
    rdErr (interface.mkOk (go.GoType.PointerType T) #l) ⊢ ▷ (∀ msg : GoString, ⌜msg ≠ []⌝ -∗ Φ #msg) -∗
      WP (App (Val #(methods (go.GoType.PointerType T) go!"Error" #l)) (Val #())) {{ Φ }} := by
  iintro Hr HΦ
  iunfold rdErr at Hr
  icases Hr with ⟨#Hn, -⟩
  iunfold errNE at Hn
  icases Hn with ⟨%e, %He, -, #HW⟩
  cases He
  iapply HW $$ HΦ

/-- The reader predicate of a read at the acceptor's end after `R0`, and its accessor
(`read_au`). -/
theorem rd_acc_srv (W : RpcWorld GF) (a : GoString) (cn : Nat) (R0 : List w8) :
    ⊢ □ (∀ (got : List w8) (m : Nat),
      recvTokL (Gg := hG.goose_globalGS) cn true (reqProto (Gg := hG.goose_globalGS) W a)
        (R0 ++ got) -∗
      |={⊤,∅}=> ∃ st d, netEnd (extGlobalGS netExt (G := hG.goose_globalGS)) cn true st ∗
        netDir (extGlobalGS netExt (G := hG.goose_globalGS)) cn (!true) d ∗
        ∀ r d', ⌜ReadOutcome st d m r d'⌝ -∗
          netEnd (extGlobalGS netExt (G := hG.goose_globalGS)) cn true st -∗
          netDir (extGlobalGS netExt (G := hG.goose_globalGS)) cn (!true) d' ={∅,⊤}=∗
            recvTokL (Gg := hG.goose_globalGS) cn true (reqProto (Gg := hG.goose_globalGS) W a)
              (R0 ++ (got ++ r.got))) := by
  imodintro
  iintro %got %m HP
  imod read_au (Gg := hG.goose_globalGS) cn true _ _ m $$ HP with ⟨%st, %d, Hst, Hd, Hk⟩
  imodintro
  iexists st, d
  iframe Hst Hd
  iintro %r %d' %Hro Hst Hd
  imod Hk $$ %r %d' %Hro Hst Hd with ⟨HP, -⟩
  imodintro
  rw [← List.append_assoc]
  iexact HP

/-- The names of a connection are unique. -/
theorem isRpcConn_agree (W : RpcWorld GF) (a : GoString) (cn : Nat) (γ γ' : RpcConnNames) :
    isRpcConn (Gg := hG.goose_globalGS) W a cn γ ∗ isRpcConn (Gg := hG.goose_globalGS) W a cn γ' ⊢
      ⌜γ = γ'⌝ := by
  iintro ⟨Hc, Hc'⟩
  iunfold isRpcConn at Hc Hc'
  icases Hc with ⟨Hr, -⟩
  icases Hc' with ⟨Hr', -⟩
  iunfold regElem at Hr Hr'
  iapply ghostMapElem_agree _ _ _ _ _ _ $$ Hr Hr'

/-- The requests a reader's bytes `R` meet (their protocol fact): some `L` of the connection. -/
theorem req_of_read (W : RpcWorld GF) (a : GoString) (cn : Nat) (R : List w8) (hR : R ≠ []) :
    protoPrefix (reqProto (Gg := hG.goose_globalGS) W a) cn R ⊢
    ∃ (γ : RpcConnNames) (L : List RpcReq), isRpcConn (Gg := hG.goose_globalGS) W a cn γ ∗
      monoListLbOwn γ.reqs L ∗
      ⌜(∀ r ∈ L, reqOk r) ∧ L.length ≤ 2 ^ 64 ∧ R <+: W.hs a ++ reqsWire L⌝ := by
  iintro #Hpp
  iunfold protoPrefix at Hpp
  icases Hpp with (%Hnil | ⟨%ext, %Hext, #HP⟩)
  · exact absurd Hnil hR
  iunfold reqProto at HP
  icases HP with ⟨%γ, %L, #Hrpc, #Hlb, ⟨%HL, %Hlen, %Hpre⟩, -⟩
  iexists γ, L
  iframe Hrpc Hlb
  ipureintro; exact ⟨HL, Hlen, Hext.trans Hpre⟩

/-- A reader that has read past the dialer's handshake learns that the acceptor's answer was
written whole (`reqProto`: the dialer writes nothing more before it has it). -/
theorem hsAns_of_read (W : RpcWorld GF) (a : GoString) (cn : Nat) (R : List w8)
    (hR : ¬ R <+: W.hs a) :
    protoPrefix (reqProto (Gg := hG.goose_globalGS) W a) cn R ⊢
      sentLb (Gg := hG.goose_globalGS) cn true (W.hsAns a) := by
  iintro #Hpp
  iunfold protoPrefix at Hpp
  icases Hpp with (%Hnil | ⟨%ext, %Hext, #HP⟩)
  · subst Hnil; exact absurd List.nil_prefix hR
  iunfold reqProto at HP
  icases HP with ⟨%γ, %L, -, -, -, (%Hhs | #Hs)⟩
  · exact absurd (Hext.trans Hhs) hR
  · iexact Hs

/-- With the acceptor's fresh token, the reader claims its half of `ctr` (at `0`). -/
theorem claim_role (W : RpcWorld GF) (a : GoString) (cn : Nat) (γ : RpcConnNames) :
    £ 1 ∗ isRpcConn (Gg := hG.goose_globalGS) W a cn γ ∗ connFresh (Gg := hG.goose_globalGS) cn true ⊢
      |={⊤}=> ghostVar γ.ctr (1 : Qp).half 0 := by
  iintro ⟨Hlc, #Hrpc, Hfr⟩
  iunfold isRpcConn at Hrpc
  icases Hrpc with ⟨-, #Hinv⟩
  iinv Hinv with Hi Hclose
  imod lc_fupd_elim_later (E := ⊤ \ ↑connN) $$ Hlc Hi with Hi
  iunfold connInv at Hi
  icases Hi with ⟨%L, %k, %A, Hh, Hctr, HA, Hrole, %Hk, Hnamed, Hdeps, Hans⟩
  icases Hrole with (H0 | Hfr2)
  · imod Hclose $$ [Hh Hctr HA Hfr Hnamed Hdeps Hans] with -
    · inext
      iunfold connInv
      iexists L, k, A
      iframe Hh Hctr HA Hnamed Hdeps Hans
      isplitl [Hfr]
      · iright; iexact Hfr
      ipureintro; exact Hk
    imodintro; iexact H0
  · iexfalso
    iapply connFresh_excl (Gg := hG.goose_globalGS) cn true $$ [$Hfr $Hfr2]

/-- The reader takes request `k` (the `k`-th of the lower bound `L`) once: its deposit and the
right to answer it, `ans k ↦ none`. -/
theorem take_req (W : RpcWorld GF) (a : GoString) (cn : Nat) (γ : RpcConnNames) (k : Nat)
    (L : List RpcReq) (r : RpcReq) (hr : L[k]? = some r) :
    £ 1 ∗ isRpcConn (Gg := hG.goose_globalGS) W a cn γ ∗ ghostVar γ.ctr (1 : Qp).half k ∗
      monoListLbOwn γ.reqs L ⊢
    |={⊤}=> ghostVar γ.ctr (1 : Qp).half (k + 1) ∗ reqDeposit (Gg := hG.goose_globalGS) W a r ∗
      ghostMapElem γ.ans k (DFrac.own 1) (none : Option (GoString × List w8)) := by
  iintro ⟨Hlc, #Hrpc, Hmy, #Hlb⟩
  iunfold isRpcConn at Hrpc
  icases Hrpc with ⟨-, #Hinv⟩
  iinv Hinv with Hi Hclose
  imod lc_fupd_elim_later (E := ⊤ \ ↑connN) $$ Hlc Hi with Hi
  iunfold connInv at Hi
  icases Hi with ⟨%L', %k', %A, Hh, Hctr, HA, Hrole, %Hk, Hnamed, Hdeps, Hans⟩
  ihave %Heq := ghostVar_agree $$ Hctr Hmy
  subst Heq
  ihave %Hpre := mono_list_auth_lb_valid $$ Hh Hlb
  obtain ⟨-, Hpre⟩ := Hpre
  have hr' : L'[k']? = some r := by
    obtain ⟨t, rfl⟩ := Hpre
    rw [List.getElem?_append_left (List.getElem?_eq_some_iff.1 hr).1]; exact hr
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
      have := Hk.2 k' (by simp [h])
      omega
  imod ghost_map_insert k' (none : Option (GoString × List w8)) hAk $$ HA with ⟨HA, Hel⟩
  imod ghostVar_update_halves (k' + 1) γ.ctr k' k' $$ Hctr Hmy with ⟨Hctr, Hmy⟩
  imod Hclose $$ [Hh Hctr HA Hrole Hnamed Hdeps Hans] with -
  · inext
    iunfold connInv
    iexists L', k' + 1, A.insert k' none
    iframe Hh Hctr HA Hrole Hnamed Hdeps
    isplitr
    · ipureintro
      refine ⟨hkL, fun i hi => ?_⟩
      by_cases hik : i = k'
      · omega
      · have : (A.lookup i).isSome := by
          rwa [GMap.lookup_insert_ne _ _ (Ne.symm hik)] at hi
        have := Hk.2 i this
        omega
    · iapply (BigSepM.bigSepM_insert (Φ := fun i o => answerRes (Gg := hG.goose_globalGS) L' i o)
        (by rw [gmap_get?_eq]; exact hAk)).2
      iframe Hans
      iunfold answerRes
      itrivial
  imodintro
  iframe Hmy Hdep Hel

/-- After the frames `ps` of the first `k` requests, a header frame `h`: the reader takes request
`k` (its role claimed at the first), whose header `h` is. -/
theorem req_hdr (W : RpcWorld GF) (a : GoString) (cn : Nat) (ps : List (List w8)) (k : Nat)
    (h : List w8) (hps : ps.length = 2 * k) (hb : ∀ q ∈ ps, q.length < 2 ^ 63)
    (hh : h.length < 2 ^ 63) :
    £ 1 ∗ £ 1 ∗
      protoPrefix (reqProto (Gg := hG.goose_globalGS) W a) cn (W.hs a ++ framesOf (ps ++ [h])) ∗
      ((⌜k = 0⌝ ∗ connFresh (Gg := hG.goose_globalGS) cn true) ∨
        ∃ γ : RpcConnNames, isRpcConn (Gg := hG.goose_globalGS) W a cn γ ∗
          ghostVar γ.ctr (1 : Qp).half k) ⊢
    |={⊤}=> ∃ (γ : RpcConnNames) (L : List RpcReq) (r : RpcReq),
      isRpcConn (Gg := hG.goose_globalGS) W a cn γ ∗ monoListLbOwn γ.reqs L ∗
      ⌜L[k]? = some r ∧ h = reqHdr (W64 k) r.sm ∧ k < 2 ^ 64 ∧ reqOk r⌝ ∗
      ghostVar γ.ctr (1 : Qp).half (k + 1) ∗ reqDeposit (Gg := hG.goose_globalGS) W a r ∗
      ghostMapElem γ.ans k (DFrac.own 1) (none : Option (GoString × List w8)) := by
  iintro ⟨Hlc1, Hlc2, #Hpp, Hrole⟩
  icases req_of_read W a cn _ (List.append_ne_nil_of_right_ne_nil _ (framesOf_snoc_ne ps h)) $$ Hpp
    with ⟨%γ, %L, #Hrpc, #Hlb, ⟨%HL, %Hlen, %Hpre⟩⟩
  obtain ⟨r, hr, hr0⟩ := req_next L ps h k 0 (by omega) (by omega) HL hb hh
    ((List.prefix_append_right_inj _).1 Hpre)
  have hrh : h = reqHdr (W64 k) r.sm := by simp at hr0; exact hr0.symm
  have hkL : k < L.length := (List.getElem?_eq_some_iff.1 hr).1
  ihave Hctr : (|={⊤}=> ghostVar γ.ctr (1 : Qp).half k : IProp GF) $$ [Hlc1 Hrole]
  · icases Hrole with (⟨%Hk0, Hfr⟩ | ⟨%γ', #Hrpc', Hc⟩)
    · subst Hk0
      iapply claim_role W a cn γ $$ [$Hlc1 $Hrpc $Hfr]
    · ihave %Hg := isRpcConn_agree W a cn γ γ' $$ [$Hrpc $Hrpc']
      subst Hg
      imodintro; iexact Hc
  imod Hctr
  imod take_req W a cn γ k L r hr $$ [$Hlc2 $Hrpc $Hctr $Hlb] with ⟨Hctr, Hdep, Hel⟩
  imodintro
  iexists γ, L, r
  iframe Hrpc Hlb Hctr Hdep Hel
  ipureintro
  exact ⟨hr, hrh, by omega, HL r (List.mem_of_getElem? hr)⟩

/-- After the frames `ps` of the first `k` requests and the header of request `k` (the `k`-th of
the lower bound `L`), a body frame `b`: request `k`'s argument bytes. -/
theorem req_body (W : RpcWorld GF) (a : GoString) (cn : Nat) (γ : RpcConnNames)
    (L : List RpcReq) (r : RpcReq) (ps : List (List w8)) (k : Nat) (h b : List w8)
    (hr : L[k]? = some r) (hps : ps.length = 2 * k) (hb : ∀ q ∈ ps, q.length < 2 ^ 63)
    (hh : h.length < 2 ^ 63) (hbl : b.length < 2 ^ 63) :
    isRpcConn (Gg := hG.goose_globalGS) W a cn γ ∗ monoListLbOwn γ.reqs L ∗
      protoPrefix (reqProto (Gg := hG.goose_globalGS) W a) cn
        (W.hs a ++ framesOf (ps ++ [h] ++ [b])) ⊢
    ⌜b = r.body⌝ := by
  iintro ⟨#Hrpc, #Hlb, #Hpp⟩
  icases req_of_read W a cn _
    (List.append_ne_nil_of_right_ne_nil _ (framesOf_snoc_ne (ps ++ [h]) b)) $$ Hpp
    with ⟨%γ', %L', #Hrpc', #Hlb', ⟨%HL, %Hlen, %Hpre⟩⟩
  ihave %Hg := isRpcConn_agree W a cn γ γ' $$ [$Hrpc $Hrpc']
  subst Hg
  ihave %Hc := mono_list_lb_valid $$ Hlb Hlb'
  obtain ⟨r', hr', hr1⟩ := req_next L' (ps ++ [h]) b k 1 (by omega) (by simp; omega) HL
    (by intro q hq; simp at hq; rcases hq with hq | rfl; exact hb q hq; exact hh) hbl
    ((List.prefix_append_right_inj _).1 Hpre)
  have hrr : r' = r := by
    rcases Hc with ⟨t, rfl⟩ | ⟨t, rfl⟩
    · rw [List.getElem?_append_left (List.getElem?_eq_some_iff.1 hr).1, hr] at hr'
      exact (Option.some.inj hr').symm
    · rw [List.getElem?_append_left (List.getElem?_eq_some_iff.1 hr').1, hr'] at hr
      exact Option.some.inj hr
  subst hrr
  ipureintro
  simp at hr1; exact hr1.symm

/-- The guard of a request's body read (`ReadRequestBody`'s): after the frames `ps` of the first
`k` requests and the header `h` of request `k` (`r`, the `k`-th of `L`), the body frame read is
its argument bytes, one step later. -/
theorem req_guard (W : RpcWorld GF) (a : GoString) (cn : Nat) (γ : RpcConnNames)
    (L : List RpcReq) (r : RpcReq) (ps : List (List w8)) (k : Nat) (h : List w8)
    (hr : L[k]? = some r) (hps : ps.length = 2 * k) (hb : ∀ q ∈ ps, q.length < 2 ^ 63)
    (hh : h.length < 2 ^ 63) :
    isRpcConn (Gg := hG.goose_globalGS) W a cn γ ∗ monoListLbOwn γ.reqs L ⊢
    □ (∀ pl : List w8, ⌜pl.length ≤ maxFrameN⌝ -∗
      recvTokL (Gg := hG.goose_globalGS) cn true (reqProto (Gg := hG.goose_globalGS) W a)
        (W.hs a ++ framesOf (ps ++ [h]) ++ frameOf pl) -∗
      ▷ (recvTokL (Gg := hG.goose_globalGS) cn true (reqProto (Gg := hG.goose_globalGS) W a)
          (W.hs a ++ framesOf (ps ++ [h]) ++ frameOf pl) ∗ ⌜pl = r.body⌝)) := by
  iintro ⟨#Hrpc, #Hlb⟩
  imodintro
  iintro %pl %Hpl HP
  ihave HrL := recvTokL_later (Gg := hG.goose_globalGS) cn true _ _ $$ HP
  inext
  icases recvTok_proto (Gg := hG.goose_globalGS) cn true _ _ $$ HrL with ⟨HrT, #Hpp⟩
  have hpl : pl.length < 2 ^ 63 := by unfold maxFrameN at Hpl; omega
  have hfr : W.hs a ++ framesOf (ps ++ [h]) ++ frameOf pl =
      W.hs a ++ framesOf (ps ++ [h] ++ [pl]) := by
    rw [framesOf_append (ps ++ [h]) [pl], framesOf_cons, framesOf_nil, List.append_nil,
      List.append_assoc]
  rw [hfr]
  ihave %Hbody := req_body W a cn γ L r ps k h pl hr hps hb hh hpl $$ [$Hrpc $Hlb $Hpp]
  rw [← hfr]
  isplitl [HrT]
  · iapply recvTok_L $$ HrT
  ipureintro; exact Hbody

/-- The right to answer a request says the handshake's answer was written whole. -/
theorem ansPend_hsAns (W : RpcWorld GF) (a : GoString) (cn : Nat) (k : Nat) (sm : GoString)
    (Φ : List w8 → GoString → IProp GF) :
    ansPend W a cn k sm Φ ⊢
      ansPend W a cn k sm Φ ∗ sentLb (Gg := hG.goose_globalGS) cn true (W.hsAns a) := by
  iintro Hp
  iunfold ansPend at Hp
  icases Hp with ⟨%γ, %L, %r, #Hrpc, #Hlb, %Hp, Hel, #Hpost, #Hs⟩
  isplitl
  · iunfold ansPend
    iexists γ, L, r
    iframe Hrpc Hlb Hel Hpost Hs
    ipureintro; exact Hp
  · iexact Hs

/-- The answer to request `k`, from the right to answer it and the continuation's `Φ reply msg`:
its persistent `ans` element; the continuation goes to the connection for the client. -/
theorem answer (W : RpcWorld GF) (a : GoString) (cn : Nat) (k : Nat) (sm : GoString)
    (Φ : List w8 → GoString → IProp GF) (msg : GoString) (reply : List w8) :
    £ 1 ∗ ansPend W a cn k sm Φ ∗ Φ reply msg ⊢
    |={⊤}=> ∃ γ : RpcConnNames, isRpcConn (Gg := hG.goose_globalGS) W a cn γ ∗
      ghostMapElem γ.ans k .discard (some (msg, reply)) ∗ ⌜k < 2 ^ 64⌝ := by
  iintro ⟨Hlc, Hp, HΦ⟩
  iunfold ansPend at Hp
  icases Hp with ⟨%γ, %L, %r, #Hrpc, #Hlb, ⟨%hr, %hsm, %hk⟩, Hel, #Hpost, -⟩
  ihave #Hrpc' := Hrpc
  iunfold isRpcConn at Hrpc'
  icases Hrpc' with ⟨-, #Hinv⟩
  iinv Hinv with Hi Hclose
  imod lc_fupd_elim_later (E := ⊤ \ ↑connN) $$ Hlc Hi with Hi
  iunfold connInv at Hi
  icases Hi with ⟨%L', %k', %A, Hh, Hctr, HA, Hrole, %Hk, Hnamed, Hdeps, Hans⟩
  ihave %HAk := ghost_map_lookup $$ HA Hel
  ihave %Hpre := mono_list_auth_lb_valid $$ Hh Hlb
  obtain ⟨-, Hpre⟩ := Hpre
  have hr' : L'[k]? = some r := by
    obtain ⟨t, rfl⟩ := Hpre
    rw [List.getElem?_append_left (List.getElem?_eq_some_iff.1 hr).1]; exact hr
  imod ghost_map_update (some (msg, reply)) $$ HA Hel with ⟨HA, Hel⟩
  imod ghostMapElem_persist $$ Hel with #Hel
  imod Hclose $$ [Hh Hctr HA Hrole Hnamed Hdeps Hans HΦ] with -
  · inext
    iunfold connInv
    iexists L', k', A.insert k (some (msg, reply))
    iframe Hh Hctr HA Hrole Hnamed Hdeps
    isplitr
    · ipureintro
      refine ⟨Hk.1, fun i hi => ?_⟩
      by_cases hik : i = k
      · subst hik; exact Hk.2 i (by simp [HAk])
      · exact Hk.2 i (by rwa [GMap.lookup_insert_ne _ _ (Ne.symm hik)] at hi)
    · ihave ⟨-, Hback⟩ := (BigSepM.bigSepM_insert_acc (Φ := fun i o => answerRes (Gg := hG.goose_globalGS) L' i o)
        (by rw [gmap_get?_eq]; exact HAk)) $$ Hans
      iapply Hback
      iunfold answerRes
      iexists r
      isplitr
      · ipureintro; exact hr'
      ileft
      iunfold replyEscrow
      iexists Φ
      iframe Hpost HΦ
  imodintro
  iexists γ
  iframe Hrpc Hel
  ipureintro; exact hk

/-- A response written: the answers `Rs` recorded so far and the new answer `x` (of the
connection `γ`, recorded) meet the acceptor's protocol, and the record grows by `x`. -/
theorem resp_step (W : RpcWorld GF) (a : GoString) (cn : Nat) (γ : RpcConnNames) (Rs : List Ans)
    (x : Ans) (hok : ∀ y ∈ Rs ++ [x], ansOk y) :
    isRpcConn (Gg := hG.goose_globalGS) W a cn γ ∗ sentLb (Gg := hG.goose_globalGS) cn false (W.hs a) ∗
      ghostMapElem γ.ans x.idx .discard (some (x.msg, x.reply)) ∗ ansRec W a cn Rs ⊢
    (□ respProto (Gg := hG.goose_globalGS) W a cn (W.hsAns a ++ respsWire (Rs ++ [x]))) ∗
      ansRec W a cn (Rs ++ [x]) := by
  iintro ⟨#Hrpc, #Hsl, #Hel, Hrec⟩
  ihave #Hels : ([∗list] y ∈ Rs ++ [x], ghostMapElem γ.ans y.idx .discard (some (y.msg, y.reply)) :
      IProp GF) $$ [Hrec]
  · iunfold ansRec at Hrec
    icases Hrec with (%HRs | ⟨%γ', #Hrpc', #HRs⟩)
    · subst HRs
      simp only [List.nil_append]
      iapply BigSepL.bigSepL_singleton.2; iexact Hel
    · ihave %Hg := isRpcConn_agree W a cn γ γ' $$ [$Hrpc $Hrpc']
      subst Hg
      iapply BigSepL.bigSepL_snoc.2
      iframe HRs Hel
  isplitr
  · imodintro
    iunfold respProto
    iexists γ, Rs ++ [x]
    iframe Hrpc Hels
    isplitr
    · ipureintro
      exact ⟨hok, List.prefix_refl _⟩
    iright; iexact Hsl
  · iunfold ansRec
    iright
    iexists γ
    iframe Hrpc Hels

end ghost

end net.rpc
end Perennial
