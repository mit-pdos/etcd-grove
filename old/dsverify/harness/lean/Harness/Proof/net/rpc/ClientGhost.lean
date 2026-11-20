/-
The ghost lemmas of the rpc client (`ClientDefs.lean`): pure facts about the wire format and the
reader's choice of the request a response answers, and the client's ghost updates (allocating a
client, inserting a pending call, appending a request, consuming a response).

**Which request a response answers.** The acceptor's protocol (`respProto`) says the response
stream is frames answering distinct requests `Rs` of the connection, but each read learns its own
`Rs` (an existential), and two requests with the same sequence number (after `2 ^ 64` calls) and
the same answer have the same frame. So the reader keeps its own list `C` of the answers it
consumed (distinct indices, each with its persistent answer): given the next frame, among the
first `|C| + 1` answers of `Rs` with that frame's payload there is one more than among `C`'s
(the payloads of `C` are those of `Rs`'s first `|C|`), and an answer is fixed by its index
(`ans` is a ghost map); so one of them is not in `C` (`pick_fresh`).
-/
module

public import Harness.Proof.net.rpc.ClientDefs

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode NetConn

namespace net.rpc

/-! ## Pure facts -/

theorem framesOf_singleton (p : List w8) : framesOf [p] = frameOf p := by
  simp [framesOf]

theorem sint_nat_lt (x : w64) : sint.nat x < 2 ^ 63 := by
  unfold sint.nat; have := BitVec.toInt_lt (x := x); simp at this; omega

theorem respMsg_stable {L L' : List RpcReq} (x : Ans) (hx : x.1 < L.length) (h : L <+: L') :
    respMsg L x = respMsg L' x := by
  unfold respMsg
  obtain ⟨t, rfl⟩ := h
  rw [List.getElem?_append_left hx]

theorem respMsg_map_stable {L L' : List RpcReq} (C : List Ans) (hC : ∀ y ∈ C, y.1 < L.length)
    (h : L <+: L') : C.map (respMsg L) = C.map (respMsg L') :=
  List.map_congr_left (fun y hy => respMsg_stable y (hC y hy) h)

theorem respMsg_of_lt {L : List RpcReq} (x : Ans) (hx : x.1 < L.length) :
    respMsg L x = msgOf L[x.1].seq x.2.1 x.2.2 := by
  unfold respMsg
  rw [List.getElem?_eq_getElem hx]
  rfl

theorem nodup_of_map_fst {A B : Type} (l : List (A × B)) (h : (l.map Prod.fst).Nodup) :
    l.Nodup := by
  induction l with
  | nil => exact List.nodup_nil
  | cons a t ih =>
    simp only [List.map_cons, List.nodup_cons] at h ⊢
    exact ⟨fun ha => h.1 (List.mem_map_of_mem ha), ih h.2⟩

/-- Among the first `|C| + 1` answers of `Rs` there is one not in `C` with the payload of the
`|C|`-th (see the file header). -/
theorem pick_fresh {β : Type} [DecidableEq β] (f : Ans → β) (Rs C : List Ans)
    (hRs : (Rs.map Prod.fst).Nodup) (_hC : (C.map Prod.fst).Nodup)
    (hfun : ∀ x ∈ Rs, ∀ y ∈ C, x.1 = y.1 → x = y)
    (hQ : (Rs.take C.length).map f = C.map f) (hk : C.length < Rs.length) :
    ∃ x ∈ Rs, x.1 ∉ C.map Prod.fst ∧ f x = f Rs[C.length] := by
  classical
  refine Classical.byContradiction fun hno => ?_
  have hno' : ∀ x ∈ Rs, x.1 ∉ C.map Prod.fst → f x ≠ f Rs[C.length] :=
    fun x hx hn hf => hno ⟨x, hx, hn, hf⟩
  let p := f Rs[C.length]
  let X := (Rs.take (C.length + 1)).filter (fun x => decide (f x = p))
  let Y := C.filter (fun x => decide (f x = p))
  have hRsnd : Rs.Nodup := nodup_of_map_fst Rs hRs
  have hXnd : X.Nodup := ((List.take_sublist _ _).nodup hRsnd).filter _
  have hXY : X ⊆ Y := by
    intro x hx
    have hx' := List.mem_filter.1 hx
    obtain ⟨hxT, hfx⟩ := hx'
    have hfx' : f x = p := of_decide_eq_true hfx
    have hxR : x ∈ Rs := List.mem_of_mem_take hxT
    have hin : x.1 ∈ C.map Prod.fst :=
      Classical.byContradiction fun hn => hno' x hxR hn hfx'
    obtain ⟨y, hy, hyx⟩ := List.mem_map.1 hin
    have := hfun x hxR y hy hyx.symm
    subst this
    exact List.mem_filter.2 ⟨hy, hfx⟩
  have hle : X.length ≤ Y.length := (List.subperm_of_subset hXnd hXY).length_le
  have hcount : ∀ l : List Ans,
      (l.filter (fun x => decide (f x = p))).length = (l.map f).count p := by
    intro l
    rw [List.count_eq_countP, List.countP_map, ← List.countP_eq_length_filter]
    congr 1
  have hX : X.length = Y.length + 1 := by
    show ((Rs.take (C.length + 1)).filter (fun x => decide (f x = p))).length =
      (C.filter (fun x => decide (f x = p))).length + 1
    rw [List.take_add_one, List.getElem?_eq_getElem hk, Option.toList_some, List.filter_append,
      List.length_append, hcount, hcount, hQ, ← hcount]
    simp [p]
  omega

/-- The reader's next frame `pl` (after the frames of its consumed answers `C`), in a stream
whose protocol extension `ext` frames the answers `Rs`: it answers one of `Rs` not in `C`. -/
theorem client_resp_next {L' Lr Lm : List RpcReq} {Rs C : List Ans} {pl ext : List w8}
    (hb : ∀ q ∈ Rs.map (respMsg L'), q.length < 2 ^ 63) (hpl : pl.length < 2 ^ 63)
    (hCb : ∀ q ∈ C.map (respMsg Lr), q.length < 2 ^ 63)
    (hRsLt : ∀ x ∈ Rs, x.1 < L'.length) (hCLt : ∀ y ∈ C, y.1 < Lr.length)
    (h1 : L' <+: Lm) (h2 : Lr <+: Lm)
    (hRs : (Rs.map Prod.fst).Nodup) (hC : (C.map Prod.fst).Nodup)
    (hfun : ∀ x ∈ Rs, ∀ y ∈ C, x.1 = y.1 → x = y)
    (h : connectedBytes ++ framesOf (C.map (respMsg Lr)) ++ frameOf pl <+: ext)
    (hext : ext <+: connectedBytes ++ framesOf (Rs.map (respMsg L'))) :
    ∃ x ∈ Rs, x.1 ∉ C.map Prod.fst ∧ respMsg Lm x = pl := by
  have h3 := h.trans hext
  rw [List.append_assoc] at h3
  have h4 := (List.prefix_append_right_inj connectedBytes).1 h3
  rw [respMsg_map_stable C hCLt h2, respMsg_map_stable Rs hRsLt h1] at h4
  rw [respMsg_map_stable Rs hRsLt h1] at hb
  rw [respMsg_map_stable C hCLt h2] at hCb
  obtain ⟨htake, hget⟩ := framesOf_next hCb hb hpl h4
  rw [List.length_map] at htake hget
  have hk : C.length < Rs.length := by
    have := (List.getElem?_eq_some_iff.1 hget).1
    simpa using this
  rw [List.getElem?_map, List.getElem?_eq_getElem hk] at hget
  simp only [Option.map_some, Option.some.injEq] at hget
  rw [← List.map_take] at htake
  obtain ⟨x, hx, hxC, hfx⟩ := pick_fresh (respMsg Lm) Rs C hRs hC hfun htake hk
  exact ⟨x, hx, hxC, hfx.trans hget⟩

/-- A stream holding `connectedBytes` and a frame is not a prefix of `connectedBytes`. -/
theorem not_prefix_connected (bs pl : List w8) :
    ¬ (connectedBytes ++ bs ++ frameOf pl <+: connectedBytes) := by
  intro h
  have := h.length_le
  simp only [List.length_append, frameOf_length] at this
  omega

/-! ## Ghost lemmas -/

section ghost
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netConnExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [net.Assumptions] [net.model.Assumptions] [net.rpc.Assumptions]
variable [RpcKit] [RpcCodec GF]



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

theorem ans_agree1 (γ : GName) (x : Ans) (C : List Ans) :
    ⊢ (ghostMapElem γ x.1 .discard (some x.2) : IProp GF) -∗
      ([∗list] y ∈ C, ghostMapElem γ y.1 .discard (some y.2)) -∗
      ⌜∀ y ∈ C, x.1 = y.1 → x = y⌝ := by
  induction C with
  | nil =>
    iintro - -
    ipureintro; intro y hy; cases hy
  | cons y C ih =>
    iintro #Hx Hl
    icases BigSepL.bigSepL_cons.1 $$ Hl with ⟨#Hy, #Hl⟩
    ihave %IH := ih $$ Hx Hl
    by_cases hxy : x.1 = y.1
    · obtain ⟨x1, x2⟩ := x
      obtain ⟨y1, y2⟩ := y
      simp only at hxy
      subst hxy
      ihave %Hag := ghostMapElem_agree _ _ _ _ _ _ $$ Hx Hy
      ipureintro
      intro z hz hxz
      rcases List.mem_cons.1 hz with rfl | hz
      · simp only [Option.some.injEq] at Hag; rw [Hag]
      · exact IH z hz hxz
    · ipureintro
      intro z hz hxz
      rcases List.mem_cons.1 hz with rfl | hz
      · exact absurd hxz hxy
      · exact IH z hz hxz

theorem ans_agree (γ : GName) (Rs C : List Ans) :
    ⊢ ([∗list] x ∈ Rs, ghostMapElem γ x.1 .discard (some x.2) : IProp GF) -∗
      ([∗list] y ∈ C, ghostMapElem γ y.1 .discard (some y.2)) -∗
      ⌜∀ x ∈ Rs, ∀ y ∈ C, x.1 = y.1 → x = y⌝ := by
  induction Rs with
  | nil =>
    iintro - -
    ipureintro; intro x hx; cases hx
  | cons x Rs ih =>
    iintro Hr #Hl
    icases BigSepL.bigSepL_cons.1 $$ Hr with ⟨#Hx, #Hr⟩
    ihave %IH := ih $$ Hr Hl
    ihave %H1 := ans_agree1 γ x C $$ Hx Hl
    ipureintro
    intro z hz
    rcases List.mem_cons.1 hz with rfl | hz
    · exact H1
    · exact IH z hz

theorem store_take (γn : ClientNames) (C : List Nat) (L : List RpcReq) (j : Nat) (r : RpcReq)
    (hj : j ∉ C) (hr : L[j]? = some r) :
    store (GF := GF) γn C L ⊢ storeRes γn r ∗ store γn (C ++ [j]) L := by
  unfold store
  refine (BigSepL.bigSepL_delete_cond hr).1.trans ?_
  simp only [hj, ite_false]
  refine sep_mono_right (BigSepL.bigSepL_mono_of_forall fun {k y} => ?_)
  by_cases hk : k = j
  · subst hk; simp only [ite_true, List.mem_append, List.mem_singleton, or_true]
    exact true_intro
  · have : (k ∈ C ++ [j]) ↔ k ∈ C := by simp [hk]
    simp only [hk, ite_false]
    by_cases hkC : k ∈ C
    · simp only [hkC, ite_true, List.mem_append, true_or]; exact .rfl
    · have : k ∉ C ++ [j] := by simp [hk, hkC]
      simp only [hkC, this, ite_false]; exact .rfl

theorem store_snoc (γn : ClientNames) (C : List Nat) (L : List RpcReq) (r : RpcReq)
    (hn : L.length ∉ C) :
    store (GF := GF) γn C L ∗ storeRes γn r ⊢ store γn C (L ++ [r]) := by
  unfold store
  refine (sep_mono_right ?_).trans BigSepL.bigSepL_snoc.2
  simp only [hn, ite_false]; exact .rfl

theorem answerRes_snoc (L : List RpcReq) (r : RpcReq) (i : Nat) (hi : i < L.length)
    (o : Option (GoString × List w8)) :
    answerRes (GF := GF) L i o ⊢ answerRes (L ++ [r]) i o := by
  unfold answerRes
  rcases o with _ | ⟨msg, rep⟩
  · exact .rfl
  · simp only
    rw [List.getElem?_append_left hi]

/-- Appending request `r` (the caller's, holding `sending`): the connection's list and the
client's copy grow, the request's deposit goes to the connection, the caller's element half
to the store. -/
theorem client_append (W : RpcWorld GF) (a : GoString) (cid : w64) (γn : ClientNames)
    (L : List RpcReq) (r : RpcReq) :
    ⊢ inv cliN (cliInv γn) -∗ isRpcConn W a cid γn.conn -∗
      monoListAuthOwn γn.cl (1 : Qp).half L -∗ storeRes γn r -∗ reqDeposit W a r ={⊤}=∗
      monoListAuthOwn γn.cl (1 : Qp).half (L ++ [r]) ∗ monoListLbOwn γn.conn.reqs (L ++ [r]) := by
  unfold isRpcConn
  iintro #Hci ⟨#Hreg, #Hconn⟩ Hcl Hst Hdep
  iinv Hci with Hi Hclose1
  unfold cliInv
  icases Hi with ⟨%L1, %P, %C, >Hreqs, >Hcl1, >Hpend, >Hcons, >%HC, Hstore⟩
  iinv Hconn with Hj Hclose2
  · exact mask_ndot_ne' rpcN "conn" "client" (by decide)
  unfold connInv
  icases Hj with ⟨%L2, %k, %A, >Hreqs2, Hctr, HA, Hclaim, >%Hk, Hdeps, Hans⟩
  imod ml_halves_update γn.cl (List.prefix_append L [r]) $$ Hcl Hcl1 with ⟨%H1, Hcl, Hcl1, -⟩
  subst H1
  imod ml_halves_update γn.conn.reqs (List.prefix_append L [r]) $$ Hreqs Hreqs2
    with ⟨%H2, Hreqs, Hreqs2, #Hlb⟩
  subst H2
  imod Hclose2 $$ [Hreqs2 Hctr HA Hclaim Hdeps Hans Hdep] with -
  · inext
    iexists L ++ [r], k, A
    iframe
    isplitr
    · ipureintro
      refine ⟨by simp; omega, Hk.2⟩
    isplitl [Hdeps Hdep]
    · rw [List.drop_append_of_le_length Hk.1]
      iapply BigSepL.bigSepL_snoc.2
      iframe
    · iapply BigSepM.bigSepM_mono (fun {i o} hio => answerRes_snoc L r i ?_ o) $$ Hans
      have := Hk.2 i (by show (get? A i).isSome = true; rw [hio]; rfl)
      omega
  imod Hclose1 $$ [Hreqs Hcl1 Hpend Hcons Hstore Hst] with -
  · inext
    iexists L ++ [r], P, C
    iframe
    isplitr
    · ipureintro
      refine ⟨fun y hy => by have := HC.1 y hy; simp; omega, HC.2⟩
    iapply store_snoc γn _ L r ?_ $$ [$Hstore $Hst]
    intro hm
    obtain ⟨y, hy, hyx⟩ := List.mem_map.1 hm
    have := HC.1 y hy
    omega
  imodintro
  iframe
  iexact Hlb

/-- Inserting a pending call (the caller, holding `mu` and `sending`, while up): its entry's
element half and resources go to the map entry, the other half to the caller. -/
theorem client_insert (γn : ClientNames) (m : GMap w64 Loc) (s : w64) (e : PEntry)
    (lst0 : List (w64 × PEntry)) (hs : m !! s = none) :
    ⊢ inv cliN (cliInv γn) -∗ pendAlive (GF := GF) γn m false -∗
      ghostVar γn.last (1 : Qp).half lst0 -∗ callRes e ={⊤}=∗
      pendAlive γn (<[s := e.1]> m) false ∗ ghostVar γn.last (1 : Qp).half [(s, e)] ∗
      ghostMapElem γn.pend s (DFrac.own (1 : Qp).half) e := by
  iintro #Hci Hal Hlast Hres
  unfold pendAlive
  icases Hal with ⟨%P, %lst, Hpend, Hlast2, %HP, Hm⟩
  imod ghostVar_update_halves [(s, e)] γn.last _ _ $$ Hlast Hlast2 with ⟨Hlast, Hlast2⟩
  iinv Hci with Hi Hclose1
  unfold cliInv
  icases Hi with ⟨%L1, %P1, %C, >Hreqs, >Hcl1, >Hpend1, >Hcons, >%HC, Hstore⟩
  ihave %Hag := ghostMapAuth_agree _ _ _ _ _ $$ Hpend Hpend1
  obtain ⟨-, rfl⟩ := Hag
  have hPs : P !! s = none := by
    cases h : P !! s with
    | none => rfl
    | some _ => exact absurd hs (HP.2 rfl s (by rw [h]; simp))
  ihave Hf := (ghostMapAuth_halves γn.pend P).2 $$ [$Hpend $Hpend1]
  imod ghost_map_insert s e hPs $$ Hf with ⟨Hf, He⟩
  icases (ghostMapAuth_halves γn.pend _).1 $$ Hf with ⟨Hpend, Hpend1⟩
  icases (ghostMapElem_halves γn.pend s e).1 $$ He with ⟨He1, He2⟩
  imod Hclose1 $$ [Hreqs Hcl1 Hpend1 Hcons Hstore] with -
  · inext
    iexists L1, P.insert s e, C
    iframe
    ipureintro; exact HC
  imodintro
  iframe Hlast He2
  iframe Hlast2
  iexists P.insert s e
  iframe Hpend
  isplitr
  · ipureintro
    refine ⟨?_, ?_⟩
    · intro t f ht
      simp only [List.mem_singleton, Prod.mk.injEq] at ht
      obtain ⟨rfl, rfl⟩ := ht
      left; exact GMap.lookup_insert _ _ _
    · intro _ t ht
      by_cases hst : s = t
      · subst hst; rw [GMap.lookup_insert]; simp
      · rw [GMap.lookup_insert_ne _ _ hst] at ht ⊢
        exact HP.2 rfl t ht
  iapply (BigSepM.bigSepM_insert hs).2
  isplitl [He1 Hres]
  · iexists e
    iframe
    ipureintro; exact ⟨GMap.lookup_insert _ _ _, rfl⟩
  iapply BigSepM.bigSepM_mono (fun {t pc} htp => ?_) $$ Hm
  iintro ⟨%f, %hf, Hf, Hr⟩
  iexists f
  iframe
  ipureintro
  have hst : s ≠ t := fun h => by
    subst h; have : m !! s = some pc := htp
    rw [hs] at this; cases this
  rw [GMap.lookup_insert_ne _ _ hst]; exact hf

theorem pendAlive_shut (γn : ClientNames) (m : GMap w64 Loc) (sd : Bool) :
    pendAlive (GF := GF) γn m sd ⊢ pendAlive γn m true := by
  unfold pendAlive
  iintro ⟨%P, %lst, Hp, Hl, %HP, Hm⟩
  iexists P, lst
  iframe
  ipureintro
  exact ⟨HP.1, fun h => by cases h⟩

/-- A failed writer (holding the `last` half of its own insertion) withdraws its entry from the
map: its decoding resource comes back. -/
theorem client_withdraw (γn : ClientNames) (m : GMap w64 Loc) (s : w64) (pc : Loc) (e : PEntry)
    (D : IProp GF) (hm : m !! s = some pc) :
    ⊢ pendAlive (GF := GF) γn m true -∗ ghostVar γn.last (1 : Qp).half [(s, e)] -∗
      savedPropOwn e.2.2.2 .discard D -∗
      pendAlive γn (GMap.delete s m) true ∗ ghostVar γn.last (1 : Qp).half [(s, e)] ∗ ▷ D := by
  unfold pendAlive
  iintro ⟨%P, %lst, Hp, Hl2, %HP, Hm⟩ Hl #Hret
  ihave %Hlst := ghostVar_agree _ _ _ _ _ $$ Hl Hl2
  subst Hlst
  icases (BigSepM.bigSepM_delete (show get? m s = some pc from hm)).1 $$ Hm
    with ⟨⟨%e', %he', Helem, Hres⟩, Hm⟩
  have hee : e' = e := by
    rcases HP.1 s e (List.mem_singleton.2 rfl) with h | h
    · rw [h] at he'; exact (Option.some.inj he'.1).symm
    · rw [h] at he'; cases he'.1
  subst hee
  unfold callRes
  icases Hres with ⟨%ch, %reply, %γf, %Φ, %Θ, %D', -, -, -, -, -, -, #Hret', HD', -⟩
  ihave #Hag := saved_prop_agree _ _ _ _ _ $$ Hret Hret'
  isplitl [Hp Hl2 Hm]
  · iexists P, [(s, e')]
    iframe
    ipureintro; exact ⟨HP.1, fun h => by cases h⟩
  isplitl [Hl]
  · iexact Hl
  inext
  iapply internal_eq_rewrite_wand $$ Hag HD'

instance storeRes_timeless (γn : ClientNames) (r : RpcReq) :
    Timeless (storeRes (GF := GF) γn r) := by
  unfold storeRes; infer_instance

instance store_timeless (γn : ClientNames) (C : List Nat) (L : List RpcReq) :
    Timeless (store (GF := GF) γn C L) := by
  unfold store
  refine BigSepL.bigSepL_timeless (fun {k x} _ => ?_)
  by_cases h : k ∈ C
  · simp only [h, ite_true]; infer_instance
  · simp only [h, ite_false]; infer_instance

/-- The reader consumes its next frame `pl` (`msgOf seq msg b`): it answers request `i` of the
connection, not consumed before; the reader's list grows by `(i, msg, b)` and the request's
element half of the pending map comes out of the store. -/
theorem client_consume (W : RpcWorld GF) (a : GoString) (cid : w64) (γn : ClientNames)
    (C : List Ans) (Lr : List RpcReq) (ext pl : List w8) (seq : w64) (msg : GoString)
    (b : List w8) (hpl : pl = msgOf seq msg b) (hplb : pl.length < 2 ^ 63)
    (hCLt : ∀ y ∈ C, y.1 < Lr.length) (hCnd : (C.map Prod.fst).Nodup)
    (hCb : ∀ q ∈ C.map (respMsg Lr), q.length < 2 ^ 63)
    (hext : connectedBytes ++ framesOf (C.map (respMsg Lr)) ++ frameOf pl <+: ext) :
    ⊢ inv cliN (cliInv γn) -∗ isRpcConn W a cid γn.conn -∗ respProto W a cid ext -∗
      monoListAuthOwn γn.cons (1 : Qp).half C -∗ monoListLbOwn γn.conn.reqs Lr -∗
      ([∗list] y ∈ C, ghostMapElem γn.conn.ans y.1 .discard (some y.2)) ={⊤}=∗
      ∃ (i : Nat) (Lr' : List RpcReq) (r : RpcReq),
        ⌜r.seq = seq ∧ Lr'[i]? = some r ∧ (∀ y ∈ C ++ [(i, msg, b)], y.1 < Lr'.length) ∧
          ((C ++ [(i, msg, b)]).map Prod.fst).Nodup ∧
          (∀ q ∈ (C ++ [(i, msg, b)]).map (respMsg Lr'), q.length < 2 ^ 63) ∧
          framesOf ((C ++ [(i, msg, b)]).map (respMsg Lr')) =
            framesOf (C.map (respMsg Lr)) ++ frameOf pl⌝ ∗
        monoListAuthOwn γn.cons (1 : Qp).half (C ++ [(i, msg, b)]) ∗
        monoListLbOwn γn.conn.reqs Lr' ∗
        ([∗list] y ∈ C ++ [(i, msg, b)], ghostMapElem γn.conn.ans y.1 .discard (some y.2)) ∗
        storeRes γn r := by
  iintro #Hci #Hrpc Hp Hcons #HLr #HC
  unfold respProto
  icases Hp with (%Hpre | ⟨%γ', %L', %Rs, #Hrpc', #HL', #HRs, %HRs⟩)
  · exfalso
    rw [List.append_assoc] at hext
    exact not_prefix_connected _ _ (by rw [List.append_assoc]; exact hext.trans Hpre)
  obtain ⟨hRsnd, hRsLt, hRsb, hRspre⟩ := HRs
  unfold isRpcConn regElem
  icases Hrpc with ⟨#Hreg, -⟩
  icases Hrpc' with ⟨#Hreg', -⟩
  ihave %Hγ := ghostMapElem_agree _ _ _ _ _ _ $$ Hreg Hreg'
  subst Hγ
  ihave %hfun := ans_agree γn.conn.ans Rs C $$ HRs HC
  iinv Hci with Hi Hclose
  unfold cliInv
  icases Hi with ⟨%L, %P, %C1, >Hreqs, >Hcl1, >Hpend1, >Hcons1, >%HC1, >Hstore⟩
  ihave %HL'L := mono_list_auth_lb_valid _ _ _ _ $$ Hreqs HL'
  ihave %HLrL := mono_list_auth_lb_valid _ _ _ _ $$ Hreqs HLr
  ihave #HLb := monoListLbOwn_get _ _ _ $$ Hreqs
  obtain ⟨x, hxRs, hxC, hxpl⟩ := client_resp_next hRsb hplb hCb hRsLt hCLt HL'L.2 HLrL.2 hRsnd hCnd hfun
    hext hRspre
  have hxL : x.1 < L.length := by
    have := hRsLt x hxRs; have := HL'L.2.length_le; omega
  have hLx : L[x.1]? = some L[x.1] := List.getElem?_eq_getElem hxL
  rw [respMsg_of_lt x hxL, hpl] at hxpl
  have hlen : (msgOf L[x.1].seq x.2.1 x.2.2).length < 2 ^ 63 := by rw [hxpl, ← hpl]; exact hplb
  rw [msgOf_length] at hlen
  have hlen2 : msg.length < 2 ^ 63 := by
    have := msgOf_length seq msg b; rw [← hpl] at this; omega
  obtain ⟨hseq, hmsg, hb⟩ := msgOf_inj (by omega) hlen2 hxpl
  obtain ⟨i, xm, xb⟩ := x
  simp only at hmsg hb hseq hxL hLx hxC
  subst hmsg hb
  ihave #Hx := BigSepL.bigSepL_mem hxRs $$ HRs
  ihave %Hag := monoListAuthOwn_agree _ _ _ _ _ $$ Hcons Hcons1
  obtain ⟨-, rfl⟩ := Hag
  icases store_take γn (C.map Prod.fst) L i L[i] hxC hLx $$ Hstore with ⟨Hsr, Hstore⟩
  imod ml_halves_update γn.cons (List.prefix_append C [(i, xm, xb)]) $$ Hcons Hcons1
    with ⟨-, Hcons, Hcons1, -⟩
  have hnd : ((C ++ [(i, xm, xb)]).map Prod.fst).Nodup := by
    simp only [List.map_append, List.map_cons, List.map_nil]
    exact List.nodup_append.2 ⟨hCnd, List.nodup_cons.2 ⟨by simp, List.nodup_nil⟩,
      fun u hu v hv => by simp at hv; subst hv; exact fun h => hxC (h ▸ hu)⟩
  have hlt : ∀ y ∈ C ++ [(i, xm, xb)], y.1 < L.length := by
    intro y hy
    rcases List.mem_append.1 hy with hy | hy
    · have := hCLt y hy; have := HLrL.2.length_le; omega
    · simp at hy; subst hy; exact hxL
  imod Hclose $$ [Hreqs Hcl1 Hpend1 Hcons1 Hstore] with -
  · iexists L, P, C ++ [(i, xm, xb)]
    iframe
    isplitr
    · ipureintro; exact ⟨hlt, hnd⟩
    simp only [List.map_append, List.map_cons, List.map_nil]
    iexact Hstore
  have hmap : (C ++ [(i, xm, xb)]).map (respMsg L) = C.map (respMsg Lr) ++ [pl] := by
    rw [List.map_append, respMsg_map_stable C hCLt HLrL.2]
    simp only [List.map_cons, List.map_nil, respMsg_of_lt (i, xm, xb) hxL, hpl]
    rw [← hseq]
  imodintro
  iexists i, L, L[i]
  iframe
  isplitr
  · ipureintro
    refine ⟨hseq, hLx, hlt, hnd, ?_, ?_⟩
    · rw [hmap]; intro q hq
      rcases List.mem_append.1 hq with hq | hq
      · exact hCb q hq
      · simp at hq; subst hq; exact hplb
    · rw [hmap, framesOf_append, framesOf_singleton]
  isplitr
  · iexact HLb
  iapply BigSepL.bigSepL_snoc.2
  iframe #

/-- The reader takes the pending call of its request's entry `e` (under `s`): with the map
entry, its resources (the entry leaves the ghost map); with none, the client is shut down. -/
theorem client_take (γn : ClientNames) (m : GMap w64 Loc) (sd : Bool) (s : w64) (e : PEntry) :
    ⊢ inv cliN (cliInv γn) -∗ pendAlive (GF := GF) γn m sd -∗
      ghostMapElem γn.pend s (DFrac.own (1 : Qp).half) e ={⊤}=∗
      ((⌜m !! s = none ∧ sd = true⌝ ∗ pendAlive γn m sd) ∨
        (⌜m !! s = some e.1⌝ ∗ pendAlive γn (GMap.delete s m) sd ∗ callRes e)) := by
  iintro #Hci Hal He
  unfold pendAlive
  icases Hal with ⟨%P, %lst, Hp, Hl, %HP, Hm⟩
  ihave %HPs := ghost_map_lookup $$ Hp He
  cases hm : m !! s with
  | none =>
    cases sd with
    | false =>
      exfalso
      exact HP.2 rfl s (by show P.lookup s ≠ none; rw [HPs]; simp) hm
    | true =>
      imodintro
      ileft
      isplitr
      · ipureintro; exact ⟨rfl, rfl⟩
      iexists P, lst
      iframe
      ipureintro; exact HP
  | some pc =>
    icases (BigSepM.bigSepM_delete (show get? m s = some pc from hm)).1 $$ Hm
      with ⟨⟨%e', %he', He', Hres⟩, Hm⟩
    have hee : e' = e := by
      have h1 : P !! s = some e' := he'.1
      have h2 : P !! s = some e := HPs
      rw [h1] at h2; exact Option.some.inj h2
    subst hee
    iinv Hci with Hi Hclose
    unfold cliInv
    icases Hi with ⟨%L, %P1, %C, >Hreqs, >Hcl1, >Hpend1, >Hcons1, >%HC1, >Hstore⟩
    ihave %Hag := ghostMapAuth_agree _ _ _ _ _ $$ Hp Hpend1
    obtain ⟨-, rfl⟩ := Hag
    ihave Hf := (ghostMapAuth_halves γn.pend P).2 $$ [$Hp $Hpend1]
    ihave Hef := (ghostMapElem_halves γn.pend s e').2 $$ [$He $He']
    imod ghost_map_delete $$ Hf Hef with Hf
    icases (ghostMapAuth_halves γn.pend _).1 $$ Hf with ⟨Hp, Hpend1⟩
    imod Hclose $$ [Hreqs Hcl1 Hpend1 Hcons1 Hstore] with -
    · iexists L, P.delete s, C
      iframe
      ipureintro; exact HC1
    imodintro
    iright
    isplitr
    · ipureintro; rw [he'.2]
    iframe Hres
    iexists P.delete s, lst
    iframe
    isplitr
    · ipureintro
      refine ⟨?_, ?_⟩
      · intro t f ht
        by_cases hst : s = t
        · subst hst; right; exact GMap.lookup_delete _ _
        · rw [GMap.lookup_delete_ne _ hst]; exact HP.1 t f ht
      · intro hsd t ht
        by_cases hst : s = t
        · subst hst; exact absurd (GMap.lookup_delete _ _) ht
        · rw [GMap.lookup_delete_ne _ hst] at ht ⊢
          exact HP.2 hsd t ht
    iapply BigSepM.bigSepM_mono (fun {t pc'} htp => ?_) $$ Hm
    iintro ⟨%f, %hf, Hf, Hr⟩
    iexists f
    iframe
    ipureintro
    have hst : s ≠ t := fun h => by
      subst h; have : (GMap.delete s m) !! s = some pc' := htp
      rw [GMap.lookup_delete] at this; cases this
    rw [GMap.lookup_delete_ne _ hst]; exact hf

/-- The reader (holding the `dead` token) finds the pending map alive. -/
theorem alive_of_dead (γn : ClientNames) (m : GMap w64 Loc) (sd : Bool) :
    ⊢ (pendAlive (GF := GF) γn m sd ∨ (token γn.dead ∗ ⌜m = ∅ ∧ sd = true⌝)) -∗ token γn.dead -∗
      pendAlive γn m sd ∗ token γn.dead := by
  iintro (Hal | ⟨Hd2, -⟩) Hd
  · iframe
  · iexfalso; iapply token_exclusive $$ Hd Hd2

/-- The reader collects the answer `(msg, rep)` of request `i` (`r`, any message) with the
request's collection token: the call's `Φ rep msg`. -/
theorem client_collect (W : RpcWorld GF) (a : GoString) (cid : w64) (γ : RpcConnNames)
    (Lr : List RpcReq) (i : Nat) (r : RpcReq) (msg : GoString) (rep : List w8)
    (Φ : List w8 → GoString → IProp GF) (hr : Lr[i]? = some r) :
    ⊢ isRpcConn W a cid γ -∗ monoListLbOwn γ.reqs Lr -∗
      ghostMapElem γ.ans i .discard (some (msg, rep)) -∗ token r.col -∗
      savedPredOwn r.post .discard (fun p : List w8 × GoString => Φ p.1 p.2) -∗ £ 1 -∗ £ 1
      ={⊤}=∗ Φ rep msg := by
  unfold isRpcConn
  iintro ⟨-, #Hconn⟩ #HLr #Ha Htok #Hpost Hlc1 Hlc2
  iinv Hconn with Hj Hclose
  imod lc_fupd_elim_later $$ Hlc1 Hj with Hj
  unfold connInv
  icases Hj with ⟨%L, %k, %A, Hreqs, Hctr, HA, Hclaim, %Hk, Hdeps, Hans⟩
  ihave %HA := ghost_map_lookup $$ HA Ha
  ihave %HLrL := mono_list_auth_lb_valid _ _ _ _ $$ Hreqs HLr
  have hLi : L[i]? = some r := by
    obtain ⟨t, ht⟩ := HLrL.2
    rw [← ht, List.getElem?_append_left (List.getElem?_eq_some_iff.1 hr).1, hr]
  icases (BigSepM.bigSepM_delete (show get? A i = some (some (msg, rep)) from HA)).1 $$ Hans
    with ⟨Hai, Hans⟩
  unfold answerRes
  icases Hai with ⟨%r', %hr', Hesc⟩
  rw [hLi] at hr'
  cases hr'
  icases Hesc with (Hesc | Htok2)
  rotate_left
  · iexfalso; iapply token_exclusive $$ Htok Htok2
  imod Hclose $$ [Hreqs Hctr HA Hclaim Hdeps Hans Htok] with -
  · inext
    iexists L, k, A
    iframe
    isplitr
    · ipureintro; exact Hk
    iapply (BigSepM.bigSepM_delete (show get? A i = some (some (msg, rep)) from HA)).2
    iframe
    iexists r
    iframe
    ipureintro; exact hLi
  unfold replyEscrow
  icases Hesc with ⟨%Φ', #Hpost', HΦ'⟩
  ihave Hag := saved_pred_agree _ _ _ (fun p : List w8 × GoString => Φ p.1 p.2)
    (fun p : List w8 × GoString => Φ' p.1 p.2) (rep, msg) $$ Hpost Hpost'
  imod lc_fupd_elim_later $$ Hlc2 Hag with #Hag
  imodintro
  iapply internal_eq_rewrite_wand $$ Hag HΦ'

/-- A new client's ghost state, over its connection's names `γ` (whose request list is empty,
the dialer holding its half). -/
theorem client_alloc (γ : RpcConnNames) :
    ⊢ monoListAuthOwn (GF := GF) γ.reqs (1 : Qp).half ([] : List RpcReq) ={⊤}=∗
      ∃ γn : ClientNames, ⌜γn.conn = γ⌝ ∗ inv cliN (cliInv γn) ∗
        monoListAuthOwn γn.cl (1 : Qp).half ([] : List RpcReq) ∗
        ghostVar γn.last (1 : Qp).half ([] : List (w64 × PEntry)) ∗
        pendAlive γn ∅ false ∗ monoListAuthOwn γn.sdl 1 ([] : List Unit) ∗
        monoListAuthOwn γn.cons (1 : Qp).half ([] : List Ans) ∗ token γn.dead := by
  iintro Hreqs
  imod mono_list_own_alloc (GF := GF) ([] : List RpcReq) with ⟨%γcl, Hcl, -⟩
  imod ghost_map_alloc_empty (GF := GF) (K := w64) (V := PEntry) with ⟨%γp, Hp⟩
  imod mono_list_own_alloc (GF := GF) ([] : List Ans) with ⟨%γc, Hc, -⟩
  imod mono_list_own_alloc (GF := GF) ([] : List Unit) with ⟨%γs, Hs, -⟩
  imod ghostVar_alloc (GF := GF) ([] : List (w64 × PEntry)) with ⟨%γl, Hl⟩
  imod token_alloc (GF := GF) with ⟨%γd, Hd⟩
  icases (ml_halves γcl _).1 $$ Hcl with ⟨Hcl1, Hcl2⟩
  icases (ml_halves γc _).1 $$ Hc with ⟨Hc1, Hc2⟩
  icases (ghostMapAuth_halves γp _).1 $$ Hp with ⟨Hp1, Hp2⟩
  icases (ghostVar_split_half γl 1 _).1 $$ Hl with ⟨Hl1, Hl2⟩
  let γn : ClientNames := ⟨γ, γcl, γp, γc, γs, γl, γd⟩
  imod inv_alloc cliN ⊤ (cliInv γn) $$ [Hreqs Hcl1 Hp1 Hc1] with #Hinv
  · inext
    unfold cliInv
    iexists [], ∅, []
    iframe
    isplitr
    · ipureintro; simp
    unfold store; iapply BigSepL.bigSepL_nil.2; itrivial
  imodintro
  iexists γn
  iframe
  isplitr
  · ipureintro; rfl
  isplitr
  · iexact Hinv
  unfold pendAlive
  iexists ∅, []
  iframe
  isplitr
  · ipureintro
    constructor
    · intro s e h; simp at h
    · intro _ s h; exact absurd (GMap.lookup_empty (K := w64) (V := PEntry) s) h
  iapply BigSepM.bigSepM_empty.2
  itrivial

/-- The dialer registers its new connection `cid` (with the end's fresh token): fresh names,
an invariant with no requests, and the dialer's half of the request list. -/
theorem conn_register (W : RpcWorld GF) (a : GoString) (cid : w64) :
    ⊢ inv regN (regInv W) -∗ connFresh cid false ={⊤}=∗
      ∃ γ : RpcConnNames, isRpcConn W a cid γ ∗
        monoListAuthOwn γ.reqs (1 : Qp).half ([] : List RpcReq) := by
  iintro #Hreg Hfr
  imod mono_list_own_alloc (GF := GF) ([] : List RpcReq) with ⟨%γr, Hr, -⟩
  imod ghostVar_alloc (GF := GF) (0 : Nat) with ⟨%γk, Hk⟩
  imod ghost_map_alloc_empty (GF := GF) (K := Nat) (V := Option (GoString × List w8))
    with ⟨%γa, Ha⟩
  icases (ml_halves γr _).1 $$ Hr with ⟨Hr1, Hr2⟩
  icases (ghostVar_split_half γk 1 _).1 $$ Hk with ⟨Hk1, Hk2⟩
  let γ : RpcConnNames := (γr, γk, γa)
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
    unfold isRpcConn regElem
    iframe
    iframe #

end ghost

end net.rpc

end Perennial
