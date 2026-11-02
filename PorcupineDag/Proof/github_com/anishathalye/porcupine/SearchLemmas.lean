/- Lean-first (no Rocq counterpart).

# Lemmas of the DAG search's proofs (2026-11-02)

For `chains.lift`, `chains.unlift` and `checkSingle`: a client's struct depends on the chains'
state only at that client (`ChAgree`, `clientOwn_agree`), and the access to one client of the
chains (`chainsOwn_acc`: the client's element pointer, its `clientOwn`, and the chains back at a
state that agrees elsewhere, with the same frontier).
-/
module

public import PorcupineDag.Proof.github_com.anishathalye.porcupine.Search

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProofMode

namespace github_com.anishathalye.porcupine

open Theory

/-- Two chains' states agree at client `c`. -/
def ChAgree (st st' : ChSt) (c : Nat) : Prop :=
  st'.head c = st.head c ∧ st'.nDeps.getD c 0 = st.nDeps.getD c 0 ∧
  st'.vis.getD c [] = st.vis.getD c [] ∧ st'.fu.getD c [] = st.fu.getD c []

section bi
variable {PROP : Type _} [BI PROP] [BIAffine PROP] {A : Type _}

/-- A big separating conjunction with one element replaced and the predicate changed. -/
theorem bigSepL_set_change {Φ Ψ : Nat → A → PROP} {l : List A} {j : Nat} {x : A} (y : A)
    (hx : l[j]? = some x) :
    ([∗list] k ↦ z ∈ l, if k = j then emp else Φ k z) ⊢
      (□ ∀ k z, ⌜k ≠ j⌝ → Φ k z -∗ Ψ k z) -∗ Ψ j y -∗ [∗list] k ↦ z ∈ l.set j y, Ψ k z := by
  iintro Hl #Himp Hy
  have hy : (l.set j y)[j]? = some y := by
    rw [List.getElem?_set_self]; exact (List.getElem?_eq_some_iff.mp hx).1
  icases (BigSepL.bigSepL_insert_acc hx).trans (sep_mono_right (forall_elim y)) $$ Hl with ⟨-, Hl⟩
  ihave Hl := Hl $$ []
  · simp only [↓reduceIte]; iempintro
  icases BigSepL.bigSepL_lookup_acc_impl hy $$ Hl with ⟨-, Hl⟩
  iapply Hl $$ [] Hy
  imodintro
  iintro %k %z %_ %Hk Hz
  simp only [Hk, ↓reduceIte]
  iapply Himp $$ %k %z %Hk Hz

end bi

/-- Setting a clear bit and clearing it again gives the words back. -/
theorem bsClear_bsSet (ws : List w64) (pos : w64) (h : uint.nat pos / 64 < ws.length)
    (hb : bsBit ws (uint.nat pos) = false) : bsClear (bsSet ws pos) pos = ws := by
  unfold bsClear bsSet
  have hset : ∀ a, (ws.set (uint.nat pos / 64) a).getD (uint.nat pos / 64) 0 = a := by
    intro a; simp [List.getD_eq_getElem?_getD, List.getElem?_set_self h]
  rw [hset, List.set_set]
  have hw : (ws.getD (uint.nat pos / 64) 0 ||| W64 1 <<< (pos % W64 64)) &&& ~~~(W64 1 <<< (pos % W64 64)) =
      ws.getD (uint.nat pos / 64) 0 := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    rw [getLsbD_andnot_bit _ _ _ hj, getLsbD_or_bit _ _ _ hj]
    by_cases hjp : j = uint.nat pos % 64
    · subst hjp
      unfold bsBit at hb
      simp only [List.getD_eq_getElem?_getD] at hb
      simp only [decide_true, Bool.or_true, Bool.not_true, Bool.and_false]
      exact hb.symm
    · simp [hjp]
  rw [hw, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some,
    List.set_getElem_self]

section heap
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.anishathalye.porcupine.Assumptions]

theorem clientOwn_agree (h : List (Op OpV)) (cs : List (List Nat)) {st st' : ChSt} {c : Nat}
    (cv : client) (ha : ChAgree st st' c) :
    clientOwn h cs st c cv ⊢ clientOwn (GF := GF) h cs st' c cv := by
  obtain ⟨h1, h2, h3, h4⟩ := ha
  unfold clientOwn ChSt.fuAt
  rw [h1, h2, h3, h4]

/-- One client of a chains value: its element pointer and struct; the value comes back at any
state that agrees at the other clients, with the same frontier. -/
theorem chainsRepr_acc (chV : chains) (h : List (Op OpV)) (cs : List (List Nat)) (st : ChSt)
    (j : Nat) (hj : j < cs.length) :
    chainsRepr chV h cs st ⊢ ⌜sint.Z chV.clients'.len = cs.length⌝ ∗ ∃ cv : client,
      sliceIndexRef client (j : Int) chV.clients' ↦ cv ∗ clientOwn (GF := GF) h cs st j cv ∗
      ∀ (st' : ChSt) (cv' : client), ⌜(∀ c, c ≠ j → ChAgree st st' c) ∧ st'.frontier = st.frontier⌝ -∗
        sliceIndexRef client (j : Int) chV.clients' ↦ cv' -∗ clientOwn h cs st' j cv' -∗
        chainsRepr chV h cs st' := by
  iintro Hr
  unfold chainsRepr
  icases Hr with ⟨%cvs, Hcl, %Hcvs, Hfr, Hcap, Hcls⟩
  ihave %Hlen := ownSlice_len $$ Hcl
  obtain ⟨cv, hcv⟩ : ∃ cv, cvs[j]? = some cv := ⟨_, List.getElem?_eq_getElem (by omega)⟩
  icases ownSlice_elem_acc (j : Int) cv _ _ cvs (by omega) (by simpa using hcv) $$ Hcl with ⟨He, Hcl⟩
  icases BigSepL.bigSepL_lookup_acc_impl hcv $$ Hcls with ⟨Hc, Hcls⟩
  isplitr
  · ipureintro; obtain ⟨h1, h2⟩ := Hlen; rw [← Hcvs.1]; word
  iexists cv
  iframe He Hc
  iintro %st' %cv' %Hag He Hc
  obtain ⟨Hag, Hfr'⟩ := Hag
  iexists cvs.set j cv'
  ihave Hcl := Hcl $$ %cv' He
  simp only [Int.toNat_natCast]
  iframe Hcl
  rw [Hfr']
  iframe Hfr Hcap
  isplitr
  · ipureintro; simpa using Hcvs
  iapply bigSepL_set_change cv' hcv $$ [Hcls] [] Hc
  · iapply Hcls $$ [] []
    · imodintro
      iintro %k %y %_ %Hk Hy
      simp only [Hk, ↓reduceIte]
      iexact Hy
    · simp only [↓reduceIte]; iempintro
  imodintro
  iintro %k %y %Hk Hy
  iapply clientOwn_agree h cs y (Hag k Hk) $$ Hy

/-- One client of the chains (`chainsRepr_acc`), at a known clients slice. -/
theorem chainsOwnCl_acc (ch : Loc) (cl : GoSlice) (h : List (Op OpV)) (cs : List (List Nat))
    (st : ChSt) (j : Nat) (hj : j < cs.length) :
    chainsOwnCl ch cl h cs st ⊢ ∃ (chV : chains) (cv : client), ch ↦ chV ∗
      ⌜chV.clients' = cl ∧ sint.Z cl.len = cs.length⌝ ∗
      sliceIndexRef client (j : Int) cl ↦ cv ∗ clientOwn (GF := GF) h cs st j cv ∗
      ∀ (st' : ChSt) (cv' : client), ⌜(∀ c, c ≠ j → ChAgree st st' c) ∧ st'.frontier = st.frontier⌝ -∗
        ch ↦ chV -∗ sliceIndexRef client (j : Int) cl ↦ cv' -∗ clientOwn h cs st' j cv' -∗
        chainsOwnCl ch cl h cs st' := by
  iintro Hch
  unfold chainsOwnCl
  icases Hch with ⟨%chV, Hch, %Hcl, Hr⟩
  subst Hcl
  icases chainsRepr_acc chV h cs st j hj $$ Hr with ⟨%Hlen, %cv, He, Hc, Hback⟩
  iexists chV, cv
  iframe Hch He Hc
  isplitr
  · ipureintro; exact ⟨rfl, Hlen⟩
  iintro %st' %cv' %Hag Hch He Hc
  iexists chV
  iframe Hch
  isplitr
  · ipureintro; rfl
  iapply Hback $$ %st' %cv' %Hag He Hc

/-- One client of the chains. -/
theorem chainsOwn_acc (ch : Loc) (h : List (Op OpV)) (cs : List (List Nat)) (st : ChSt) (j : Nat)
    (hj : j < cs.length) :
    chainsOwn ch h cs st ⊢ ∃ (chV : chains) (cv : client),
      ch ↦ chV ∗ ⌜sint.Z chV.clients'.len = cs.length⌝ ∗
      sliceIndexRef client (j : Int) chV.clients' ↦ cv ∗ clientOwn (GF := GF) h cs st j cv ∗
      ∀ (st' : ChSt) (cv' : client), ⌜(∀ c, c ≠ j → ChAgree st st' c) ∧ st'.frontier = st.frontier⌝ -∗
        ch ↦ chV -∗ sliceIndexRef client (j : Int) chV.clients' ↦ cv' -∗ clientOwn h cs st' j cv' -∗
        chainsOwn ch h cs st' := by
  iintro Hch
  icases chainsOwn_cl ch h cs st $$ Hch with ⟨%cl, Hch⟩
  icases chainsOwnCl_acc ch cl h cs st j hj $$ Hch with ⟨%chV, %cv, Hch, %Hl, He, Hc, Hback⟩
  obtain ⟨rfl, Hl⟩ := Hl
  iexists chV, cv
  iframe Hch He Hc
  isplitr
  · ipureintro; exact Hl
  iintro %st' %cv' %Hag Hch He Hc
  iapply chainsOwnCl_weaken
  iapply Hback $$ %st' %cv' %Hag Hch He Hc

theorem clientOwn_facts (h : List (Op OpV)) (cs : List (List Nat)) (st : ChSt) (c : Nat)
    (cv : client) :
    clientOwn h cs st c cv ⊢ ⌜sint.Z cv.id' = c ∧ sint.Z cv.head' = st.head c ∧
      cv.nDeps' = st.nDeps.getD c 0⌝ ∗ clientOwn (GF := GF) h cs st c cv := by
  unfold clientOwn
  iintro ⟨%Hc, Hr⟩
  iframe Hr
  ipureintro; exact ⟨Hc, Hc⟩

/-- The frontier slice of a chains value. -/
theorem chainsRepr_frontier (chV : chains) (h : List (Op OpV)) (cs : List (List Nat)) (st : ChSt) :
    chainsRepr chV h cs st ⊢
      chV.frontier' ↦* (st.frontier.map (fun (c : Nat) => (W64 (c : Int) : w64))) ∗
      (chV.frontier' ↦* (st.frontier.map (fun (c : Nat) => (W64 (c : Int) : w64))) -∗
        chainsRepr (GF := GF) chV h cs st) := by
  unfold chainsRepr
  iintro ⟨%cvs, Hcl, %Hcvs, Hfr, Hcap, Hcls⟩
  iframe Hfr
  iintro Hfr
  iexists cvs
  iframe
  ipureintro; exact Hcvs

/-- The clients slice as its elements' points-tos (and the way back, for a list of the same
length). -/
theorem clients_elems (sl : GoSlice) (cvs : List client) :
    sl ↦* cvs ⊢ ([∗list] j ↦ cv ∈ cvs, sliceIndexRef client (j : Int) sl ↦ cv) ∗
      (∀ cvs' : List client, ⌜cvs'.length = cvs.length⌝ -∗
        ([∗list] j ↦ cv ∈ cvs', sliceIndexRef client (j : Int) sl ↦ cv) -∗ sl ↦* cvs' : IProp GF) := by
  rw [ownSlice_unseal]; unfold ownSliceDef
  iintro (%H | ⟨Harr, %Hcap⟩)
  · obtain ⟨rfl, rfl⟩ := H
    isplitl []
    · iapply BigSepL.bigSepL_nil.2; iempintro
    iintro %cvs' %Hl _
    ileft; ipureintro
    exact ⟨rfl, List.eq_nil_of_length_eq_zero (by simpa using Hl)⟩
  · icases typedPointsto_not_null_dup _ _ _ $$ Harr with ⟨Harr, %Hnn⟩
    icases typedPointsto_split _ _ _ $$ Harr with Harr
    simp only [TypedPointsto.typedPointstoDef]
    icases Harr with ⟨%Hlen, Harr⟩
    unfold arrayElems
    simp only [sliceIndexRef]
    iframe Harr
    iintro %cvs' %Hl Hel
    iright
    isplitl
    · iapply typedPointsto_combine _ _ _ Hnn
      simp only [TypedPointsto.typedPointstoDef]
      isplitr
      · ipureintro; rw [Hl]; exact Hlen
      · unfold arrayElems; iexact Hel
    · ipureintro; exact Hcap

/-- The clients of a chains value but client `i`: their elements' points-tos and structs. -/
def othersOwn (cl : GoSlice) (h : List (Op OpV)) (cs : List (List Nat)) (st : ChSt) (i : Nat)
    (cvs : List client) : IProp GF :=
  iprop([∗list] j ↦ cv ∈ cvs,
    if j = i then emp else (sliceIndexRef client (j : Int) cl ↦ cv ∗ clientOwn h cs st j cv))

/-- A chains value with client `i` taken out (`chainsRepr_open`). -/
def chainsRest (chV : chains) (h : List (Op OpV)) (cs : List (List Nat)) (st : ChSt) (i : Nat)
    (cvs : List client) : IProp GF :=
  iprop(⌜cvs.length = cs.length ∧ sint.Z chV.numOps' = h.length⌝ ∗
    chV.frontier' ↦* (st.frontier.map (fun (c : Nat) => (W64 (c : Int) : w64))) ∗
    ownSliceCap w64 chV.frontier' (DFrac.own 1) ∗ othersOwn chV.clients' h cs st i cvs ∗
    (∀ cvs' : List client, ⌜cvs'.length = cvs.length⌝ -∗
      ([∗list] j ↦ cv ∈ cvs', sliceIndexRef client (j : Int) chV.clients' ↦ cv) -∗
      chV.clients' ↦* cvs'))

/-- Client `i` taken out of a chains value, the others kept apart (`chainsRest`): the other
clients can then be read while client `i` stays out. -/
theorem chainsRepr_open (chV : chains) (h : List (Op OpV)) (cs : List (List Nat)) (st : ChSt)
    (i : Nat) (hi : i < cs.length) :
    chainsRepr chV h cs st ⊢ ∃ (cvs : List client) (cv : client),
      ⌜cvs[i]? = some cv ∧ cvs.length = cs.length ∧ sint.Z chV.clients'.len = cs.length⌝ ∗
      sliceIndexRef client (i : Int) chV.clients' ↦ cv ∗ clientOwn (GF := GF) h cs st i cv ∗
      chainsRest chV h cs st i cvs := by
  unfold chainsRepr chainsRest othersOwn
  iintro ⟨%cvs, Hcl, %Hcvs, Hfr, Hcap, Hcls⟩
  ihave %Hlen := ownSlice_len $$ Hcl
  icases clients_elems _ cvs $$ Hcl with ⟨Hel, Hshell⟩
  obtain ⟨cv, hcv⟩ : ∃ cv, cvs[i]? = some cv := ⟨_, List.getElem?_eq_getElem (by omega)⟩
  ihave Hall := BigSepL.bigSepL_sep_eqv.2 $$ [Hel Hcls]
  · iframe
  icases (BigSepL.bigSepL_delete_cond hcv).1 $$ Hall with ⟨⟨He, Hc⟩, Hall⟩
  iexists cvs, cv
  iframe He Hc Hfr Hcap Hshell Hall
  isplitl []
  · ipureintro; obtain ⟨h1, h2⟩ := Hlen; refine ⟨hcv, Hcvs.1, ?_⟩; rw [← Hcvs.1]; word
  ipureintro; exact Hcvs

/-- Another client read while client `i` is out. -/
theorem chainsRest_read (chV : chains) (h : List (Op OpV)) (cs : List (List Nat)) (st : ChSt)
    (i k : Nat) (cvs : List client) (cvk : client) (hk : cvs[k]? = some cvk) (hki : k ≠ i) :
    chainsRest chV h cs st i cvs ⊢ sliceIndexRef client (k : Int) chV.clients' ↦ cvk ∗
      clientOwn (GF := GF) h cs st k cvk ∗
      (sliceIndexRef client (k : Int) chV.clients' ↦ cvk -∗ clientOwn h cs st k cvk -∗
        chainsRest chV h cs st i cvs) := by
  unfold chainsRest othersOwn
  iintro ⟨%Hp, Hfr, Hcap, Hoth, Hshell⟩
  icases (BigSepL.bigSepL_lookup_acc hk).1 $$ Hoth with ⟨Hk, Hoth⟩
  simp only [hki, ↓reduceIte]
  icases Hk with ⟨He, Hc⟩
  iframe He Hc
  iintro He Hc
  iframe Hfr Hcap Hshell
  isplitr
  · ipureintro; exact Hp
  ihave Hoth := Hoth $$ %cvk [He Hc]
  · (try simp only [hki, ↓reduceIte]); iframe
  have hset : cvs.set k cvk = cvs := by
    obtain ⟨hl, he⟩ := List.getElem?_eq_some_iff.mp hk
    rw [← he]; exact List.set_getElem_self hl
  rw [hset]
  iexact Hoth

/-- Client `i` put back, at a state that agrees with `st` at the other clients. -/
theorem chainsRest_close (chV : chains) (h : List (Op OpV)) (cs : List (List Nat)) (st st' : ChSt)
    (i : Nat) (cvs : List client) (cv cv' : client) (hcv : cvs[i]? = some cv)
    (hag : ∀ c, c ≠ i → ChAgree st st' c) (hfr : st'.frontier = st.frontier) :
    sliceIndexRef client (i : Int) chV.clients' ↦ cv' ∗ clientOwn h cs st' i cv' ∗
      chainsRest chV h cs st i cvs ⊢ chainsRepr (GF := GF) chV h cs st' := by
  unfold chainsRest othersOwn chainsRepr
  iintro ⟨He, Hc, %Hp, Hfr, Hcap, Hoth, Hshell⟩
  ihave Hall := bigSepL_set_change (Ψ := fun j cv =>
      iprop(sliceIndexRef client (j : Int) chV.clients' ↦ cv ∗ clientOwn (GF := GF) h cs st' j cv))
    cv' hcv $$ Hoth [] [He Hc]
  · imodintro
    iintro %k %z %Hk ⟨He, Hc⟩
    iframe He
    iapply clientOwn_agree h cs z (hag k Hk) $$ Hc
  · iframe
  icases BigSepL.bigSepL_sep_eqv.1 $$ Hall with ⟨Hel, Hcls⟩
  iexists cvs.set i cv'
  ihave Hcl := Hshell $$ %(cvs.set i cv') [] Hel
  · ipureintro; simp
  iframe Hcl Hcls
  rw [hfr]
  iframe Hfr Hcap
  ipureintro; simpa using Hp

/-- A client's struct, with its head or `nDeps` changed. -/
theorem clientOwn_upd (h : List (Op OpV)) (cs : List (List Nat)) {st st' : ChSt} {c : Nat}
    (cv cv' : client) (hcl : cv'.cltOps' = cv.cltOps') (hid : cv'.id' = cv.id')
    (hhd : sint.Z cv'.head' = st'.head c) (hnd : cv'.nDeps' = st'.nDeps.getD c 0)
    (hv : st'.vis.getD c [] = st.vis.getD c []) (hf : st'.fu.getD c [] = st.fu.getD c []) :
    clientOwn h cs st c cv ⊢ clientOwn (GF := GF) h cs st' c cv' := by
  unfold clientOwn ChSt.fuAt
  iintro ⟨%Hc, %cos, Hcos, %Hok, Hfu⟩
  isplitr
  · ipureintro; exact ⟨by rw [hid]; exact Hc.1, hhd, hnd⟩
  iexists cos
  rw [hcl, hv, hf]
  iframe
  ipureintro; exact Hok

theorem stackRep_length (S : ModelSpec GF σ) (np : NaInvPoolName) (cs : List (List Nat))
    (ses : List stackEntry) (fs : List (Frame σ)) [NaInvG GF] :
    stackRep S np cs ses fs ⊢ ⌜ses.length = fs.length⌝ := by
  unfold stackRep
  iintro H
  ihave %h := BigSepL2.bigSepL2_length $$ H
  ipureintro; simpa using h

/-- The newest frame is the stack's last entry. -/
theorem stackRep_pop (S : ModelSpec GF σ) (np : NaInvPoolName) (cs : List (List Nat))
    (ses : List stackEntry) (f : Frame σ) (fs : List (Frame σ)) [NaInvG GF] :
    stackRep S np cs ses (f :: fs) ⊢ ∃ (ses' : List stackEntry) (se : stackEntry),
      ⌜ses = ses' ++ [se] ∧ sint.Z se.opId' = f.id ∧ sint.Z se.clientId' = clientOf cs f.id ∧
        sint.Z se.frontierIdx' = f.pos⌝ ∗ shared S np fs.length se.state' f.pre ∗
      stackRep S np cs ses' fs := by
  unfold stackRep
  simp only [List.reverse_cons]
  iintro H
  icases BigSepL2.bigSepL2_app_inv_right $$ H with ⟨%l1, %l2, %hses, H1, H2⟩
  ihave %hl2 := BigSepL2.bigSepL2_length $$ H2
  simp only [List.length_singleton] at hl2
  obtain ⟨se, rfl⟩ : ∃ se, l2 = [se] := by
    cases l2 with
    | nil => simp at hl2
    | cons a l => cases l with
      | nil => exact ⟨a, rfl⟩
      | cons b l => simp at hl2
  icases BigSepL2.bigSepL2_singleton.1 $$ H2 with ⟨%he, #Hs⟩
  iexists l1, se
  rw [show fs.length = 0 + fs.reverse.length by simp]
  iframe H1 Hs
  ipureintro; exact ⟨hses, he⟩

/-- A frame pushed: a new last entry. -/
theorem stackRep_push (S : ModelSpec GF σ) (np : NaInvPoolName) (cs : List (List Nat))
    (ses : List stackEntry) (se : stackEntry) (f : Frame σ) (fs : List (Frame σ)) [NaInvG GF]
    (hse : sint.Z se.opId' = f.id ∧ sint.Z se.clientId' = clientOf cs f.id ∧
      sint.Z se.frontierIdx' = f.pos) :
    stackRep S np cs ses fs ∗ shared S np fs.length se.state' f.pre ⊢
      stackRep S np cs (ses ++ [se]) (f :: fs) := by
  iintro ⟨H, #Hs⟩
  ihave %hl := stackRep_length S np cs ses fs $$ H
  unfold stackRep
  simp only [List.reverse_cons]
  iapply BigSepL2.bigSepL2_snoc.2
  iframe H
  rw [hl]
  iframe Hs
  ipureintro; exact hse

end heap

end github_com.anishathalye.porcupine

end Perennial
