/-
(Ported from dsverify-lab `examples/rabia/proof/Proof/rabia/roles/server/layers/network/Base.lean`, run `rabia-r1wake-1`.)

Helpers of the network layer's proofs: the logs' updates and pure facts about the lists.
-/
module

public import Dsverify.Proof.rabia.roles.server.layers.network.Spec

@[expose] public section

noncomputable section

namespace Perennial.rabia.roles.server.layers.network

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode model Net rabia.internal.message
  rabia.internal.config rabia rabia.internal.tcp

set_option linter.unusedSectionVars false

section ghost
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics] [π : NetProtoGS]

instance serLb_persistent (γs : GName) (l : List Bool) : Persistent (serLb (GF := GF) γs l) := by
  unfold serLb; infer_instance
instance hLb_persistent' (γl : SrvNames) (l : List (Nat × Nat)) : Persistent (hLb (GF := GF) γl l) := by
  unfold hLb; infer_instance
instance pushLb_persistent' (γl : SrvNames) (X : Nat) (l : List MsgV) :
    Persistent (pushLb (GF := GF) γl X l) := by
  unfold pushLb; infer_instance
instance exLb_persistent' (γl : SrvNames) (l : List MsgV) : Persistent (exLb (GF := GF) γl l) := by
  unfold exLb; infer_instance
instance bcastLb_persistent' (γ : Names) (X : Nat) (l : List MsgV) :
    Persistent (bcastLb (GF := GF) γ X l) := by
  unfold bcastLb; infer_instance

theorem serAuth_snoc (E : CoPset) (γs : GName) (bl : List Bool) (b : Bool) :
    serAuth (GF := GF) γs bl ⊢ |={E}=> serAuth γs (bl ++ [b]) ∗ serLb γs (bl ++ [b]) := by
  unfold serAuth serLb
  iintro H
  imod monoListAuthOwn_update_app [b] $$ H with ⟨H1, H2⟩
  imodintro
  iframe

theorem monoListLb_nil_fupd {A : Type} [Pos.Countable A] (E : CoPset) (γ' : GName) :
    ⊢ |={E}=> monoListLbOwn (GF := GF) γ' ([] : List A) := by
  imod monoListLbOwn_nil (GF := GF) (A := A) γ' with H
  imodintro
  iexact H

theorem serLog_alloc (E : CoPset) :
    ⊢ |={E}=> ∃ γs : GName, serAuth (GF := GF) γs [] ∗ serLb γs [] := by
  imod mono_list_own_alloc (GF := GF) (A := Bool) [] with ⟨%γs, H1, H2⟩
  imodintro
  iexists γs
  unfold serAuth serLb
  iframe

theorem hAuth_snoc (E : CoPset) (γl : SrvNames) (hl : List (Nat × Nat)) (x : Nat × Nat) :
    hAuth (GF := GF) γl hl ⊢ |={E}=> hAuth γl (hl ++ [x]) ∗ hLb γl (hl ++ [x]) := by
  unfold hAuth hLb
  iintro H
  imod monoListAuthOwn_update_app [x] $$ H with ⟨H1, H2⟩
  imodintro
  iframe

/-- The permits held for `B_k`'s client requests are distinct from a new one. -/
theorem crToks_fresh (γl : SrvNames) (L : List MsgV) (q : Nat) :
    ([∗list] m ∈ L, ∃ o : ObjV, ⌜m.obj = some o⌝ ∗ crTok γl o.proSeq.toNat) ∗ crTok (GF := GF) γl q ⊢
      ([∗list] m ∈ L, ∃ o : ObjV, ⌜m.obj = some o⌝ ∗ crTok γl o.proSeq.toNat) ∗ crTok γl q ∗
      ⌜∀ m ∈ L, ∀ o : ObjV, m.obj = some o → o.proSeq.toNat ≠ q⌝ := by
  induction L with
  | nil =>
    iintro ⟨H, T⟩
    iframe
    ipureintro; simp
  | cons a L ih =>
    iintro ⟨H, T⟩
    icases BigSepL.bigSepL_cons.1 $$ H with ⟨⟨%o, %ho, Ha⟩, H⟩
    icases ih $$ [$H $T] with ⟨H, T, %h⟩
    by_cases heq : o.proSeq.toNat = q
    · rw [heq]
      unfold crTok
      icombine Ha T gives %Hv
      exfalso
      obtain ⟨Hv, -⟩ := Hv
      exact absurd (DFrac.valid_own_op Hv) (by have : (1 : Qp).val = 1 := rfl; grind)
    · isplitl [Ha H]
      · iapply BigSepL.bigSepL_cons.2
        iframe H
        iexists o
        iframe Ha
        ipureintro; exact ho
      iframe T
      ipureintro
      intro m hm o' ho'
      rcases List.mem_cons.1 hm with rfl | hm
      · rw [ho] at ho'; cases ho'; exact heq
      · exact h m hm o' ho'

theorem monoList_join {A : Type} [Pos.Countable A] (γ' : GName) (l : List A) :
    monoListAuthOwn (GF := GF) γ' (1 : Qp).half l ∗ monoListAuthOwn γ' (1 : Qp).half l ⊣⊢
      monoListAuthOwn γ' 1 l := by
  have h := (monoListAuthOwn_fractional (GF := GF) γ' l).fractional (1 : Qp).half (1 : Qp).half
  rw [Qp.half_add_half] at h
  exact h.symm

/-- A recorded configuration has at most `maxS` servers (unfolds `Ghost.lean`'s `cfgIs`: a
missing law). -/
theorem cfgIs_n_le (γ : Names) (cf : RCfg) :
    cfgIs (GF := GF) γ.rab cf ⊢ ⌜cf.n ≤ maxS⌝ := by
  unfold cfgIs
  iintro ⟨-, %h⟩
  ipureintro
  obtain ⟨h, -⟩ := h
  unfold maxS; omega

/-- The serializer appends `m` to `B_k` (the invariant's half joins its own). -/
theorem bcast_append (γ : Names) (cf : RCfg) (k : Nat) (B : List MsgV) (m : MsgV) (hk : k < cf.n)
    (hro : RoundsOrdered (B ++ [m])) :
    shared (GF := GF) γ ∗ cfgIs γ.rab cf ∗ £ 1 ∗ monoListAuthOwn (γ.net.bcast k) (1 : Qp).half B ∗
      bmsgOk γ cf k m ⊢
      |={⊤}=> monoListAuthOwn (γ.net.bcast k) (1 : Qp).half (B ++ [m]) ∗ bcastLb γ k (B ++ [m]) := by
  iintro ⟨#Hsh, #Hcfg, Hlc, Hmine, Hok⟩
  ihave %hn := cfgIs_n_le γ cf $$ Hcfg
  unfold shared
  icases Hsh with ⟨-, #Hbc, -, -⟩
  have hr : (List.range maxS)[k]? = some k := by simp [show k < maxS by omega]
  ihave #Hinv := BigSepL.bigSepL_lookup hr $$ Hbc
  iinv Hinv with Hi Hclose
  imod lc_fupd_elim_later (E := ⊤ \ ↑(bcastN k)) $$ Hlc Hi with Hi
  unfold bcastInv
  icases Hi with ⟨%l, Ha, Hbig, %Hro⟩
  ihave %Hag := monoListAuthOwn_agree _ _ _ _ _ $$ Ha Hmine
  obtain ⟨-, rfl⟩ := Hag
  ihave Hfull := (monoList_join _ _).1 $$ [$Ha $Hmine]
  imod monoListAuthOwn_update_app [m] $$ Hfull with ⟨Hfull, #Hlb⟩
  icases (monoList_join _ _).2 $$ Hfull with ⟨Ha, Hmine⟩
  ihave Hbig' : (([∗list] m ∈ l, bmsgOk γ cf k m) : IProp GF) $$ [Hbig]
  · icases Hbig with (%Hl | ⟨%cf', #Hcf', Hbig⟩)
    · subst Hl
      iapply BigSepL.bigSepL_nil.2; iempintro
    · ihave %Heq := cfgIs_agree γ.rab cf' cf $$ [$Hcf' $Hcfg]
      subst Heq
      iexact Hbig
  imod Hclose $$ [Ha Hbig' Hok] with -
  · inext
    iexists l ++ [m]
    iframe Ha
    isplitl
    · iright
      iexists cf
      iframe Hcfg
      iapply BigSepL.bigSepL_snoc.2
      iframe
    · ipureintro; exact hro
  imodintro
  iframe Hmine
  unfold bcastLb
  iexact Hlb

/-- A reply's destination (unfolds `Proto.lean`'s `replyOk`: a missing law). -/
theorem replyOk_phase (γ : Names) (cf : RCfg) (j : Nat) (m : MsgV) :
    replyOk (GF := GF) γ cf j m ⊢ replyOk γ cf j m ∗ ⌜m.phase.toNat = j⌝ := by
  iintro H
  unfold replyOk
  icases H with ⟨%o, %W, %b, %h, H1, H2, H3⟩
  isplitl
  · iexists o, W, b
    iframe
    ipureintro; exact h
  · ipureintro; exact h.2.1

end ghost

end Perennial.rabia.roles.server.layers.network

namespace Perennial.rabia.roles.server.layers.network
open model rabia

/-! ## Pure facts -/

theorem snoc_of_prefix {α : Type} (px lp : List α) (m : α) (h : px <+: lp ∨ lp <+: px)
    (hl : lp.length = px.length + 1) (hm : lp[px.length]? = some m) : lp = px ++ [m] := by
  rcases h with ⟨t, rfl⟩ | h
  · simp only [List.length_append] at hl
    have ht : t.length = 1 := by omega
    match t, ht with
    | [a], _ =>
      simp only [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self,
        List.getElem?_cons_zero, Option.some.injEq] at hm
      rw [hm]
  · have := h.length_le; omega

theorem bcastPart_snoc_reply (px : List MsgV) (m : MsgV) (h : m.ty = tyProposalReply) :
    bcastPart (px ++ [m]) = bcastPart px := by
  simp [bcastPart, List.filter_append, h]

theorem bcastPart_snoc_bc (px : List MsgV) (m : MsgV) (h : m.ty ≠ tyProposalReply) :
    bcastPart (px ++ [m]) = bcastPart px ++ [m] := by
  simp [bcastPart, List.filter_append, h]

/-- The handler's log invariant after a reply from `X` (its broadcasts unchanged). -/
theorem hlInv_same (P : List (List MsgV)) (hl : List (Nat × Nat)) (X : Nat) (px lp : List MsgV)
    (hpx : P[X]? = some px) (hb : bcastPart lp = bcastPart px)
    (h : ∀ (Y : Nat) (py : List MsgV), P[Y]? = some py → ∀ j < (bcastPart py).length, (Y, j) ∈ hl) :
    ∀ (Y : Nat) (py : List MsgV), (P.set X lp)[Y]? = some py →
      ∀ j < (bcastPart py).length, (Y, j) ∈ hl := by
  intro Y py hy j hj
  rw [List.getElem?_set] at hy
  by_cases hYX : X = Y
  · subst hYX
    have hlt : X < P.length := (List.getElem?_eq_some_iff.1 hpx).1
    simp only [hlt, ↓reduceIte, Option.some.injEq] at hy
    subst hy
    rw [hb] at hj
    exact h X px hpx j hj
  · simp only [hYX, ↓reduceIte] at hy
    exact h Y py hy j hj

/-- The handler's log invariant after forwarding `X`'s next broadcast. -/
theorem hlInv_snoc (P : List (List MsgV)) (hl : List (Nat × Nat)) (X : Nat) (px : List MsgV)
    (m : MsgV) (hpx : P[X]? = some px)
    (h : ∀ (Y : Nat) (py : List MsgV), P[Y]? = some py → ∀ j < (bcastPart py).length, (Y, j) ∈ hl) :
    ∀ (Y : Nat) (py : List MsgV), (P.set X (px ++ [m]))[Y]? = some py →
      ∀ j < (bcastPart py).length, (Y, j) ∈ hl ++ [(X, (bcastPart px).length)] := by
  intro Y py hy j hj
  rw [List.getElem?_set] at hy
  by_cases hYX : X = Y
  · subst hYX
    have hlt : X < P.length := (List.getElem?_eq_some_iff.1 hpx).1
    simp only [hlt, ↓reduceIte, Option.some.injEq] at hy
    subst hy
    by_cases hm : m.ty = tyProposalReply
    · rw [bcastPart_snoc_reply _ _ hm] at hj
      exact List.mem_append_left _ (h X px hpx j hj)
    · rw [bcastPart_snoc_bc _ _ hm, List.length_append, List.length_singleton] at hj
      by_cases hjl : j < (bcastPart px).length
      · exact List.mem_append_left _ (h X px hpx j hjl)
      · have : j = (bcastPart px).length := by omega
        subst this
        exact List.mem_append_right _ (List.mem_singleton_self _)
  · simp only [hYX, ↓reduceIte] at hy
    exact List.mem_append_left _ (h Y py hy j hj)

theorem msgRound_ty {m : MsgV} {sr : Nat × Nat} (h : msgRound m = some sr) :
    m.ty ≠ tyClientRequest := by
  intro hc
  simp [msgRound, roundOf, hc, tyClientRequest, tyProposal, tyState, tyVote] at h

theorem getElem?_snoc_cases {α : Type} {B : List α} {m x : α} {i : Nat}
    (h : (B ++ [m])[i]? = some x) : (i < B.length ∧ B[i]? = some x) ∨ (i = B.length ∧ x = m) := by
  by_cases hi : i < B.length
  · left; rw [List.getElem?_append_left hi] at h; exact ⟨hi, h⟩
  · right
    rw [List.getElem?_append_right (by omega)] at h
    rcases hk : i - B.length with _ | k
    · rw [hk] at h; simp at h; exact ⟨by omega, h.symm⟩
    · rw [hk] at h; simp at h

theorem roundsOrdered_prefix {l l' : List MsgV} (h : RoundsOrdered l) (hp : l' <+: l) :
    RoundsOrdered l' := by
  obtain ⟨h1, h2, h3⟩ := h
  have hg : ∀ {i : Nat} {m : MsgV}, l'[i]? = some m → l[i]? = some m := fun hi =>
    prefix_getElem? hp hi
  refine ⟨?_, ?_, ?_⟩
  · intro i m s r hi hr
    obtain ⟨j, hj, m', hm', hr'⟩ := h1 i m s r (hg hi) hr
    have hil : i < l'.length := (List.getElem?_eq_some_iff.1 hi).1
    refine ⟨j, hj, m', ?_, hr'⟩
    have hjl : j < l'.length := by omega
    have := prefix_getElem? hp (List.getElem?_eq_getElem hjl)
    rw [hm'] at this
    rw [List.getElem?_eq_getElem hjl, ← Option.some.inj this]
  · intro i j m m' sr hi hj hr hr'
    exact h2 i j m m' sr (hg hi) (hg hj) hr hr'
  · intro i j m m' o o' hi hj a b c d e
    exact h3 i j m m' o o' (hg hi) (hg hj) a b c d e

theorem exLogOk_prefix {l l' : List MsgV} (h : ExLogOk l) (hp : l' <+: l) : ExLogOk l' :=
  ⟨roundsOrdered_prefix h.1 hp, fun m hm => h.2 m (hp.subset hm)⟩

theorem mem_getElem? {α : Type} {l : List α} {x : α} (h : x ∈ l) : ∃ i : Nat, l[i]? = some x :=
  List.mem_iff_getElem?.1 h

/-- Appending the executor's next message to `B_k`. -/
theorem ro_append_exec (B Ex : List MsgV) (m : MsgV) (hB : RoundsOrdered B)
    (hEx : B.filter (fun m => decide (m.ty ≠ tyClientRequest)) = Ex)
    (hE : RoundsOrdered (Ex ++ [m])) (hm : m.ty ≠ tyClientRequest) :
    RoundsOrdered (B ++ [m]) := by
  obtain ⟨b1, b2, b3⟩ := hB
  obtain ⟨e1, e2, -⟩ := hE
  -- a message of `B` with a round is in `Ex`
  have inEx : ∀ {j : Nat} {m' : MsgV} {sr : Nat × Nat}, B[j]? = some m' → msgRound m' = some sr →
      ∃ j', j' < Ex.length ∧ Ex[j']? = some m' := by
    intro j m' sr hj hr
    have hmem : m' ∈ Ex := by
      rw [← hEx, List.mem_filter]
      exact ⟨List.mem_of_getElem? hj, by simpa using msgRound_ty hr⟩
    obtain ⟨j', hj'⟩ := mem_getElem? hmem
    exact ⟨j', (List.getElem?_eq_some_iff.1 hj').1, hj'⟩
  have exIdx : ∀ {j' : Nat} {m' : MsgV}, j' < Ex.length → Ex[j']? = some m' →
      (Ex ++ [m])[j']? = some m' := fun hl h => by rw [List.getElem?_append_left hl]; exact h
  have mEx : (Ex ++ [m])[Ex.length]? = some m := by simp
  refine ⟨?_, ?_, ?_⟩
  · intro i m0 s r hi hr
    rcases getElem?_snoc_cases hi with ⟨hil, hi'⟩ | ⟨rfl, rfl⟩
    · obtain ⟨j, hj, m', hm', hr'⟩ := b1 i m0 s r hi' hr
      exact ⟨j, hj, m', by rw [List.getElem?_append_left (by omega)]; exact hm', hr'⟩
    · obtain ⟨j, hj, m', hm', hr'⟩ := e1 Ex.length m0 s r mEx hr
      rcases getElem?_snoc_cases hm' with ⟨hjl, hm2⟩ | ⟨h, -⟩
      · have hmem : m' ∈ B := by
          have : m' ∈ Ex := List.mem_of_getElem? hm2
          rw [← hEx] at this; exact (List.mem_filter.1 this).1
        obtain ⟨j2, hj2⟩ := mem_getElem? hmem
        have hj2l : j2 < B.length := (List.getElem?_eq_some_iff.1 hj2).1
        exact ⟨j2, hj2l, m', by rw [List.getElem?_append_left hj2l]; exact hj2, hr'⟩
      · omega
  · intro i j m1 m2 sr hi hj hr1 hr2
    rcases getElem?_snoc_cases hi with ⟨hil, hi'⟩ | ⟨rfl, rfl⟩ <;>
      rcases getElem?_snoc_cases hj with ⟨hjl, hj'⟩ | ⟨rfl, rfl⟩
    · exact b2 i j m1 m2 sr hi' hj' hr1 hr2
    · obtain ⟨j', hj'l, hj'⟩ := inEx hi' hr1
      have := e2 j' Ex.length m1 m2 sr (exIdx hj'l hj') mEx hr1 hr2
      omega
    · obtain ⟨j', hj'l, hj'⟩ := inEx hj' hr2
      have := e2 j' Ex.length m2 m1 sr (exIdx hj'l hj') mEx hr2 hr1
      omega
    · rfl
  · intro i j m1 m2 o o' hi hj c1 c2 ho ho' hs
    rcases getElem?_snoc_cases hi with ⟨hil, hi'⟩ | ⟨rfl, rfl⟩
    · rcases getElem?_snoc_cases hj with ⟨hjl, hj'⟩ | ⟨rfl, rfl⟩
      · exact b3 i j m1 m2 o o' hi' hj' c1 c2 ho ho' hs
      · exact absurd c2 hm
    · exact absurd c1 hm

/-- Appending a client request of a new object to `B_k`. -/
theorem ro_append_cr (B : List MsgV) (m : MsgV) (o : ObjV) (hB : RoundsOrdered B)
    (hm : m.ty = tyClientRequest) (hmo : m.obj = some o)
    (hnew : ∀ m' ∈ B, m'.ty = tyClientRequest → ∀ o', m'.obj = some o' → o'.proSeq ≠ o.proSeq) :
    RoundsOrdered (B ++ [m]) := by
  obtain ⟨b1, b2, b3⟩ := hB
  have hr : ∀ sr, msgRound m ≠ some sr := fun sr h => msgRound_ty h hm
  refine ⟨?_, ?_, ?_⟩
  · intro i m0 s r hi hr0
    rcases getElem?_snoc_cases hi with ⟨hil, hi'⟩ | ⟨rfl, rfl⟩
    · obtain ⟨j, hj, m', hm', hr'⟩ := b1 i m0 s r hi' hr0
      exact ⟨j, hj, m', by rw [List.getElem?_append_left (by omega)]; exact hm', hr'⟩
    · exact absurd hr0 (hr _)
  · intro i j m1 m2 sr hi hj hr1 hr2
    rcases getElem?_snoc_cases hi with ⟨hil, hi'⟩ | ⟨rfl, rfl⟩
    · rcases getElem?_snoc_cases hj with ⟨hjl, hj'⟩ | ⟨rfl, rfl⟩
      · exact b2 i j m1 m2 sr hi' hj' hr1 hr2
      · exact absurd hr2 (hr _)
    · exact absurd hr1 (hr _)
  · intro i j m1 m2 o1 o2 hi hj c1 c2 ho1 ho2 hs
    rcases getElem?_snoc_cases hi with ⟨hil, hi'⟩ | ⟨rfl, rfl⟩ <;>
      rcases getElem?_snoc_cases hj with ⟨hjl, hj'⟩ | ⟨rfl, rfl⟩
    · exact b3 i j m1 m2 o1 o2 hi' hj' c1 c2 ho1 ho2 hs
    · rw [hmo] at ho2; cases ho2
      exact absurd hs (hnew m1 (List.mem_of_getElem? hi') c1 o1 ho1)
    · rw [hmo] at ho1; cases ho1
      exact absurd hs.symm (hnew m2 (List.mem_of_getElem? hj') c2 o2 ho2)
    · rfl

theorem map_length_set {α : Type} (P : List (List α)) (X : Nat) (px lp : List α)
    (hpx : P[X]? = some px) (hl : lp.length = px.length + 1) :
    (P.set X lp).map List.length =
      (P.map List.length).set X ((P.map List.length).getD X 0 + 1) := by
  rw [List.map_set]
  congr 1
  simp [hpx, hl]

end Perennial.rabia.roles.server.layers.network

namespace Perennial.rabia.roles.server.layers.network

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode model Net rabia.internal.message
  rabia.internal.config rabia rabia.internal.tcp

section ghost2
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics] [π : NetProtoGS]

/-- The serializer's step on the `R`-th forward `m` (log `bl ++ [b]`): `B_k ++ [m]` keeps its
rounds in order, its client requests' permits, its other messages a prefix of `E_k`. -/
theorem ser_step (γl : SrvNames) (B Ex : List MsgV) (bl : List Bool) (b : Bool) (m : MsgV)
    (hbl : (bl.filter id).length = Ex.length) (hEx : ExLogOk Ex) (hB : RoundsOrdered B)
    (hBEx : B.filter (fun m => decide (m.ty ≠ tyClientRequest)) = Ex) :
    exLb (GF := GF) γl Ex ∗
      ([∗list] m ∈ B.filter (fun m => decide (m.ty = tyClientRequest)),
        ∃ o : ObjV, ⌜m.obj = some o⌝ ∗ crTok γl o.proSeq.toNat) ∗
      (if (bl ++ [b])[bl.length]? = some true then
        iprop(∃ l : List MsgV, exLb γl l ∗
          ⌜l[((bl ++ [b]).take bl.length |>.filter id).length]? = some m ∧ ExLogOk l⌝)
       else iprop(∃ o : ObjV, ⌜m.ty = tyClientRequest ∧ m.obj = some o⌝ ∗ crTok γl o.proSeq.toNat)) ⊢
    ∃ Ex' : List MsgV, exLb γl Ex' ∗
      ([∗list] m ∈ (B ++ [m]).filter (fun m => decide (m.ty = tyClientRequest)),
        ∃ o : ObjV, ⌜m.obj = some o⌝ ∗ crTok γl o.proSeq.toNat) ∗
      ⌜ExLogOk Ex' ∧ RoundsOrdered (B ++ [m]) ∧
        (B ++ [m]).filter (fun m => decide (m.ty ≠ tyClientRequest)) = Ex' ∧
        ((bl ++ [b]).filter id).length = Ex'.length⌝ := by
  iintro ⟨#Hexlb, Htoks, Hrest⟩
  have htake : (bl ++ [b]).take bl.length = bl := by simp
  have hget : (bl ++ [b])[bl.length]? = some b := by simp
  rw [htake, hget]
  cases b
  · simp only [Option.some.injEq, Bool.false_eq_true, ↓reduceIte]
    icases Hrest with ⟨%o, %Hmo, Htok⟩
    icases crToks_fresh γl _ _ $$ [$Htoks $Htok] with ⟨Htoks, Htok, %hfresh⟩
    have hnew : ∀ m' ∈ B, m'.ty = tyClientRequest → ∀ o', m'.obj = some o' → o'.proSeq ≠ o.proSeq := by
      intro m' hm' hc o' ho' heq
      exact hfresh m' (List.mem_filter.2 ⟨hm', by simpa using hc⟩) o' ho' (by rw [heq])
    iexists Ex
    iframe Hexlb
    have hf : (B ++ [m]).filter (fun m => decide (m.ty = tyClientRequest)) =
        B.filter (fun m => decide (m.ty = tyClientRequest)) ++ [m] := by
      rw [List.filter_append]; simp [Hmo.1]
    isplitl
    · rw [hf]
      iapply BigSepL.bigSepL_snoc.2
      iframe Htoks
      iexists o
      iframe Htok
      ipureintro; exact Hmo.2
    ipureintro
    refine ⟨hEx, ro_append_cr B m o hB Hmo.1 Hmo.2 hnew, ?_, ?_⟩
    · rw [List.filter_append, hBEx]; simp [Hmo.1]
    · simpa using hbl
  · simp only [↓reduceIte]
    icases Hrest with ⟨%l, #Hl, %Hlm⟩
    rw [hbl] at Hlm
    obtain ⟨Hlm, Hlok⟩ := Hlm
    unfold exLb
    ihave %Hpre := mono_list_lb_valid _ _ _ $$ Hexlb Hl
    have hlen : Ex.length < l.length := (List.getElem?_eq_some_iff.1 Hlm).1
    have hpre : Ex <+: l := by
      rcases Hpre with h | h
      · exact h
      · have := h.length_le; omega
    have hpre2 : Ex ++ [m] <+: l := by
      obtain ⟨t, rfl⟩ := hpre
      rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self] at Hlm
      match t, Hlm with
      | a :: t, Hlm =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at Hlm
        subst Hlm
        exact ⟨t, by simp⟩
    have hEx' : ExLogOk (Ex ++ [m]) := exLogOk_prefix Hlok hpre2
    have hmty : m.ty ≠ tyClientRequest := hEx'.2 m (by simp)
    iexists Ex ++ [m]
    isplitr
    · iapply monoListLbOwn_le _ hpre2 $$ Hl
    have hf : (B ++ [m]).filter (fun m => decide (m.ty = tyClientRequest)) =
        B.filter (fun m => decide (m.ty = tyClientRequest)) := by
      rw [List.filter_append]; simp [hmty]
    isplitl
    · rw [hf]
      iexact Htoks
    ipureintro
    refine ⟨hEx', ro_append_exec B Ex m hB hBEx hEx'.1 hmty, ?_, ?_⟩
    · rw [List.filter_append, hBEx]; simp [hmty]
    · simp [hbl]

end ghost2

end Perennial.rabia.roles.server.layers.network

namespace Perennial.rabia.roles.server.layers.network
open model rabia

/-! ## The size of the messages' encodings (H-N-1) -/

theorem varint_len_le (k : Nat) : ∀ n, n < 128 ^ (k + 1) → (varint n).length ≤ k + 1 := by
  induction k with
  | zero => intro n h; rw [varint]; simp at h; simp [h]
  | succ k ih =>
    intro n h
    rw [varint]
    split
    · simp
    · simp only [List.length_cons]
      have := ih (n / 128) (by rw [Nat.div_lt_iff_lt_mul (by omega)]; rw [Nat.pow_succ] at h; exact h)
      omega

theorem varint_len_w32 (x : w32) : (varint x.toNat).length ≤ 5 :=
  varint_len_le 4 _ (by have := x.isLt; simp at *; omega)

theorem varint_len_64 (n : Nat) (h : n < 2 ^ 64) : (varint n).length ≤ 10 :=
  varint_len_le 9 _ (by simp at *; omega)

theorem encScalar_len (t : w8) (n : Nat) : (encScalar t n).length ≤ 1 + (varint n).length := by
  unfold encScalar; split <;> simp; omega

theorem flatMap_varint_len (l : List w32) : (l.flatMap fun n => varint n.toNat).length ≤ 5 * l.length := by
  induction l with
  | nil => simp
  | cons x l ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    have := varint_len_w32 x
    omega

theorem encPacked_len (t : w8) (l : List w32) (h : l.length ≤ 10) : (encPacked t l).length ≤ 52 := by
  unfold encPacked
  split
  · simp
  · simp only [encBytes, List.length_cons, List.length_append]
    have h1 := flatMap_varint_len l
    have h2 := varint_len_le 0 (l.flatMap fun n => varint n.toNat).length (by omega)
    omega

theorem flatMap_encBytes_len (cs : List GoString) (h : ∀ c ∈ cs, c.length < cmdBound) :
    (cs.flatMap (encBytes 0x3a)).length ≤ 409604 * cs.length := by
  induction cs with
  | nil => simp
  | cons c cs ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons, encBytes]
    have hc := h c (by simp)
    have ih := ih (fun c' hc' => h c' (by simp [hc']))
    have := varint_len_le 2 c.length (by unfold cmdBound at hc; omega)
    unfold cmdBound at hc; rw [Nat.mul_succ]; omega

/-- The objects Rabia's servers send: a batch of at most 10 requests, commands within
`cmdBound`. -/
theorem encObj_len (o : ObjV) (hc : o.cliIds.length ≤ 10) (hs : o.cliSeqs.length ≤ 10)
    (hl : o.commands.length ≤ 10) (hcmd : ∀ c ∈ o.commands, c.length < cmdBound) :
    (encObj o).length ≤ 4100000 := by
  unfold encObj
  simp only [List.length_append]
  have a1 := encScalar_len 0x08 o.proId.toNat
  have a2 := encScalar_len 0x10 o.proSeq.toNat
  have a3 := encScalar_len 0x18 o.svrSeq.toNat
  have b1 := varint_len_w32 o.proId
  have b2 := varint_len_w32 o.proSeq
  have b3 := varint_len_w32 o.svrSeq
  have p1 := encPacked_len 0x2a o.cliIds hc
  have p2 := encPacked_len 0x32 o.cliSeqs hs
  have hn : (if o.isNull then [(0x20 : w8), 1] else []).length ≤ 2 := by split <;> simp
  have hcm := flatMap_encBytes_len o.commands hcmd
  omega

theorem encMsg_len (m : MsgV) (h : ∀ o, m.obj = some o → (encObj o).length ≤ 4100000) :
    (encMsg m).length < 2 ^ 32 := by
  have a1 := encScalar_len 0x08 (enumNat m.ty)
  have a2 := encScalar_len 0x10 m.phase.toNat
  have a3 := encScalar_len 0x18 m.value.toNat
  have b1 := varint_len_64 (enumNat m.ty) (by unfold enumNat; exact BitVec.isLt _)
  have b2 := varint_len_w32 m.phase
  have b3 := varint_len_w32 m.value
  unfold encMsg
  cases ho : m.obj with
  | none => simp only [List.length_append, List.length_nil]; omega
  | some o =>
    have := h o ho
    simp only [encBytes, List.length_cons, List.length_append]
    have := varint_len_le 3 (encObj o).length (by omega)
    omega

theorem slotOnly_encObj (o : ObjV) (b : Bool) (h : o.slotOnly b) : (encObj o).length ≤ 4100000 := by
  unfold model.ObjV.slotOnly at h
  rw [h]
  exact encObj_len _ (by simp) (by simp) (by simp) (by simp)

end Perennial.rabia.roles.server.layers.network

namespace Perennial.rabia.roles.server.layers.network

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode model Net rabia.internal.message
  rabia.internal.config rabia rabia.internal.tcp

section ghost3
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics] [π : NetProtoGS]

/-- An object with registered requests is small (unfolds `Proto.lean`'s `objOk` and `Ghost.lean`'s
`regFacts`: a missing law). The batch's bound (`≤ 10`, `ProxyBatchSize`) is not in `objOk` since
S3: hub request H2-N-1. -/
theorem objOk_encObj (γ : Names) (cf : RCfg) (o : ObjV) :
    objOk (GF := GF) γ cf o ⊢ objOk γ cf o ∗ ⌜(encObj o).length ≤ 4100000⌝ := by
  iintro H
  unfold objOk
  icases H with ⟨%rs, #H1, #H2, %h⟩
  ihave %hlen : ⌜rs.length = o.commands.length⌝ $$ [H2]
  · unfold regFacts
    icases H2 with ⟨%hl, -⟩
    ipureintro; exact hl
  obtain ⟨-, hc, hs, -, hbs, -, -, hcmd⟩ := id h
  have hb : rs.length ≤ 10 := Nat.le_trans hbs (RCfg.batchSize_le10 cf)
  isplitl
  · iexists rs
    iframe H1 H2
    ipureintro; exact h
  · ipureintro
    exact encObj_len o (by simp [hc]; omega) (by simp [hs]; omega) (by omega)
      (fun c hc' => by obtain ⟨i, -, -, h'⟩ := hcmd c hc'; exact h')

/-- The encoding of a `ProposalReply` fits a frame's length field (H-N-1). -/
theorem replyOk_encBound (γ : Names) (cf : RCfg) (j : Nat) (m : MsgV) :
    replyOk (GF := GF) γ cf j m ⊢ replyOk γ cf j m ∗ ⌜(encMsg m).length < 2 ^ 32⌝ := by
  iintro H
  unfold replyOk
  icases H with ⟨%o, %W, %b, %h, Hok, H3, H4⟩
  icases objOk_encObj γ cf o $$ Hok with ⟨Hok, %ho⟩
  isplitl
  · iexists o, W, b
    iframe
    ipureintro; exact h
  · ipureintro
    exact encMsg_len m (fun o' h' => by rw [h.2.2.1] at h'; cases h'; exact ho)

/-- The encoding of a broadcast message fits a frame's length field (H-N-1). -/
theorem bmsgOk_encBound (γ : Names) (cf : RCfg) (X : Nat) (m : MsgV) :
    bmsgOk (GF := GF) γ cf X m ⊢ bmsgOk γ cf X m ∗ ⌜(encMsg m).length < 2 ^ 32⌝ := by
  have hobj : ∀ o, m.obj = some o → (encObj o).length ≤ 4100000 → (encMsg m).length < 2 ^ 32 :=
    fun o ho hl => encMsg_len m (fun o' h' => by rw [ho] at h'; cases h'; exact hl)
  unfold bmsgOk
  iintro H
  by_cases h0 : m.ty = tyClientRequest
  · simp only [h0, ↓reduceIte]
    icases H with ⟨%o, %h, Hok⟩
    icases objOk_encObj γ cf o $$ Hok with ⟨Hok, %hl⟩
    isplitl
    · iexists o; iframe; ipureintro; exact h
    · ipureintro; exact hobj o h.1 hl
  simp only [h0, ↓reduceIte]
  by_cases h1 : m.ty = tyProposal
  · simp only [h1, ↓reduceIte]
    icases H with ⟨%o, %h, Hok, Hf⟩
    icases objOk_encObj γ cf o $$ Hok with ⟨Hok, %hl⟩
    isplitl
    · iexists o; iframe; ipureintro; exact h
    · ipureintro; exact hobj o h.1 hl
  simp only [h1, ↓reduceIte]
  by_cases h2 : m.ty = tyState
  · simp only [h2, ↓reduceIte]
    icases H with ⟨%o, %h, Hf⟩
    isplitl
    · iexists o; iframe; ipureintro; exact h
    · ipureintro; exact hobj o h.1 (slotOnly_encObj o false h.2.2)
  simp only [h2, ↓reduceIte]
  by_cases h3 : m.ty = tyVote
  · simp only [h3, ↓reduceIte]
    icases H with ⟨%o, %h, Hf⟩
    isplitl
    · iexists o; iframe; ipureintro; exact h
    · ipureintro; exact hobj o h.1 (slotOnly_encObj o false h.2)
  simp only [h3, ↓reduceIte]
  by_cases h4 : m.ty = tyProposalRequest
  · simp only [h4, ↓reduceIte]
    icases H with ⟨%h, Hf⟩
    isplitl
    · iframe; ipureintro; exact h
    · ipureintro; exact encMsg_len m (fun o h' => by rw [h.2] at h'; cases h')
  simp only [h4, ↓reduceIte]
  by_cases h5 : m.ty = tyDecision
  · simp only [h5, ↓reduceIte]
    icases H with ⟨%o, %d, %h, Hf, Hd⟩
    cases d with
    | null =>
      unfold decObjOk
      icases Hd with %hd
      isplitl
      · iexists o, .null; iframe; isplitr
        · ipureintro; exact h
        · ipureintro; exact hd
      · ipureintro; exact hobj o h (slotOnly_encObj o true hd.2.2)
    | obj id =>
      unfold decObjOk
      icases Hd with ⟨%hd, Hok⟩
      icases objOk_encObj γ cf o $$ Hok with ⟨Hok, %hl⟩
      isplitl
      · iexists o, .obj id; iframe; isplitr
        · ipureintro; exact h
        · dsimp only; iframe; ipureintro; exact hd
      · ipureintro; exact hobj o h hl
  simp only [h5, ↓reduceIte]
  iexfalso; iexact H

end ghost3

end Perennial.rabia.roles.server.layers.network
