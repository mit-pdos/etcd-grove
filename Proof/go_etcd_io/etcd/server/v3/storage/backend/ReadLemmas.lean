/-
Lemmas on the read side's predicates (`InvBackend.lean`): the slices a read returns
(`rdSlices`, `kvsOutRd`), and the clients' lemmas on a held read transaction (`rtHeld_view`,
`rtHeld_read`, `crtSnap_read`) and on a single-key range (`rtRange_single`). Lean-first (no Rocq
counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.backend.InvBackend
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.RangeLemmas
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.BksLemmas

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace backend

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.backend

section lemmas
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]

/-! ## The read side's states -/

theorem keyLe_refl (k : w64 × Nat) : keyLe k k := Or.inr ⟨rfl, Nat.le_refl _⟩

theorem keyLe_next_ver {k : w64 × Nat} {v : w64} {i : Nat} (h : keyLe k (v, i))
    (hv : uint.Z v + 1 < 2 ^ 64) : keyLe k (v + W64 1, 0) := by
  left
  show uint.Z k.1 < uint.Z (v + W64 1)
  have : uint.Z (v + W64 1) = uint.Z v + 1 := by word
  rcases h with h | ⟨h1, _⟩
  · simp only at h; omega
  · simp only at h1; rw [h1]; omega

theorem keyLe_next_idx {k : w64 × Nat} {v : w64} {i : Nat} (h : keyLe k (v, i)) :
    keyLe k (v, i + 1) := by
  rcases h with h | ⟨h1, h2⟩
  · left; exact h
  · right; exact ⟨h1, by simp only at h2 ⊢; omega⟩

theorem fresh_next_ver {V : Type} (M : GMap (w64 × Nat) V) (v : w64) (i : Nat)
    (hall : ∀ k x, M.lookup k = some x → keyLe k (v, i)) (hv : uint.Z v + 1 < 2 ^ 64) :
    M.lookup (v + W64 1, 0) = none := by
  cases h : M.lookup (v + W64 1, 0) with
  | none => rfl
  | some x =>
    exfalso
    have := hall _ x h
    have hz : uint.Z (v + W64 1) = uint.Z v + 1 := by word
    rcases this with h1 | ⟨h1, _⟩
    · simp only at h1; omega
    · simp only at h1
      have := congrArg (fun x : w64 => uint.Z x) h1; omega

theorem fresh_next_idx {V : Type} (M : GMap (w64 × Nat) V) (v : w64) (i : Nat)
    (hall : ∀ k x, M.lookup k = some x → keyLe k (v, i)) : M.lookup (v, i + 1) = none := by
  cases h : M.lookup (v, i + 1) with
  | none => rfl
  | some x =>
    exfalso
    rcases hall _ x h with h1 | ⟨_, h2⟩
    · simp only at h1; omega
    · simp only at h2; omega

theorem idsOk_writebackR {P : BParams} {W : WBuf} {R : RBuf} (hW : idsOk P W.bks)
    (hR : idsOk P R.bks) : idsOk P (writebackR W R).bks := by
  intro i es h
  simp only [writebackR, wbMerge] at h
  change ((gmapImap _ W.bks).lookup i).or (R.bks.lookup i) = some es at h
  cases hw : W.bks.lookup i with
  | some es' => exact hW i es' hw
  | none =>
    have : (gmapImap (fun id es => canon (bkOf R.bks id ++ es)) W.bks).lookup i = none := by
      show (W.bks.lookup i).map _ = none; rw [hw]; rfl
    rw [this, Option.none_or] at h
    exact hR i es h

theorem idsOk_reset {P : BParams} {R : RBuf} (hR : idsOk P R.bks) : idsOk P R.reset.bks := by
  intro i es h
  simp only [RBuf.reset, bksReset] at h
  rw [GMap.lookup_fmap] at h
  cases h' : R.bks.lookup i with
  | none =>
    rw [GMap.lookup_filter] at h
    simp only [h'] at h
    cases h
  | some es' => exact hR i es' h'

/-! ## The readers' view across a commit -/

theorem bkOf_bksReset (B : GMap w64 (List Ent)) (i : w64) : bkOf (bksReset B) i = [] := by
  unfold bkOf bksReset
  rw [GMap.lookup_fmap]
  cases (GMap.filter (fun _ es => !es.isEmpty) B) !! i <;> rfl

theorem vOf_reset (P : BParams) (D : Data) (R : RBuf) (n k : GoString) :
    vOf P (D, R.reset) n k = dget D n k := by
  unfold vOf ovB
  simp only [RBuf.reset, bkOf_bksReset]
  cases P.BT.lookup n <;> simp [lastVal]

theorem vData_lookup (P : BParams) (rv : RView) (nk : GoString × GoString) :
    (vData P rv).lookup nk = if P.HB nk.1 then none else vOf P rv nk.1 nk.2 := rfl

/-- A cached copy `X` that read as the state `(C, R)` before a commit that kept the view reads
as the new state `(C', R.reset)` over the new data. -/
theorem vData_rebase (P : BParams) (C C' : Data) (X R : RBuf)
    (h1 : vData P (C, X) = vData P (C, R)) (h2 : vData P (C', R.reset) = vData P (C, R)) :
    vData P (C', X) = vData P (C', R.reset) := by
  apply GMap.ext_iff'.2
  intro nk
  have e1 := congrArg (fun M => GMap.lookup M nk) h1
  have e2 := congrArg (fun M => GMap.lookup M nk) h2
  simp only [vData_lookup] at e1 e2 ⊢
  split
  · rfl
  · rename_i hb
    simp only [hb, Bool.false_eq_true, ↓reduceIte] at e1 e2
    rw [vOf_reset] at e2 ⊢
    unfold vOf ovB at e1 ⊢
    cases hA : (P.BT.lookup nk.1).bind (fun i => lastVal (bkOf X.bks i) nk.2) with
    | none => rfl
    | some x =>
      rw [hA] at e1
      simp only [Option.some_or] at e1 ⊢
      unfold vOf ovB at e2
      rw [e2, ← e1]

/-! ## Map points-to fractions -/

section maps
variable {K V : Type} [ZeroVal K] [DecidableEq K] [ZeroVal V] [go.IntoValInj K]

theorem ownMap_split (l : Loc) (q1 q2 : Qp) (m : GMap K V) :
    ownMap (GF := GF) l (DFrac.own (q1 + q2)) m ⊢
      ownMap l (DFrac.own q1) m ∗ ownMap l (DFrac.own q2) m := by
  rw [ownMap_unseal]
  iintro H
  unfold ownMapDef
  icases H with ⟨%mv, %mp, Hown, %Hm, %Ha, %Hd, %Hdef⟩
  icases ((heapPointsto_fractional l mv).fractional q1 q2).1 $$ Hown
    with ⟨H1, H2⟩
  isplitl [H1]
  · iexists mv, mp; iframe H1; ipureintro; exact ⟨Hm, Ha, Hd, Hdef⟩
  · iexists mv, mp; iframe H2; ipureintro; exact ⟨Hm, Ha, Hd, Hdef⟩

theorem ownMap_combine (l : Loc) (q1 q2 : Qp) (m : GMap K V) :
    ownMap (GF := GF) l (DFrac.own q1) m ∗ ownMap l (DFrac.own q2) m ⊢
      ownMap l (DFrac.own (q1 + q2)) m := by
  rw [ownMap_unseal]
  unfold ownMapDef
  iintro ⟨⟨%mv, %mp, H1, %Hm, %Ha, %Hd, %Hdef⟩, ⟨%mv2, %mp2, H2, -⟩⟩
  ihave %Hv := heapPointsto_agree _ _ _ _ _ $$ [H1 H2]
  · iframe
  subst Hv
  iexists mv2, mp
  isplitl
  · iapply ((heapPointsto_fractional l mv2).fractional q1 q2).2
    iframe
  ipureintro; exact ⟨Hm, Ha, Hd, Hdef⟩

theorem ownMap_agree [go.IntoValInj V] (l : Loc) (dq1 dq2 : DFrac) (m1 m2 : GMap K V) :
    ownMap (GF := GF) l dq1 m1 ∗ ownMap l dq2 m2 ⊢ ⌜m1 = m2⌝ := by
  rw [ownMap_unseal]
  unfold ownMapDef
  iintro ⟨⟨%mv, %mp, H1, %Hm, %Ha, -⟩, ⟨%mv2, %mp2, H2, %Hm2, %Ha2, -⟩⟩
  ihave %Hv := heapPointsto_agree _ _ _ _ _ $$ [H1 H2]
  · iframe
  subst Hv
  ipureintro
  apply GMap.ext_iff'.2
  intro k
  have h1 := Ha k
  have h2 := Ha2 k
  rw [← go.mapLookup_pure _ _ _ Hm, go.mapLookup_pure _ _ _ Hm2, h2] at h1
  cases e1 : m1.lookup k <;> cases e2 : m2.lookup k <;>
    rw [e1, e2] at h1 <;> simp at h1
  all_goals first | rfl | (congr 1; exact (go.intoVal_inj h1).symm)

theorem ownMap_valid (l : Loc) (q : Qp) (m : GMap K V) :
    ownMap (GF := GF) l (DFrac.own q) m ⊢ ⌜q.val ≤ 1⌝ := by
  rw [ownMap_unseal]
  unfold ownMapDef
  iintro ⟨%mv, %mp, H1, -⟩
  iapply heapPointsto_frac_valid $$ H1

end maps

/-! ## The receipts' sum -/

theorem toList_insert_perm {V : Type} (m : GMap Nat V) (k : Nat) (v : V) (h : m.lookup k = none) :
    (GMap.insert k v m).toList.Perm ((k, v) :: m.toList) := by
  have hn1 : (GMap.insert k v m).toList.Nodup :=
    list_nodup_of_map Prod.fst _ (GMap.toList_keys_nodup _)
  have hn2 : ((k, v) :: m.toList).Nodup := by
    refine List.nodup_cons.2 ⟨fun hm => ?_, list_nodup_of_map Prod.fst _ (GMap.toList_keys_nodup _)⟩
    have := (GMap.mem_toList m k v).1 hm
    rw [show m !! k = m.lookup k from rfl, h] at this; cases this
  apply (List.perm_ext_iff_of_nodup hn1 hn2).2
  intro ⟨k', v'⟩
  rw [GMap.mem_toList, List.mem_cons, GMap.mem_toList]
  by_cases hk : k = k'
  · subst hk
    rw [GMap.lookup_insert]
    constructor
    · intro h'; cases h'; left; rfl
    · rintro (h' | h')
      · cases h'; rfl
      · rw [show m !! k = m.lookup k from rfl, h] at h'; cases h'
  · rw [GMap.lookup_insert_ne _ _ hk]
    constructor
    · intro h'; right; exact h'
    · rintro (h' | h')
      · cases h'; exact absurd rfl hk
      · exact h'

theorem perm_sum_rat {l l' : List Rat} (h : l.Perm l') : l.sum = l'.sum := by
  induction h with
  | nil => rfl
  | cons x _ ih => simp [ih]
  | swap x y l => simp; grind
  | trans _ _ ih1 ih2 => rw [ih1, ih2]

theorem le_sum_of_mem_nat {l : List Nat} {x : Nat} (h : x ∈ l) : x ≤ l.sum := by
  induction l with
  | nil => cases h
  | cons a t ih =>
    simp only [List.sum_cons]
    rcases List.mem_cons.1 h with h | h
    · omega
    · have := ih h; omega

theorem gmap_fresh_nat {V : Type} (m : GMap Nat V) : ∃ k, m.lookup k = none := by
  refine ⟨m.domList.sum + 1, ?_⟩
  cases h : m.lookup (m.domList.sum + 1) with
  | none => rfl
  | some v =>
    exfalso
    have hm := (GMap.mem_dom_list m _).2 (by show (m !! _).isSome; rw [show m !! _ = m.lookup _ from rfl, h]; rfl)
    have := le_sum_of_mem_nat hm
    omega

theorem qsum_empty : qsum (∅ : GMap Nat Qp) = 0 := by
  unfold qsum; rw [GMap.toList_empty]; rfl

theorem qsum_insert (m : GMap Nat Qp) (k : Nat) (v : Qp) (h : m.lookup k = none) :
    qsum (GMap.insert k v m) = qsum m + (v : Rat) := by
  unfold qsum
  rw [perm_sum_rat ((toList_insert_perm m k v h).map _)]
  simp only [List.map_cons, List.sum_cons]
  grind

theorem qsum_delete (m : GMap Nat Qp) (k : Nat) (v : Qp) (h : m.lookup k = some v) :
    qsum m = qsum (GMap.delete k m) + (v : Rat) := by
  have h1 : m = GMap.insert k v (GMap.delete k m) := (GMap.delete_insert_id m k v h).symm
  conv => lhs; rw [h1]
  exact qsum_insert _ _ _ (GMap.lookup_delete m k)

/-! ## The buckets map's and `txMu`'s first token's parts -/

theorem qp_add_mk (a : Rat) (ha : 0 < a) (r : Qp) (h : 0 < a + r.val) :
    (⟨a, ha⟩ : Qp) + r = ⟨a + r.val, h⟩ := rfl

theorem ghostVar_le_one {A : Type} [Pos.Countable A] (γ : GName) (q : Qp) (a : A) :
    ghostVar (GF := GF) γ q a ⊢ ⌜q.val ≤ 1⌝ := by
  iintro H
  have hq : q = q.half + q.half := (Qp.half_add_half q).symm
  rw [hq]
  icases ((ghostVar_fractional (GF := GF) γ a).fractional q.half q.half).1 $$ H with ⟨H1, H2⟩
  ihave %Hv := ghostVar_valid_2 γ a q.half a q.half $$ H1 H2
  ipureintro
  exact Hv.1

theorem mapPart_split (cm : GoMap) (qm : Rat) (r : Qp) (M : GMap w64 Loc) (h : r.val ≤ qm) :
    mapPart (GF := GF) cm qm M ⊢ mapPart cm (qm - r.val) M ∗ cm ↦${DFrac.own r} M := by
  have hr := r.2
  have hq : 0 < qm := by grind
  unfold mapPart
  rw [dif_pos hq]
  by_cases h0 : 0 < qm - r.val
  · rw [dif_pos h0]
    have : (⟨qm, hq⟩ : Qp) = ⟨qm - r.val, h0⟩ + r := by
      rw [qp_add_mk _ _ _ (by grind)]; congr 1; grind
    rw [this]
    iintro H
    iapply ownMap_split $$ H
  · rw [dif_neg h0]
    have : (⟨qm, hq⟩ : Qp) = r := Subtype.ext (by show qm = r.val; grind)
    rw [this]
    iintro H; iframe

theorem mapPart_join (cm : GoMap) (qm : Rat) (r : Qp) (M : GMap w64 Loc) (h : 0 ≤ qm) :
    mapPart (GF := GF) cm qm M ∗ cm ↦${DFrac.own r} M ⊢ mapPart cm (qm + r.val) M := by
  have hr := r.2
  unfold mapPart
  rw [dif_pos (show 0 < qm + r.val by grind)]
  by_cases h0 : 0 < qm
  · rw [dif_pos h0, ← qp_add_mk _ h0]
    iintro ⟨H1, H2⟩
    iapply ownMap_combine; iframe
  · rw [dif_neg h0]
    have : (⟨qm + r.val, by grind⟩ : Qp) = r := Subtype.ext (by show qm + r.val = r.val; grind)
    rw [this]
    iintro ⟨_, H⟩; iexact H

theorem tokPart_split (γ : BNames) (a : Rat) (r : Qp) (h : r.val ≤ a) :
    tokPart (GF := GF) γ a ⊢ tokPart γ (a - r.val) ∗ ghostVar γ.txa r () := by
  have hr := r.2
  have hq : 0 < a := by grind
  unfold tokPart
  rw [dif_pos hq]
  by_cases h0 : 0 < a - r.val
  · rw [dif_pos h0]
    have : (⟨a, hq⟩ : Qp) = ⟨a - r.val, h0⟩ + r := by
      rw [qp_add_mk _ _ _ (by grind)]; congr 1; grind
    rw [this]
    iintro H
    iapply ((ghostVar_fractional (GF := GF) γ.txa ()).fractional _ _).1 $$ H
  · rw [dif_neg h0]
    have : (⟨a, hq⟩ : Qp) = r := Subtype.ext (by show a = r.val; grind)
    rw [this]
    iintro H; iframe

theorem tokPart_join (γ : BNames) (a : Rat) (r : Qp) (h : 0 ≤ a) :
    tokPart (GF := GF) γ a ∗ ghostVar γ.txa r () ⊢ tokPart γ (a + r.val) := by
  have hr := r.2
  unfold tokPart
  rw [dif_pos (show 0 < a + r.val by grind)]
  by_cases h0 : 0 < a
  · rw [dif_pos h0, ← qp_add_mk _ h0]
    iintro ⟨H1, H2⟩
    iapply ((ghostVar_fractional (GF := GF) γ.txa ()).fractional _ _).2; iframe
  · rw [dif_neg h0]
    have : (⟨a + r.val, by grind⟩ : Qp) = r := Subtype.ext (by show a + r.val = r.val; grind)
    rw [this]
    iintro ⟨_, H⟩; iexact H

/-- The token's part is at most the whole token. -/
theorem tokPart_le (γ : BNames) (a : Rat) :
    tokPart (GF := GF) γ a ⊢ ⌜a ≤ 1⌝ ∗ tokPart γ a := by
  unfold tokPart
  by_cases h : 0 < a
  · rw [dif_pos h]
    iintro H
    ihave %Hb := ghostVar_le_one $$ H
    iframe; ipureintro; exact Hb
  · rw [dif_neg h]
    iintro _; iframe; ipureintro; grind

/-- A fraction of the map, out of the invariant against the same fraction of the token. -/
theorem intv_borrow (γ : BNames) (P : BParams) (rtx : Loc) (cm : GoMap) (D : Data) (r : Qp)
    (E : CoPset) (hE : ↑(bN.@"intv") ⊆ E) :
    intvInv (GF := GF) γ P rtx cm D ∗ ghostVar γ.txa r () ⊢
      |={E}=> ∃ M : GMap w64 Loc, cm ↦${DFrac.own r} M ∗ □ cmFacts P rtx D M := by
  iintro ⟨Hinv, Ht⟩
  unfold intvInv
  icases Hinv with ⟨#Hi, -⟩
  iinv Hi with ⟨%M, %qm, >#Hf, >%Hq, >Hm, >Htp⟩ Hclose
  ihave Htp := tokPart_join γ (1 - qm) r (by grind) $$ [Htp Ht]
  · iframe
  icases tokPart_le γ _ $$ Htp with ⟨%Hb, Htp⟩
  icases mapPart_split cm qm r M (by grind) $$ Hm with ⟨Hm, Hr⟩
  imod Hclose $$ [Hm Htp] with -
  · inext
    iexists M, qm - r.val
    rw [show 1 - (qm - r.val) = 1 - qm + r.val by grind]
    iframe; iframe #
    ipureintro; have := r.2; grind
  imodintro
  iexists M
  iframe; iframe #

/-- A fraction of the map back into the invariant (the writer's whole map possibly changed,
with its facts), for the same fraction of the token. -/
theorem intv_return (γ : BNames) (P : BParams) (rtx : Loc) (cm : GoMap) (D : Data) (r : Qp)
    (M : GMap w64 Loc) (E : CoPset) (hE : ↑(bN.@"intv") ⊆ E) :
    intvInv (GF := GF) γ P rtx cm D ∗ cm ↦${DFrac.own r} M ∗ □ cmFacts P rtx D M ⊢
      |={E}=> ghostVar γ.txa r () := by
  iintro ⟨Hinv, Hr, #Hf⟩
  unfold intvInv
  icases Hinv with ⟨#Hi, -⟩
  iinv Hi with ⟨%M', %qm, Hf', >%Hq, >Hm, >Htp⟩ Hclose
  ihave %Hrv := ownMap_valid cm r M $$ Hr
  -- the map's parts agree (when the invariant holds any) and fit in the whole map
  have hr := r.2
  by_cases h0 : 0 < qm
  · unfold mapPart
    rw [dif_pos h0]
    ihave %HM := ownMap_agree cm _ _ M' M $$ [Hm Hr]
    · iframe
    subst HM
    ihave Hm := ownMap_combine cm ⟨qm, h0⟩ r M' $$ [Hm Hr]
    · iframe
    rw [qp_add_mk _ h0 r (by grind)]
    ihave %Hv := ownMap_valid cm _ M' $$ Hm
    icases tokPart_split γ (1 - qm) r (by simp at Hv; grind) $$ Htp with ⟨Htp, Ht⟩
    imod Hclose $$ [Hm Htp] with -
    · inext
      iexists M', qm + r.val
      rw [show 1 - (qm + r.val) = 1 - qm - r.val by grind]
      iframe; iframe #
      rw [dif_pos (show 0 < qm + r.val by grind)]
      iframe
      ipureintro; simp at Hv; grind
    imodintro; iframe
  · have hq0 : qm = 0 := by grind
    subst hq0
    icases tokPart_split γ (1 - 0) r (by grind) $$ Htp with ⟨Htp, Ht⟩
    imod Hclose $$ [Hr Htp] with -
    · inext
      iexists M, r.val
      rw [show 1 - r.val = 1 - 0 - r.val by grind]
      iframe; iframe #
      unfold mapPart
      rw [dif_pos hr]
      iframe
      ipureintro; grind
    imodintro; iframe


/-! ## A cursor's entry -/

theorem curAt_some (tx : Loc) (es : List Ent) (n : Nat) (k v : GoSlice) (e : Ent)
    (h : es[n]? = some e) :
    curAt (GF := GF) tx es n k v ⊢ ⌜k ≠ slice.nil⌝ ∗ txBytes tx k e.1 ∗ txBytes tx v e.2 := by
  unfold curAt; rw [h]

theorem curAt_none (tx : Loc) (es : List Ent) (n : Nat) (k v : GoSlice) (h : es[n]? = none) :
    curAt (GF := GF) tx es n k v ⊢ ⌜k = slice.nil ∧ v = slice.nil⌝ := by
  unfold curAt; rw [h]

/-! ## The slices a read returns -/

instance rdSlices_persistent (rtx : Loc) (ss : List GoSlice) (bs : List GoString) :
    Persistent (rdSlices (GF := GF) rtx ss bs) := by
  unfold rdSlices; infer_instance

theorem rdSlices_nil (rtx : Loc) : ⊢ rdSlices (GF := GF) rtx [] [] := by
  unfold rdSlices
  simp only [List.zip_nil_left]
  iintro
  isplitr
  · ipureintro; rfl
  iapply BigSepL.bigSepL_nil.2; iempintro

theorem rdSlices_length (rtx : Loc) (ss : List GoSlice) (bs : List GoString) :
    rdSlices (GF := GF) rtx ss bs ⊢ ⌜ss.length = bs.length⌝ := by
  unfold rdSlices; iintro ⟨%H, _⟩; ipureintro; exact H

theorem rdSlices_snoc (rtx : Loc) (ss : List GoSlice) (bs : List GoString) (s : GoSlice)
    (b : GoString) :
    rdSlices (GF := GF) rtx ss bs ∗ rdB rtx s b ⊢ rdSlices rtx (ss ++ [s]) (bs ++ [b]) := by
  unfold rdSlices
  iintro ⟨⟨%Hlen, H⟩, #Hs⟩
  isplitr
  · ipureintro; simp [Hlen]
  rw [List.zip_append Hlen]
  iapply BigSepL.bigSepL_append.2
  iframe H
  simp only [List.zip_cons_cons, List.zip_nil_left]
  iapply BigSepL.bigSepL_singleton.2
  iexact Hs

theorem rdSlices_append (rtx : Loc) (ss ss' : List GoSlice) (bs bs' : List GoString) :
    rdSlices (GF := GF) rtx ss bs ∗ rdSlices rtx ss' bs' ⊢
      rdSlices rtx (ss ++ ss') (bs ++ bs') := by
  unfold rdSlices
  iintro ⟨⟨%Hlen, H⟩, ⟨%Hlen', H'⟩⟩
  isplitr
  · ipureintro; simp [Hlen, Hlen']
  rw [List.zip_append Hlen]
  iapply BigSepL.bigSepL_append.2
  iframe

theorem slicesAre_len (ss : List GoSlice) (bs : List GoString) :
    slicesAre (GF := GF) ss bs ⊢ ⌜ss.length = bs.length⌝ := by
  unfold slicesAre; iintro ⟨%H, _⟩; ipureintro; exact H

/-- The buffers' read-only slices are read slices. -/
theorem rdSlices_of_slicesAre (rtx : Loc) (ss : List GoSlice) (bs : List GoString) :
    slicesAre (GF := GF) ss bs ⊢ rdSlices rtx ss bs := by
  unfold slicesAre rdSlices
  iintro ⟨%Hlen, H⟩
  isplitr
  · ipureintro; exact Hlen
  iapply BigSepL.bigSepL_mono _ $$ H
  intro _ _ _
  iintro H
  unfold rdB
  ileft; iexact H

theorem kvsOutRd_of_kvsOut (rtx : Loc) (keys vals : GoSlice) (res : List Ent) :
    kvsOut (GF := GF) keys vals res ⊢ kvsOutRd rtx keys vals res := by
  unfold kvsOut kvsOutRd
  iintro ⟨%ks, %vs, Hk, Hkc, Hv, Hvc, Hka, Hva⟩
  iexists ks, vs
  iframe Hk Hkc Hv Hvc
  isplitl [Hka]
  · iapply rdSlices_of_slicesAre $$ Hka
  · iapply rdSlices_of_slicesAre $$ Hva

theorem kvsOutRd_nil (rtx : Loc) : ⊢ kvsOutRd (GF := GF) rtx slice.nil slice.nil [] := by
  iintro
  iapply kvsOutRd_of_kvsOut
  iapply kvsOut_nil_r

/-! ## Fractions of a read buffer agree on its layout -/

theorem bbAt_agree (bb : Loc) (dq1 dq2 : DFrac) (p1 p2 : BBPhys) (es : List Ent) :
    bbAt (GF := GF) bb dq1 p1 es ∗ bbAt bb dq2 p2 es ⊢ ⌜p1 = p2⌝ := by
  unfold bbAt
  iintro ⟨⟨H1, Hs1, -⟩, ⟨H2, Hs2, -⟩⟩
  icombine H1 H2 gives %h
  have hb : p1.buf = p2.buf := by simpa using congrArg bucketBuffer.buf' h
  rw [hb]
  ihave %hk := ownSlice_agree _ _ _ _ _ $$ Hs1 Hs2
  ipureintro
  cases p1; cases p2
  simp only at hb hk
  subst hb hk; rfl

theorem bksAt_agree (m : GoMap) (dq1 dq2 : DFrac) (P1 P2 : BksPhys) (B : GMap w64 (List Ent)) :
    bksAt (GF := GF) m dq1 P1 B ∗ bksAt m dq2 P2 B ⊢ ⌜P1 = P2⌝ := by
  unfold bksAt
  iintro ⟨⟨Hm1, Hb1⟩, ⟨Hm2, Hb2⟩⟩
  ihave %Hf := ownMap_agree (K := w64) (V := Loc) m dq1 dq2 (P1.fmap Prod.fst) (P2.fmap Prod.fst)
    $$ [Hm1 Hm2]
  · iframe
  iapply (show iprop(∀ id, ⌜P1 !! id = P2 !! id⌝) ⊢ iprop(⌜P1 = P2⌝) from
    (pure_forall (PROP := IProp GF)).2.trans (pure_mono (fun h => GMap.ext_iff'.2 h)))
  iintro %id
  have hid : (P1 !! id).map Prod.fst = (P2 !! id).map Prod.fst := by
    have := congrArg (fun M => M !! id) Hf
    simpa using this
  cases h1 : P1 !! id with
  | none =>
    cases h2 : P2 !! id with
    | none => ipureintro; rfl
    | some x2 => rw [h1, h2] at hid; cases hid
  | some x1 =>
    cases h2 : P2 !! id with
    | none => rw [h1, h2] at hid; cases hid
    | some x2 =>
      rw [h1, h2] at hid
      simp only [Option.map_some, Option.some.injEq] at hid
      icases bbs_lookup_acc P1 B dq1 id x1 h1 $$ Hb1 with ⟨%es1, %he1, Hx1, -⟩
      icases bbs_lookup_acc P2 B dq2 id x2 h2 $$ Hb2 with ⟨%es2, %he2, Hx2, -⟩
      rw [he1] at he2
      cases he2
      rw [hid]
      ihave %Hp := bbAt_agree x2.1 dq1 dq2 x1.2 x2.2 es1 $$ [Hx1 Hx2]
      · iframe
      ipureintro
      cases x1; cases x2
      simp only at hid Hp
      subst hid Hp; rfl

theorem rbAt_agree (txr : Loc) (dq1 dq2 : DFrac) (m1 m2 : GoMap) (P1 P2 : BksPhys) (R : RBuf) :
    rbAt (GF := GF) txr dq1 m1 P1 R ∗ rbAt txr dq2 m2 P2 R ⊢ ⌜m1 = m2 ∧ P1 = P2⌝ := by
  unfold rbAt
  iintro ⟨⟨Ht1, -, Hb1⟩, ⟨Ht2, -, Hb2⟩⟩
  icombine Ht1 Ht2 gives %h
  have hm : m1 = m2 := by simpa using congrArg txBuffer.buckets' h
  subst hm
  ihave %HP := bksAt_agree m1 dq1 dq2 P1 P2 R.bks $$ [Hb1 Hb2]
  · iframe
  ipureintro; exact ⟨rfl, HP⟩

theorem rbAt_ownRB (txr : Loc) (m : GoMap) (Pb : BksPhys) (R : RBuf) (h : bksOk Pb R.bks) :
    rbAt (GF := GF) txr (DFrac.own 1) m Pb R ⊢ ownRB txr R := by
  unfold rbAt ownRB ownBks
  iintro ⟨Ht, Hv, Hb⟩
  iexists m
  iframe
  ipureintro; exact h

theorem ownRB_rbAt (txr : Loc) (R : RBuf) :
    ownRB (GF := GF) txr R ⊢ ∃ (m : GoMap) (Pb : BksPhys),
      rbAt txr (DFrac.own 1) m Pb R ∗ ⌜bksOk Pb R.bks⌝ := by
  unfold rbAt ownRB ownBks
  iintro ⟨%m, Ht, Hv, %Pb, Hb, %h⟩
  iexists m, Pb
  iframe
  ipureintro; exact h

/-! ## A copy of the read buffer made read-only for good -/

theorem bbAt_persist (bb : Loc) (p : BBPhys) (es : List Ent) :
    bbAt (GF := GF) bb (DFrac.own 1) p es ⊢ |==> bbAt bb DFrac.discard p es := by
  unfold bbAt
  iintro ⟨Hb, Hs, Hc, #Hro, #Hin⟩
  ipersist Hb
  ipersist Hs
  ipersist Hc
  imodintro
  iframe #

theorem bbs_persist (n : Nat) (P : BksPhys) (B : GMap w64 (List Ent)) (hn : GMap.size P = n) :
    ([∗map] _id ↦ x;es ∈ P;B, bbAt (GF := GF) x.1 (DFrac.own 1) x.2 es) ⊢
      |==> [∗map] _id ↦ x;es ∈ P;B, bbAt (GF := GF) x.1 DFrac.discard x.2 es := by
  induction n generalizing P B with
  | zero =>
    have hP : P = ∅ := GMap.map_size_empty_inv P hn
    subst hP
    iintro H
    ihave %Hd := BigSepM2.bigSepM2_lookup_iff $$ H
    have hB : B = ∅ := by
      apply (GMap.mapEmpty B).2
      intro k
      have := Hd k
      cases h : B !! k with
      | none => rfl
      | some v =>
        exfalso
        have h2 : (Iris.Std.PartialMap.get? B k).isSome := by
          show (B !! k).isSome; rw [h]; rfl
        have := this.2 h2
        simp [Iris.Std.PartialMap.get?] at this
    subst hB
    imodintro
    iapply bbs_empty
  | succ n ih =>
    obtain ⟨id, x, hx⟩ := (GMap.map_size_ne_0_lookup P).1 (by omega)
    iintro H
    ihave %Hes := bbs_lookup_some P B _ id x hx $$ H
    obtain ⟨es, hes⟩ := Hes
    icases (BigSepM2.bigSepM2_delete (Φ := fun _ (x : Loc × BBPhys) es =>
        bbAt (GF := GF) x.1 (DFrac.own 1) x.2 es)
      (m1 := P) (m2 := B) (i := id) (x1 := x) (x2 := es) hx hes).1 $$ H with ⟨Hb, Hrest⟩
    imod bbAt_persist _ _ _ $$ Hb with Hb
    imod ih (GMap.delete id P) (GMap.delete id B)
      (by rw [GMap.map_size_delete_Some P id x hx]; omega) $$ Hrest with Hrest
    imodintro
    iapply (BigSepM2.bigSepM2_delete (Φ := fun _ (x : Loc × BBPhys) es =>
        bbAt (GF := GF) x.1 DFrac.discard x.2 es)
      (m1 := P) (m2 := B) (i := id) (x1 := x) (x2 := es) hx hes).2
    iframe

theorem bksAt_persist (m : GoMap) (P : BksPhys) (B : GMap w64 (List Ent)) :
    bksAt (GF := GF) m (DFrac.own 1) P B ⊢ |==> bksAt m DFrac.discard P B := by
  unfold bksAt
  iintro ⟨Hm, Hb⟩
  imod ownMap_persist _ _ _ $$ Hm with Hm
  imod bbs_persist _ P B rfl $$ Hb with Hb
  imodintro
  iframe

/-! ## A reader joins the interval -/

theorem wg_wgi_mask : (↑(bN.@"wg") : CoPset) ⊆ ⊤ \ ↑(bN.@"wgi") :=
  sync.wg_mask_ndot_ne bN "wg" "wgi" (by decide)

theorem wgOpen_excl (γw : GName) (q : Qp) :
    wgOpen (GF := GF) γw q ∗ wgOpen γw 1 ⊢ False := by
  unfold wgOpen
  iintro ⟨H1, H2⟩
  ihave %Hv := ghostVar_valid_2 γw () q () 1 $$ H1 H2
  exfalso; have := Hv.1; have := q.2
  simp only [Qp.le_iff, Qp.val_add, Qp.val_one] at *; grind

/-- A reader's `txWg.Add(1)` (holding `readTx.mu` while the interval is open): its budget token
deposited, a share of the bbolt transaction and its receipt. -/
theorem wp_rdAdd (γ : BNames) (rtx wg : Loc) (γw γo γt : GName) (q : Qp) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sync ∗ □ wgInv γ rtx wg γw γo γt ∗ wgOpen γw q ∗
        ownToks γ.rdt 1 }}
      (App (Val (wg @!! go.GoType.PointerType sync.WaitGroup.ty @!! go!"Add")) (Val #(W64 1)))
    {{ RET #(); ∃ (k : Nat) (q' : Qp), wgOpen γw q ∗ rdShare rtx γo k q' }} := by
  iintro %Φ ⟨#Hsync, #Hwgi, Hwo, Htok⟩ HΦ
  unfold wgInv
  icases Hwgi with ⟨%γwg, #Hisw, #Hi, #Hauth⟩
  iapply sync.WaitGroup.wp_Add wg (W64 1) γwg (bN.@"wg") $$ [] [Hwo Htok HΦ]
  · iframe #
  iinv Hi with >Hb Hclose
  iapply fupd_mask_intro wg_wgi_mask
  iintro Hmask
  inext
  iunfold wgBody at Hb
  icases Hb with (⟨%n, %outs, %pool, Hwgo, Hoa, Hpool, Htoks, %Hn, Hw⟩ | ⟨Hoa, Hwo', Htk⟩)
  rotate_left
  · iexfalso; iapply wgOpen_excl γw q $$ [$Hwo $Hwo']
  icases Hw with (Hw0 | Hwo')
  rotate_left
  · iexfalso; iapply wgOpen_excl γw q $$ [$Hwo $Hwo']
  ihave Htoks := ownToks_add_2 1 (sint.nat n) γ.rdt $$ [Htoks Htok]
  · iframe
  icombine Hauth Htoks gives %Hle
  have hn0 : 0 ≤ sint.Z n := by have := Hn.1; omega
  have h1 : sint.Z (W32 (sint.Z (W64 1))) = 1 := by decide
  have hnn : (sint.nat n : Int) = sint.Z n := Int.toNat_of_nonneg hn0
  have hlt : sint.Z n + 1 < 2 ^ 31 := by unfold rdMax at Hle; omega
  have hz : sint.Z (n + W32 (sint.Z (W64 1))) = sint.Z n + 1 := by
    rw [show W32 (sint.Z (W64 1)) = W32 1 from rfl]; word
  have hz' : sint.nat (n + W32 (sint.Z (W64 1))) = sint.nat n + 1 := by
    rw [show W32 (sint.Z (W64 1)) = W32 1 from rfl]; word
  obtain ⟨k, hk⟩ := gmap_fresh_nat outs
  iexists n
  iframe Hwgo
  isplitr
  · ipureintro; rw [h1]; omega
  iright
  iframe Hw0
  iintro Hw0 Hwgo
  imod Hmask with -
  imod ghost_map_insert k pool.half hk $$ Hoa with ⟨Hoa, Hrc⟩
  ihave Hpool2 : txLive rtx (pool.half + pool.half) $$ [Hpool]
  · rw [Qp.half_add_half]; iexact Hpool
  icases ((txLive_fractional rtx).fractional pool.half pool.half).1 $$ Hpool2 with ⟨Hp1, Hp2⟩
  imod Hclose $$ [Hwgo Hoa Hp1 Htoks Hw0] with -
  · inext
    unfold wgBody
    ileft
    iexists n + W32 (sint.Z (W64 1)), outs.insert k pool.half, pool.half
    rw [hz', show sint.nat n + 1 = 1 + sint.nat n by omega]
    iframe
    isplitr
    · ipureintro; rw [hz, GMap.map_size_insert_None outs k pool.half hk]; push_cast; omega
    ipureintro
    rw [qsum_insert outs k pool.half hk]
    have := Hn.2
    show pool.val / 2 + (qsum outs + pool.val / 2) = 1 / 2
    grind
  imodintro
  iapply HΦ
  iexists k, pool.half
  unfold rdShare
  iframe

/-! ## The cache's marks -/

/-- A client (its share of the view) marks the current state as copied into the cache: no
window is open. -/
theorem cache_mark (γ : BNames) (r q : Qp) (ver : w64) (idx : Nat) (win : Bool) (vd : VData) :
    cacheInv (GF := GF) γ ∗ ghostVar γ.cur r ((ver, idx), win) ∗ bView γ q vd ⊢
      |={⊤}=> (cachedAt γ ver idx ∗ ghostVar γ.cur r ((ver, idx), win) ∗ bView γ q vd ∗
        ⌜win = false⌝) := by
  iintro ⟨#Hci, Hcur, Hbv⟩
  unfold cacheInv
  iinv Hci with ⟨%Cs, %k, %w0, >Hca, >#Hels, >Hcurinv, >Hcvw, >%Hcs, >Hwin⟩ Hclose
  icombine Hcur Hcurinv gives %Hck
  have Hk := Hck.2
  simp only [Prod.mk.injEq] at Hk
  obtain ⟨rfl, rfl⟩ := Hk
  icases Hwin with (%Hw | ⟨%vd', Hbv'⟩)
  rotate_left
  · unfold bView
    icases Hbv with ⟨-, Hc1⟩
    icases Hbv' with ⟨-, Hc2⟩
    icombine Hc2 Hcvw as Hc3
    ihave %Hv := ghostVar_valid_2 γ.cvw () q.half () _ $$ Hc1 Hc3
    exfalso; have := Hv.1; have := q.half.2
    simp only [Qp.le_iff, Qp.val_add] at *
    have h1 : (Subtype.val (1 : Qp)) = 1 := rfl
    grind
  subst Hw
  have hne := Hcs.2 rfl
  cases hl : Cs.lookup (ver, idx) with
  | none =>
    imod ghost_map_insert_persist (ver, idx) true hl $$ Hca with ⟨Hca, #Hm⟩
    ihave #Hels' : [∗map] k' ↦ b ∈ Cs.insert (ver, idx) true,
        ghostMapElem γ.cached k' DFrac.discard b $$ []
    · iapply (BigSepM.bigSepM_insert_elim (M := GMap (w64 × Nat)) (m := Cs)
        (Φ := fun k b => ghostMapElem (GF := GF) γ.cached k DFrac.discard b)
        (i := (ver, idx)) (x := true)) $$ Hm Hels
    imod Hclose $$ [Hca Hcurinv Hcvw] with -
    · inext
      iexists Cs.insert (ver, idx) true, (ver, idx), false
      iframe; iframe #
      isplitr
      · ipureintro
        constructor
        · intro k' b h
          by_cases hk : (ver, idx) = k'
          · subst hk; exact keyLe_refl _
          · rw [GMap.lookup_insert_ne _ _ hk] at h; exact Hcs.1 k' b h
        · intro _; rw [GMap.lookup_insert]; simp
      ileft; ipureintro; rfl
    imodintro
    unfold cachedAt
    iframe; iframe #
    ipureintro; rfl
  | some b =>
    cases b
    · exact absurd hl hne
    ihave #Hm := BigSepM.bigSepM_lookup (show Iris.Std.PartialMap.get? Cs (ver, idx) = some true
      from hl) $$ Hels
    imod Hclose $$ [Hca Hcurinv Hcvw] with -
    · inext
      iexists Cs, (ver, idx), false
      iframe; iframe #
      isplitr
      · ipureintro; exact Hcs
      ileft; ipureintro; rfl
    imodintro
    unfold cachedAt
    iframe; iframe #
    ipureintro; rfl

/-- A mark at the current version is of a state up to the current one. -/
theorem cache_lookup (γ : BNames) (r : Qp) (ver : w64) (idx i : Nat) (win : Bool) :
    cacheInv (GF := GF) γ ∗ ghostVar γ.cur r ((ver, idx), win) ∗ cachedAt γ ver i ⊢
      |={⊤}=> (ghostVar γ.cur r ((ver, idx), win) ∗ ⌜i ≤ idx⌝) := by
  iintro ⟨#Hci, Hcur, #Hm⟩
  unfold cacheInv
  iinv Hci with ⟨%Cs, %k, %w0, >Hca, >#Hels, >Hcurinv, >Hcvw, >%Hcs, >Hwin⟩ Hclose
  icombine Hcur Hcurinv gives %Hck
  have Hk := Hck.2
  simp only [Prod.mk.injEq] at Hk
  obtain ⟨rfl, rfl⟩ := Hk
  unfold cachedAt
  icombine Hca Hm gives %Hl
  imod Hclose $$ [Hca Hcurinv Hcvw Hwin] with -
  · inext
    iexists Cs, (ver, idx), win
    iframe; iframe #
    ipureintro; exact Hcs
  imodintro
  iframe
  ipureintro
  rcases Hcs.1 _ _ Hl with h | ⟨_, h⟩
  · simp at h
  · exact h

/-- A client's share of the backend being open excludes its stop. -/
theorem bOpen_stopped (γ : BNames) (q : Qp) : bOpen (GF := GF) γ q ∗ bStopped γ ⊢ False := by
  unfold bOpen bStopped
  iintro ⟨⟨H1, -⟩, H2⟩
  ihave %H := dghostVar_agree γ.opn false _ true _ $$ H1 H2
  cases H

/-! ## The buckets cache's facts and the transaction's statistics -/

/-- What the cache holds for the bucket `bi` (of the table). -/
def bktFact (rtx : Loc) (D : Data) (n : GoString) (bk : Loc) : IProp GF :=
  iprop(⌜D.lookup n = none ∧ bk = Loc.null⌝ ∨
    ∃ m : BktData, ⌜D.lookup n = some m ∧ bk ≠ Loc.null⌝ ∗ rBkt rtx bk (bktEnts m))

instance bktFact_persistent (rtx : Loc) (D : Data) (n : GoString) (bk : Loc) :
    Persistent (bktFact (GF := GF) rtx D n bk) := by
  unfold bktFact; infer_instance

theorem cmFacts_lookup (P : BParams) (rtx : Loc) (D : Data) (M : GMap w64 Loc) (bi : BucketInfo)
    (bk : Loc) (hP : P.Wf) (hb : P.has bi) (hl : M.lookup bi.id = some bk) :
    cmFacts (GF := GF) P rtx D M ⊢ bktFact rtx D bi.name bk := by
  unfold cmFacts
  iintro H
  ihave H := BigSepM.bigSepM_lookup (show Iris.Std.PartialMap.get? M bi.id = some bk from hl) $$ H
  icases H with ⟨%n, %hn, H⟩
  have : n = bi.name := hP.1 n bi.name bi.id hn hb
  subst this
  unfold bktFact
  iexact H

theorem cmFacts_insert (P : BParams) (rtx : Loc) (D : Data) (M : GMap w64 Loc) (bi : BucketInfo)
    (bk : Loc) (hb : P.has bi) :
    cmFacts (GF := GF) P rtx D M ∗ bktFact rtx D bi.name bk ⊢
      cmFacts P rtx D (GMap.insert bi.id bk M) := by
  unfold cmFacts bktFact
  iintro ⟨H, Hf⟩
  iapply (BigSepM.bigSepM_insert_elim (M := GMap w64) (m := M) (i := bi.id) (x := bk)) $$ [Hf] H
  iexists bi.name
  iframe
  ipureintro; exact hb

theorem cmFacts_empty (P : BParams) (rtx : Loc) (D : Data) :
    ⊢ cmFacts (GF := GF) P rtx D (∅ : GMap w64 Loc) := by
  unfold cmFacts
  iintro
  iapply BigSepM.bigSepM_empty.2
  iempintro

/-- The statistics, out of the interval's invariant, for `txMu`'s second token. -/
theorem stats_take (γ : BNames) (P : BParams) (rtx : Loc) (cm : GoMap) (D : Data) (E : CoPset)
    (hE : ↑(bN.@"stats") ⊆ E) :
    intvInv (GF := GF) γ P rtx cm D ∗ ghostVar γ.txb 1 () ⊢ |={E}=> rtxStats rtx := by
  iintro ⟨Hinv, Ht⟩
  unfold intvInv
  icases Hinv with ⟨-, #Hs⟩
  iinv Hs with >Hc Hclose
  icases Hc with (Hst | Ht')
  · imod Hclose $$ [Ht] with -
    · inext; iright; iexact Ht
    imodintro; iexact Hst
  · ihave %Hv := ghostVar_valid_2 γ.txb () 1 () 1 $$ Ht Ht'
    exfalso; have := Hv.1; simp only [Qp.le_iff, Qp.val_add, Qp.val_one] at this; grind

/-- The statistics back, for `txMu`'s second token. -/
theorem stats_give (γ : BNames) (P : BParams) (rtx : Loc) (cm : GoMap) (D : Data) (E : CoPset)
    (hE : ↑(bN.@"stats") ⊆ E) :
    intvInv (GF := GF) γ P rtx cm D ∗ rtxStats rtx ⊢ |={E}=> ghostVar γ.txb 1 () := by
  iintro ⟨Hinv, Hst⟩
  unfold intvInv
  icases Hinv with ⟨-, #Hs⟩
  iinv Hs with >Hc Hclose
  icases Hc with (Hst' | Ht)
  · iexfalso; iapply rtxStats_excl rtx $$ [Hst Hst']; iframe
  · imod Hclose $$ [Hst] with -
    · inext; ileft; iexact Hst
    imodintro; iexact Ht

/-! ## The clients' lemmas on a held read transaction -/

/-- The held shared read transaction reads the clients' view. -/
theorem rtHeld_view (γ : BNames) (P : BParams) (b rtx : Loc) (rv : RView) (q : Qp) (vd : VData) :
    rtHeld (GF := GF) γ P b rtx rv ∗ bView γ q vd ⊢ ⌜vData P rv = vd⌝ := by
  unfold rtHeld rtResAt rtRest bView
  iintro ⟨⟨%rt, %rd, %H, -, -, ⟨%m, %Pb, %cm, -, -, -, Hview, -⟩, -⟩, Hbv, -⟩
  icombine Hview Hbv gives %Hv
  ipureintro; exact Hv.2

/-- A held shared read transaction's state keeps the safe-range discipline (`safeRv`: in a
safe-range bucket, bbolt's keys below the read buffer's). -/
theorem rtHeld_safe (γ : BNames) (P : BParams) (b rtx : Loc) (rv : RView) :
    rtHeld (GF := GF) γ P b rtx rv ⊢ rtHeld γ P b rtx rv ∗ ⌜safeRv P rv⌝ := by
  unfold rtHeld rtResAt rtRest rtCore
  iintro ⟨%rt, %rd, %H, #Hrt, Hrl, ⟨%m, %Pb, %cm, Hrb, %Hok, Hcm, Hview, Hrd, Hrvs,
    Hcur, Hhist, Hrtxf, Hwgf, %Hf, #Hha, #Hcv, Hpo, #Hauth, Hiv⟩, %Hrtx, Hcr⟩
  isplitl
  · iexists rt, rd, H
    iframe Hrt Hrl Hcr
    isplitl
    · iexists m, Pb, cm
      iframe; iframe #
      ipureintro; exact ⟨Hok, Hf⟩
    ipureintro; exact Hrtx
  ipureintro; exact Hf.2.2.2.2.2

/-- A slice a held shared read transaction returned, read (the backend open: its bbolt
transaction is). -/
theorem rtHeld_read (γ : BNames) (P : BParams) (b rtx : Loc) (rv : RView) (qo : Qp)
    (s : GoSlice) (v : GoString) :
    rtHeld (GF := GF) γ P b rtx rv ∗ bOpen γ qo ∗ rdB rtx s v ⊢
      ∃ dq : DFrac, s ↦*{dq} v ∗ (s ↦*{dq} v -∗ rtHeld γ P b rtx rv ∗ bOpen γ qo) := by
  iintro ⟨Hh, Ho, #Hs⟩
  unfold rdB
  icases Hs with (#Hs | #Hs)
  · iexists DFrac.discard
    iframe #
    iintro _
    iframe
  unfold rtHeld rtResAt rtRest rtCore rtIntv
  icases Hh with ⟨%rt, %rd, %H, #Hrt, Hrl, ⟨%m, %Pb, %cm, Hrb, %Hok, Hcm, Hview, Hrd, Hrvs,
    Hcur, Hhist, Hrtxf, Hwgf, %Hf, #Hha, #Hcv, Hpo, #Hauth, Hiv⟩, %Hrtx, Hcr⟩
  cases hl : rd.live
  · simp only [Bool.false_eq_true, ↓reduceIte]
    icases Hiv with ⟨-, #Hst⟩
    iexfalso; iapply bOpen_stopped γ qo $$ [$Ho $Hst]
  simp only [↓reduceIte]
  icases Hiv with ⟨Hlive, #Hsnap, #Hintv, #Hwgi, Hwo, Htk⟩
  subst Hrtx
  icases txBytes_acc rd.rtx s v sync.rfrac.half $$ [$Hs $Hlive] with ⟨%dq, Hsl, Hback⟩
  iexists dq
  iframe Hsl
  iintro Hsl
  ihave Hlive := Hback $$ Hsl
  iframe Ho
  iexists rt, rd, H
  iframe; iframe #
  rw [hl]
  simp only [↓reduceIte]
  iframe; iframe #
  isplitr
  · ipureintro; exact Hok
  ipureintro; exact Hf

/-- A slice a concurrent read transaction returned, read. -/
theorem crtSnap_read (γ : BNames) (P : BParams) (b crt rtx : Loc) (rv : RView) (s : GoSlice)
    (v : GoString) :
    crtSnap (GF := GF) γ P b crt rtx rv ∗ rdB rtx s v ⊢
      ∃ dq : DFrac, s ↦*{dq} v ∗ (s ↦*{dq} v -∗ crtSnap γ P b crt rtx rv) := by
  iintro ⟨Hc, #Hs⟩
  unfold rdB
  icases Hs with (#Hs | #Hs)
  · iexists DFrac.discard
    iframe #
    iintro _
    iframe
  unfold crtSnap rdShare
  icases Hc with ⟨%m, %Pb, %cm, %tm, %wg, %γw, %γo, %γt, %k, %q, %rt, #Hrt, #Htm, Hrb, #Hrtx,
    #Hcm, #Htm', #Hwg, Hown, #Hg, ⟨Hlive, Hrc⟩, #Hsnap, #Hintv, #Hwgi, %Hwf⟩
  icases txBytes_acc rtx s v q $$ [$Hs $Hlive] with ⟨%dq, Hsl, Hback⟩
  iexists dq
  iframe Hsl
  iintro Hsl
  ihave Hlive := Hback $$ Hsl
  iexists m, Pb, cm, tm, wg, γw, γo, γt, k, q, rt
  iframe; iframe #
  ipureintro; exact Hwf

/-! ## A single key's range -/

theorem bktEnts_sorted (m : BktData) : entsSorted (bktEnts m) := by
  unfold bktEnts
  have hn : ((m.toList.mergeSort entLe).map Prod.fst).Nodup :=
    (((List.mergeSort_perm m.toList entLe).map Prod.fst).nodup_iff).2 (GMap.toList_keys_nodup m)
  have hle := mergeSort_pairwise m.toList
  rw [List.Nodup, List.pairwise_map] at hn
  unfold entsSorted
  refine (hle.and hn).imp (fun ⟨h1, h2⟩ => ?_)
  rcases strLt_total h1 with e | e
  · exact absurd e.symm h2
  · exact e

theorem lastVal_bktEnts (m : BktData) (k : GoString) : lastVal (bktEnts m) k = m.lookup k := by
  unfold bktEnts
  rw [lastVal_mergeSort, lastVal_eq_filter]
  have hle := filter_key_length_le (GMap.toList_keys_nodup m) k
  cases h : m.lookup k with
  | none =>
    have : m.toList.filter (keyIs k) = [] := by
      apply List.filter_eq_nil_iff.2
      intro e he
      have := (GMap.mem_toList m e.1 e.2).1 he
      simp only [keyIs, decide_eq_true_eq]
      intro hk; rw [← hk] at h
      rw [show m !! e.1 = m.lookup e.1 from rfl, h] at this; cases this
    rw [this]; rfl
  | some v =>
    have hmem : (k, v) ∈ m.toList.filter (keyIs k) := by
      apply List.mem_filter.2
      refine ⟨(GMap.mem_toList m k v).2 h, by simp [keyIs]⟩
    generalize hf : m.toList.filter (keyIs k) = f at hle hmem
    match f, hle, hmem with
    | [x], _, hm =>
      simp only [List.mem_singleton] at hm
      subst hm; rfl

/-- A single key's lookup in sorted entries, as `Range` and the cursor loop find it. -/
theorem single_sorted (es : List Ent) (kb : GoString) (h : entsSorted es) :
    (match es.dropWhile (fun e => decide (strLt e.1 kb)) with
      | [] => []
      | e :: _ => if e.1 = kb then [e] else []) =
    (match lastVal es kb with
      | some v => [(kb, v)]
      | none => []) := by
  induction es with
  | nil => rfl
  | cons a t ih =>
    have ht : entsSorted t := (List.pairwise_cons.1 h).2
    have hall : ∀ y ∈ t, strLt a.1 y.1 := (List.pairwise_cons.1 h).1
    rw [lastVal_cons]
    by_cases hlt : strLt a.1 kb
    · rw [List.dropWhile_cons, _root_.decide_eq_true hlt]
      simp only [ite_true]
      rw [ih ht]
      have : ¬ a.1 = kb := fun he => strLt_irrefl _ (he ▸ hlt)
      simp only [this, ite_false, Option.or_none]
    · rw [List.dropWhile_cons, _root_.decide_eq_false hlt]
      simp only [Bool.false_eq_true, ite_false]
      have hnone : lastVal t kb = none := by
        apply lastVal_eq_none
        intro e he hek
        have := hall e he
        rw [hek] at this
        rcases strLt_total hlt with h1 | h1
        · rw [h1] at this; exact strLt_irrefl _ this
        · exact strLt_asymm h1 this
      rw [hnone, Option.none_or]
      by_cases hk : a.1 = kb
      · simp only [hk, ite_true]
        cases a; simp only at hk; subst hk; rfl
      · simp only [hk, ite_false]

theorem bbRange_single (es : List Ent) (kb : GoString) (lim : w64) (h : entsSorted es) :
    bbRange es kb [] lim = (match lastVal es kb with | some v => [(kb, v)] | none => []) := by
  rw [← single_sorted es kb h]
  unfold bbRange
  split <;> simp_all

theorem cursorRange_single (es : List Ent) (kb : GoString) (lim : w64) (h : entsSorted es) :
    cursorRange es kb [] lim = (match lastVal es kb with | some v => [(kb, v)] | none => []) := by
  rw [← single_sorted es kb h]
  unfold cursorRange seekIdx
  simp only [ite_true]
  have hd : ∀ l : List Ent, l.drop (l.takeWhile (fun e => decide (strLt e.1 kb))).length =
      l.dropWhile (fun e => decide (strLt e.1 kb)) := by
    intro l
    induction l with
    | nil => rfl
    | cons a t ih =>
      simp only [List.takeWhile_cons, List.dropWhile_cons]
      split <;> simp [ih]
  rw [hd es]
  cases es.dropWhile (fun e => decide (strLt e.1 kb)) with
  | nil => rfl
  | cons e rest =>
    rw [List.takeWhile_cons]
    by_cases he : e.1 = kb
    · simp [he]
    · simp [he]

/-- A single key's range (no end key) of a read transaction's state: the key's entry in the
readers' view, if any (the bucket of the table, the read buffer canonical). -/
theorem rtRange_single (P : BParams) (rv : RView) (bi : BucketInfo) (kb : GoString) (limit : w64)
    (hb : P.has bi) (hR : rv.2.Wf) :
    rtRange rv bi kb [] limit =
      (match vOf P rv bi.name kb with | some v => [(kb, v)] | none => []) := by
  have hs : entsSorted (bkOf rv.2.bks bi.id) := by
    unfold bkOf
    cases h : rv.2.bks.lookup bi.id with
    | none => exact entsSorted_nil
    | some es => exact hR bi.id es h
  have hvOf : vOf P rv bi.name kb =
      (lastVal (bkOf rv.2.bks bi.id) kb).or (dget rv.1 bi.name kb) := by
    unfold vOf ovB
    unfold BParams.has at hb
    rw [hb]; rfl
  unfold rtRange
  simp only [show rangeLimit [] limit = W64 1 from rfl]
  rw [bbRange_single _ _ _ hs, hvOf]
  cases hl : lastVal (bkOf rv.2.bks bi.id) kb with
  | some v => rfl
  | none =>
    simp only [List.length_nil, Option.none_or]
    rw [if_neg (by decide), cursorRange_single _ _ _ (bktEnts_sorted _), lastVal_bktEnts,
      List.append_nil]
    unfold bktOf dget
    cases rv.1.lookup bi.name <;> rfl

end lemmas

end backend
end EtcdGrove
end Perennial
