/-
Proof of `Spec/.../schema/unsafeGetAllUsers.lean`: the walk appending each value, then `proto.Unmarshal` of each. Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.schema.unsafeGetAllUsers
public import Spec.google_golang_org.protobuf.proto.UnmarshalUser

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.schema.Assumptions]

/-- An entry of a bucket's sorted entries is one of its key-value pairs. -/
private theorem bktEnts_lookup' {m : backend.BktData} {e : backend.Ent} (h : e ∈ backend.bktEnts m) :
    m.lookup e.1 = some e.2 :=
  (GMap.mem_toList m e.1 e.2).1 ((List.mergeSort_perm m.toList backend.entLe).mem_iff.1 h)

/-- Zipping one more element in front of a longer list. -/
private theorem zip_snoc' {α β : Type} (us : List α) (es : List β) (u : α) (e : β)
    (h : es[us.length]? = some e) : (us ++ [u]).zip es = us.zip es ++ [(u, e)] := by
  induction us generalizing es with
  | nil =>
    cases es with
    | nil => simp at h
    | cons x xs => simp at h; subst h; simp
  | cons a t ih =>
    cases es with
    | nil => simp at h
    | cons x xs =>
      simp only [List.length_cons, List.getElem?_cons_succ] at h
      simp [ih xs h]

/-- Filling the next slot of a slice whose first slots are set. -/
private theorem set_fill' {α : Type} (us : List α) (z u : α) (L : Nat) (h : us.length < L) :
    (us ++ List.replicate (L - us.length) z).set us.length u =
      (us ++ [u]) ++ List.replicate (L - (us ++ [u]).length) z := by
  obtain ⟨k, hk⟩ : ∃ k, L - us.length = k + 1 := ⟨L - us.length - 1, by omega⟩
  have hk' : L - (us ++ [u]).length = k := by simp; omega
  rw [hk, hk', List.replicate_succ]
  simp [List.set_append_right]

/-- What the visitor has collected: the values of the entries walked so far, each readable under
`H`, in a slice owned with its capacity. -/
private def collected (vsp : Loc) (H : IProp GF) (vis : List backend.Ent) : IProp GF :=
  iprop(∃ (sl : GoSlice) (ss : List GoSlice), vsp ↦ sl ∗ sl ↦* ss ∗
    ownSliceCap GoSlice sl (DFrac.own 1) ∗ ⌜ss.length = vis.length⌝ ∗
    [∗list] x ∈ ss.zip vis, schema.rdCap H x.1 x.2.2)

theorem schema.unsafeGetAllUsers.wp_proof
    (hUnm : proto.UnmarshalUser.spec (GF := GF) (hG := hG)) :
    schema.unsafeGetAllUsers.spec (GF := GF) (hG := hG) := by
  intro lg r H D hwf
  wp_start as ⟨#Hrd, HH⟩
  ihave Hsi : (schema.schemaInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hsi with ⟨-, -, -, -, -, -, -, -, ⟨%ub, #HUsers, -⟩, -⟩
  iunfold schema.authReader at Hrd
  icases Hrd with ⟨-, -, -, #HFE⟩
  iunfold schema.authForEachSpec at HFE
  wp_auto
  wp_apply HFE $$ %ub %_ %(collected vs_ptr H) [$HUsers $HH vs] as %err ⟨%Herr, HH, %es, %Hes, Hc⟩
  · isplitl [vs]
    · iunfold collected
      iexists slice.nil, []
      iframe vs
      isplitl []
      · iapply (ownSlice_nil (V := GoSlice) (DFrac.own 1))
      isplitl []
      · iapply (ownSliceCap_nil (V := GoSlice))
      isplitl []
      · ipureintro; rfl
      · simp only [List.zip_nil_left]; iapply BigSepL.bigSepL_nil.2; itrivial
    iintro !> %vis %e %k %v
    iclear HFE
    wp_start as ⟨Hc, #Hrc⟩
    iunfold collected at Hc
    icases Hc with ⟨%sl, %ss, Hvs, Hsl, Hcap, %Hlen, #Hss⟩
    wp_auto
    wp_apply wp_slice_literal (V := GoSlice) [v]
    isplitr
    · ipureintro; rfl
    iintro %lit ⟨Hlit, -⟩
    wp_apply wp_slice_append sl _ _ _ _ $$ [$Hsl $Hcap $Hlit] as %sl' ⟨Hsl, Hcap, -⟩
    (try wp_auto)
    iapply HΦ
    iunfold collected
    iexists sl', ss ++ [v]
    iframe Hvs Hsl Hcap
    isplitl []
    · ipureintro; simp [Hlen]
    rw [List.zip_append Hlen]
    simp only [List.zip_cons_cons, List.zip_nil_left]
    iapply BigSepL.bigSepL_snoc.2
    isplitl []
    · iexact Hss
    · iexact Hrc
  subst Herr
  iunfold collected at Hc
  icases Hc with ⟨%sl, %ss, Hvs, Hsl, Hcap, %Hlen, #Hss⟩
  wp_auto
  iclear HFE
  ihave %Hsll := ownSlice_len $$ Hsl
  wp_if_destruct
  · have hss : ss = [] := List.eq_nil_of_length_eq_zero (by rw [Hsll.1]; word)
    have hes : es = [] := List.eq_nil_of_length_eq_zero (by rw [← Hlen, hss]; rfl)
    subst hes
    (try wp_auto)
    iapply HΦ
    iframe HH
    iunfold schema.usersOutD
    iexists [], []
    isplitl []
    · iapply (ownSlice_nil (V := Loc) (DFrac.own 1))
    isplitl []
    · ipureintro; exact ⟨Hes, rfl⟩
    simp only [List.zip_nil_left]; iapply BigSepL.bigSepL_nil.2; itrivial
  wp_apply (wp_slice_make2 (V := Loc)) as %usl ⟨Husl, -⟩
  · ipureintro; word
  (try wp_auto)
  rename_i gi_ptr
  irename : (gi_ptr ↦ zero_val w64 : IProp GF) => gi
  ihave IH : iprop(∃ (n kv : w64) (us : List Loc),
      "i" ∷ i_ptr ↦ n ∗ "gi" ∷ gi_ptr ↦ kv ∗ "users" ∷ users_ptr ↦ usl ∗
      "Husl" ∷ usl ↦* (us ++ List.replicate (sint.nat sl.len - us.length) (zero_val Loc)) ∗
      "HH" ∷ H ∗ "Hvs" ∷ vs_ptr ↦ sl ∗ "Hsl" ∷ sl ↦* ss ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ sint.Z sl.len ∧ us.length = sint.nat n⌝ ∗
      "Hus" ∷ [∗list] x ∈ us.zip es, ∃ ur : auth.UserRec, ⌜x.2.2 = auth.userEncode ur⌝ ∗
        auth.ownUser x.1 ur) $$ [i gi users Husl HH Hvs Hsl]
  · iexists (W64 0), (W64 0), []
    iframe
    isplitl []
    · ipureintro; exact ⟨by word, by word, rfl⟩
    simp only [List.zip_nil_left]; iapply BigSepL.bigSepL_nil.2; itrivial
  wp_for IH
  wp_if_destruct
  · have Hlt : (sint.Z n).toNat < ss.length := by rw [Hsll.1]; word
    obtain ⟨sv, Hsv⟩ : ∃ sv, ss[(sint.Z n).toNat]? = some sv :=
      ⟨_, List.getElem?_eq_getElem Hlt⟩
    simp only [show 0 ≤ sint.Z n ∧ sint.Z n < sint.Z sl.len from ⟨Hn.1, Hif⟩]
    wp_apply wp_load_slice_index sl (sint.Z n) ss (DFrac.own 1) sv Hn.1 $$ [Hsl] as Hsl
    · iframe; ipureintro; exact Hsv
    have Hlte : (sint.Z n).toNat < es.length := by rw [← Hlen]; exact Hlt
    obtain ⟨e, He⟩ : ∃ e, es[(sint.Z n).toNat]? = some e :=
      ⟨_, List.getElem?_eq_getElem Hlte⟩
    have Hz : (ss.zip es)[(sint.Z n).toNat]? = some (sv, e) := by
      rw [List.getElem?_zip_eq_some]; exact ⟨Hsv, He⟩
    ihave #Hrc := BigSepL.bigSepL_lookup (Φ := fun _ x => schema.rdCap H x.1 x.2.2) Hz $$ Hss
    obtain ⟨ur, Hur⟩ := hwf e.1 e.2
      (bktEnts_lookup' (Hes.mem_iff.1 (List.mem_of_getElem? He)))
    simp only [show 0 ≤ sint.Z n ∧ sint.Z n < sint.Z sl.len from ⟨Hn.1, Hif⟩]
    wp_apply wp_load_slice_index sl (sint.Z n) ss (DFrac.own 1) sv Hn.1 $$ [Hsl] as Hsl
    · iframe; ipureintro; exact Hsv
    iunfold schema.rdCap at Hrc
    icases Hrc $$ HH with ⟨%dq, Hs, Hback⟩
    rw [Hur]
    wp_apply (hUnm sv ur _ _ dq) $$ [$Hs $«$r0»] as ⟨Hs, Hu⟩
    ihave HH := Hback $$ Hs
    imod (auth.ownUserX_persist _ _) $$ Hu with Hu
    ihave %Husll := ownSlice_len $$ Husl
    have Hul : sint.Z usl.len = sint.Z sl.len := by
      simp only [List.length_append, List.length_replicate] at Husll
      have : us.length + (sint.nat sl.len - us.length) = sint.nat sl.len := by word
      word
    simp only [show 0 ≤ sint.Z n ∧ sint.Z n < sint.Z usl.len from ⟨Hn.1, by rw [Hul]; exact Hif⟩]
    wp_apply wp_store_slice_index usl (sint.Z n) _ _ $$ [Husl] as Husl
    · iframe; ipureintro; simp; word
    wp_for_post
    iframe
    iexists _, _, us ++ [«$r0_ptr»]
    iframe
    have Hnu : (sint.Z n).toNat = us.length := by word
    rw [Hnu, set_fill' us _ _ _ (by word)]
    iframe Husl
    isplitl []
    · ipureintro; refine ⟨by word, by word, ?_⟩; simp; word
    rw [Hnu] at He
    rw [zip_snoc' us es _ e He]
    iapply BigSepL.bigSepL_snoc.2
    iframe Hus
    iexists ur
    iframe Hu
    ipureintro; exact Hur
  · have Hul : us.length = es.length := by rw [← Hlen, Hsll.1]; word
    rw [show sint.nat sl.len - us.length = 0 by word, List.replicate_zero, List.append_nil]
    (try wp_auto)
    iapply HΦ
    iframe HH
    iunfold schema.usersOutD
    iexists us, es
    iframe Husl Hus
    ipureintro; exact ⟨Hes, Hul⟩

end proof

end EtcdGrove
end Perennial
