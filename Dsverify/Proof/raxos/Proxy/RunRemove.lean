/-
Package `proxy`: `removeDecidedItemsFromFutureProposals` keeps some of `toBeProposed`'s ids
(each one of the old list's: their facts `idP` are kept).
-/
module

public import Dsverify.Proof.raxos.Proxy.RunSmrHelpers

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Perennial.raxos


open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net
open Perennial.raxos.pure Perennial.raxos.msg
open raxos.replica.src

section proofs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [π : NetProtoGS] [qv : hyp.QpVocab GF]
variable [raxos.replica.src.Assumptions] [raxos.proto.client.Assumptions]

attribute [local instance] HeapGS.goose_globalGS

instance rd_idP_persistent (γ : QNames) (γs : GName) (x : GoString) :
    Persistent (idP (GF := GF) γ γs x) := by
  unfold idP; infer_instance

/-- `toBeProposed` with its ids' facts. -/
def rd_tbP (γ : QNames) (γs : GName) (pr : Loc) : IProp GF :=
  iprop(∃ (tb : GoSlice) (tbs : List GoString), pr.[Proxy, go!"toBeProposed"] ↦ tb ∗ tb ↦* tbs ∗
    ownSliceCap GoString tb (DFrac.own 1) ∗ [∗list] x ∈ tbs, idP γ γs x)

theorem rd_wp_removeDecided (γ : QNames) (γs : GName) (pr : Loc) (asl : GoSlice) (xs : List GoString) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.raxos.replica.src ∗ rd_tbP γ γs pr ∗ asl ↦*□ xs }}
      (App (Val (pr @!! go.GoType.PointerType Proxy.ty @!! go!"removeDecidedItemsFromFutureProposals"))
        (Val #asl))
    {{ RET #(); rd_tbP γ γs pr }} := by
  wp_start as ⟨Htb, #Has⟩
  iunfold rd_tbP at Htb
  icases Htb with ⟨%tb, %tbs, Hf, Htb, Hcap, #Hids⟩
  wp_auto
  wp_apply (wp_map_make1 (K := GoString) (V := Bool) go.string go.bool) as %m Hm
  ihave %Hxl := ownSlice_len $$ Has
  ihave HI : (∃ (i : w64) (M : GMap GoString Bool) (e : GoString), "i" ∷ i_ptr ↦ i ∗ "Hm" ∷ m ↦$ M ∗
      "elem" ∷ elem_ptr ↦ e ∗ "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z asl.len⌝ : IProp GF)
    $$ [i Hm elem]
  · iexists W64 0, ∅, _; iframe; ipureintro; word
  wp_for HI
  wp_if_destruct
  · have Hlt : sint.nat i < xs.length := by word
    list_elem xs (sint.nat i) as x
    have Hb : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z asl.len := ⟨Hi.1, Hif⟩
    repeat' (first | wp_auto | simp only [Hb, _root_.and_self, ↓reduceIte])
    wp_apply wp_load_slice_index asl (sint.Z i) xs _ x Hi.1 $$ [Has] as -
    · iframe Has; ipureintro; simpa using Hx_lookup
    wp_apply wp_mapInsert $$ Hm as Hm
    wp_for_post
    iframe
    iexists i + W64 1, _, x
    iframe
    ipureintro; word
  ihave %Htl := ownSlice_len $$ Htb
  ihave HJ : (∃ (i j : w64) (cur : List GoString), "i" ∷ i_ptr ↦ i ∗ "j" ∷ j_ptr ↦ j ∗
      "Htb" ∷ tb ↦* cur ∗
      "%Hc" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z i ∧ sint.Z i ≤ sint.Z tb.len ∧
        cur.length = tbs.length ∧ ∀ x ∈ cur, x ∈ tbs⌝ : IProp GF) $$ [i j Htb]
  · iexists W64 0, W64 0, tbs; iframe; ipureintro
    exact ⟨by word, by word, by word, rfl, fun _ h => h⟩
  wp_for HJ
  wp_if_destruct
  · have Hlt : sint.nat i < cur.length := by word
    list_elem cur (sint.nat i) as x
    have Hb : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z tb.len := ⟨by word, Hif⟩
    repeat' (first | wp_auto | simp only [Hb, _root_.and_self, ↓reduceIte])
    wp_apply wp_load_slice_index tb (sint.Z i) cur _ x (by word) $$ [Htb] as Htb
    · iframe Htb; ipureintro; simpa using Hx_lookup
    wp_apply wp_map_lookup1 $$ Hm as Hm
    generalize (M !! x).getD (zero_val Bool) = bv
    cases bv
    · have Hbj : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z tb.len := ⟨Hc.1, by word⟩
      repeat' (first | wp_auto | simp only [Hb, Hbj, _root_.and_self, ↓reduceIte])
      wp_apply wp_load_slice_index tb (sint.Z i) cur _ x (by word) $$ [Htb] as Htb
      · iframe Htb; ipureintro; simpa using Hx_lookup
      repeat' (first | wp_auto | simp only [Hb, Hbj, _root_.and_self, ↓reduceIte])
      wp_apply wp_store_slice_index tb (sint.Z j) cur x $$ [Htb] as Htb
      · iframe Htb; ipureintro; word
      wp_for_post
      iframe
      iexists i + W64 1, j + W64 1, cur.set (sint.Z j).toNat x
      iframe
      ipureintro
      refine ⟨by word, by word, by word, by simp [Hc.2.2.2.1], ?_⟩
      intro y hy
      rcases List.mem_or_eq_of_mem_set hy with hy | hy
      · exact Hc.2.2.2.2 y hy
      · subst hy; exact Hc.2.2.2.2 _ (List.mem_of_getElem? Hx_lookup)
    · wp_auto
      wp_for_post
      iframe
      iexists i + W64 1, j, cur
      iframe
      ipureintro
      exact ⟨by word, by word, by word, Hc.2.2.2.1, Hc.2.2.2.2⟩
  · ihave %Hcw := ownSliceCap_wf $$ Hcap
    have Hb : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) ≤ sint.Z j ∧ sint.Z j ≤ sint.Z tb.cap :=
      ⟨by word, Hc.1, by word⟩
    simp only [Hb, _root_.and_self, ↓reduceIte]
    wp_auto
    icases (ownSlice_slice (W64 0) j tb _ cur ⟨by word, Hc.1, by word⟩).1 $$ Htb with ⟨-, Hj, Hrest⟩
    ihave Hcap := ownSlice_slice_absorb_capacity tb _ (W64 0) j ⟨by word, Hc.1, by word⟩ $$ [Hrest Hcap]
    · iframe
    iapply HΦ
    iunfold rd_tbP
    iexists _, _
    iframe Hf Hj Hcap
    iapply BigSepL.bigSepL_forall_elim
    iintro %k %y %Hk
    have hy : y ∈ tbs := by
      apply Hc.2.2.2.2 y
      have := List.mem_of_getElem? Hk
      simp only [subslice] at this
      exact List.mem_of_mem_take (List.mem_of_mem_drop this)
    iapply (BigSepL.bigSepL_mem (Φ := fun x => idP (GF := GF) γ γs x) hy) $$ Hids

end proofs

end Perennial.raxos
