/-
Proof of the spec of the same name (the auth plan's E2j, 2026-10-26). Lean-first (no Rocq
counterpart). The backend's `GetAllUsers` answers from the latest state; the loop copies each
message's name into the response, whose `Users` are then the state's users' names.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.auth.authStore__UserList
public import Proof.go_etcd_io.etcd.server.v3.auth.ReadsLemmas

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.auth auth go_etcd_io.etcd.api.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.auth.Assumptions]

theorem auth.authStore.UserList.wp_proof :
    auth.authStore.UserList.spec (GF := GF) (hG := hG) := by
  intro st R M P f T hs r
  wp_start as ⟨#Hinv, Hown, HWR⟩
  iunfold authWR at HWR
  icases HWR with ⟨⟨%be, Hbe, #Hbeok⟩, HT, Hen, Hca⟩
  ihave #Hbeok' := Hbeok
  iunfold authWBackendOk at Hbeok'
  icases Hbeok' with ⟨%bi, %Hbi, -, -, #HRds⟩
  iunfold authBackendReads at HRds
  icases HRds with ⟨-, -, #HGA, -⟩
  subst Hbi
  (try wp_auto)
  wp_bind (App (Val #(methods bi.ty go!"GetAllUsers" bi.v)) (Val #()))
  iapply HGA $$ %hs [$HT $Hown]
  inext
  iintro %s ⟨HT, Hown, %sta, %Hl, Hus⟩
  iunfold usersOut at Hus
  icases Hus with ⟨%us, %names, Hs, %Hn, Hmsgs⟩
  obtain ⟨Hlen, Hnd, Hmem⟩ := Hn
  ihave Hmsgs := usersOut_names sta (us.zip names)
    (fun x hx => (Hmem x.2).1 (List.of_mem_zip hx).2) $$ Hmsgs
  imod Hmsgs with #Hmsgs
  ihave %Hsl := ownSlice_len _ _ _ $$ Hs
  (try wp_auto)
  wp_apply (wp_slice_make2 (V := GoString) s.len) as %usl ⟨Husl, -⟩
  · ipureintro; word
  (try wp_auto)
  rename_i igo
  irename : (igo ↦ zero_val w64 : IProp GF) => Higo
  ihave IH : iprop(∃ (n k : w64),
      "i" ∷ i_ptr ↦ n ∗ "Higo" ∷ igo ↦ k ∗ "Hs" ∷ s ↦* us ∗
      "Husl" ∷ usl ↦* (names.take (sint.nat n) ++
        List.replicate (us.length - sint.nat n) (zero_val GoString)) ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.nat n ≤ us.length⌝) $$ [i Higo Hs Husl]
  · iexists W64 0, _
    simp only [show sint.nat (W64 0) = 0 from rfl, List.take_zero, List.nil_append, Nat.sub_zero,
      Hsl.1]
    iframe
    ipureintro
    refine ⟨by word, by word⟩
  wp_for IH
  wp_if_destruct
  · have Hlt : sint.nat n < us.length := by word
    obtain ⟨u, nm, Hu, Hnm, Hz⟩ := zip_lookup_names us names (sint.nat n) Hlen Hlt
    have Hbnd : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z s.len := ⟨Hn.1, Hif⟩
    simp only [Hbnd, and_self, ↓reduceIte]
    wp_apply wp_load_slice_index s (sint.Z n) us (DFrac.own 1) u Hn.1 $$ [Hs] as Hs
    · iframe; ipureintro; exact Hu
    (try wp_auto)
    simp only [Hbnd, and_self, ↓reduceIte]
    wp_apply wp_load_slice_index s (sint.Z n) us (DFrac.own 1) u Hn.1 $$ [Hs] as Hs
    · iframe; ipureintro; exact Hu
    ihave Hel := BigSepL.bigSepL_lookup (Φ := fun _ x => userNameAt (GF := GF) x.1 x.2) Hz $$ Hmsgs
    iunfold userNameAt at Hel
    icases Hel with ⟨%nms, #HName, #Hnms⟩
    (try wp_auto)
    wp_apply wp_bytes_to_string nms nm DFrac.discard $$ [Hnms] as -
    · iexact Hnms
    (try wp_auto)
    have h2 : (sint.nat n : Int) = sint.Z n := by word
    have Hset : 0 ≤ sint.Z n ∧ sint.Z n < ((names.take (sint.nat n) ++
        List.replicate (us.length - sint.nat n) (zero_val GoString)).length : Int) := by
      simp only [List.length_append, List.length_take, List.length_replicate]; rw [← Hlen]; omega
    ihave %Hul := ownSlice_len _ _ _ $$ Husl
    have Hbnd2 : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z usl.len := by
      obtain ⟨Hul1, Hul2⟩ := Hul
      simp only [List.length_append, List.length_take, List.length_replicate] at Hul1
      rw [← Hlen] at Hul1
      have : sint.nat n + (us.length - sint.nat n) = us.length := by omega
      constructor
      · exact Hn.1
      · have : (sint.nat usl.len : Int) = sint.Z usl.len := by word
        omega
    simp only [Hbnd2, and_self, ↓reduceIte]
    wp_apply wp_store_slice_index usl (sint.Z n) _ nm $$ [Husl] as Husl
    · iframe; ipureintro; exact Hset
    (try wp_auto)
    wp_for_post
    iframe
    iexists n + W64 1, n
    have hsucc : sint.nat (n + W64 1) = sint.nat n + 1 := by word
    rw [hsucc, Hlen]
    have := take_replicate_set names (sint.nat n) (zero_val GoString) nm Hnm
    rw [show (sint.Z n).toNat = sint.nat n from rfl, this]
    iframe
    ipureintro
    refine ⟨by word, by omega⟩
  -- the loop is done: every name copied
  have Hdone : sint.nat n = us.length := by word
  (try wp_auto)
  iapply HΦ
  iframe Hown
  isplitl [Hbe HT Hen Hca]
  · iunfold authWR; iframe HT Hen Hca; iexists (GoInterface.ok bi); iframe Hbe Hbeok
  iexists sta
  isplitr
  · ipureintro; exact Hl
  iunfold userListOut
  isplitr
  · ipureintro; rfl
  iexists _, names
  iframe
  rw [Hdone, Hlen, List.take_length, Nat.sub_self, List.replicate_zero, List.append_nil]
  iframe
  ipureintro
  exact ⟨Hnd, fun n => Hmem n⟩

end proof

end EtcdGrove
end Perennial
