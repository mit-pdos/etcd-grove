/-
`db.metasZero(size)` in `Open`'s owned phase (U11, `notes/bbolt-proof-plan.md`; the fork's
crash-safe `init`): whether every byte the file holds of its two meta pages is zero.
-/
module

public import Proof.go_etcd_io.bbolt.Open.ReadHeld
public import Proof.go_etcd_io.bbolt.Inv.Locks
public import Proof.go_etcd_io.bbolt.PkgInit
public import Perennial.Proof.io

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [ExtSemantics fsExt] [FsSemOk] [hos : HasExt fsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- **`db.metasZero(size)`**, `size` the file's size (`Stat`'s), the file's bytes `xs` held from
offset 0: whether its first `min(size, 8192)` bytes are all zero, or a read error (`fmt` formats
it). -/
abbrev DB.metasZero.spec_own : Prop :=
  ∀ (db f : Loc) (fd : w64) (p : GoString) (dqdb dqf dq dqb : DFrac) (d : OsFd)
    (xs : List ByteG),
  d.readable = true → d.path = p → xs.length < 2 ^ 62 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ osInv (GF := GF) ∗
      db.[DB, go!"file"] ↦{dqdb} f ∗ db.[DB, go!"pageSize"] ↦{dqdb} W64 4096 ∗
      fileOwn f fd p dqf ∗ osFd fd dq d ∗ osBytes p.ino 0 dqb xs }}
    (App (Val (db @!! go.GoType.PointerType DB.ty @!! go!"metasZero"))
      (Val #(W64 (xs.length : Int))))
  {{ (z : Bool) (err : GoInterface), RET (PairV #z #err);
      db.[DB, go!"file"] ↦{dqdb} f ∗ db.[DB, go!"pageSize"] ↦{dqdb} W64 4096 ∗
      fileOwn f fd p dqf ∗ osFd fd dq d ∗ osBytes p.ino 0 dqb xs ∗
      ((⌜err = interface.nil ∧ (z = true ↔ ∀ b ∈ (xs.map Prod.fst).take 8192, b = W8 0)⌝) ∨
       (⌜err ≠ interface.nil⌝ ∗ fmtErrorOk err)) }}

theorem DB.metasZero.wp_proof_own
    (hRead : os.File.ReadAt.specRacyLt (GF := GF) (hG := hG)) :
    DB.metasZero.spec_own (GF := GF) (hG := hG) := by
  intro db f fd p dqdb dqf dq dqb d xs hrd hp hx
  subst hp
  wp_start as ⟨#Hos, Hf, Hps, Hfo, Hfd, Hb⟩
  ihave #Hio : (isPkgInit (PROP := IProp GF) pkg_id.io) $$ []
  · iPkgInit
  ihave #Hn := io.eof_of_init $$ Hio
  isimp only [_root_.Perennial.errors.newVar] at Hn
  icases Hn with ⟨%eofl, #Heof, -⟩
  wp_auto
  rw [show W64 4096 * W64 2 = W64 8192 from rfl]
  have hN : ((min xs.length 8192 : Nat) : Int) < 2 ^ 31 := by omega
  wp_if_destruct
  all_goals
    try wp_auto
  all_goals first
    | (have hlt : xs.length < 8192 := by
        have := Hif; rw [show sint.Z (W64 8192) = 8192 from rfl] at this; word
       rw [show (W64 (xs.length : Int)) = W64 ((min xs.length 8192 : Nat) : Int) by
         rw [show min xs.length 8192 = xs.length by omega]]
       clear hlt)
    | (have hlt : ¬ xs.length < 8192 := by
        have := Hif; rw [show sint.Z (W64 8192) = 8192 from rfl] at this; word
       rw [show (W64 8192) = W64 ((min xs.length 8192 : Nat) : Int) by
         rw [show min xs.length 8192 = 8192 by omega]; rfl]
       clear hlt)
  all_goals
    clear Hif
    have hNl : min xs.length 8192 ≤ xs.length := Nat.min_le_left _ _
    have hN8 : min xs.length 8192 ≤ 8192 := Nat.min_le_right _ _
    have htk : List.take 8192 (List.map Prod.fst xs) =
        List.take (min xs.length 8192) (List.map Prod.fst xs) := by
      rw [List.take_eq_take_iff]; simp; omega
    rw [htk]
    generalize min xs.length 8192 = N at hNl hN8 ⊢
    wp_apply wp_slice_make2 (V := w8) (W64 (N : Int)) as %sl ⟨Hsl, -⟩
    · ipureintro; word
    have hsn : sint.nat (W64 (N : Int)) = N := by word
    rw [hsn]
    try wp_auto
    wp_apply os.File.ReadAt.wp_held hRead f fd d.path dqf sl (List.replicate N (W8 0)) (W64 0) dq dqb
      d xs _ hrd (by decide) (by rw [List.length_replicate]; omega)
      (by rw [List.length_replicate, show (W64 0).toNat = 0 from rfl]; omega) (by omega)
      $$ [Hfo Hsl Hfd Hb] as %n %err ⟨Hfo, Hfd, Hb, %vs', Hsl, %hr, #Hek⟩
    · iframe; iframe #; rw [← fileOwn_eq]; iexact Hfo
    rw [List.length_replicate, show (W64 0).toNat = 0 from rfl, List.drop_zero] at hr
    rcases hr with ⟨rfl, rfl, rfl⟩ | ⟨pe, rfl⟩
    · wp_auto
      have hBl : (List.take N (List.map Prod.fst xs)).length = N := by simp; omega
      generalize hB : List.take N (List.map Prod.fst xs) = B at hBl ⊢
      ihave %Hsll := ownSlice_len _ _ _ $$ Hsl
      ihave IH : (∃ (k : Nat) (cv : w8), "i" ∷ i_ptr ↦ W64 (k : Int) ∗ "c" ∷ c_ptr ↦ cv ∗
          "%Hk" ∷ ⌜k ≤ N ∧ ∀ j, j < k → B[j]? = some (W8 0)⌝ ∗ "Hsl" ∷ sl ↦* B : IProp GF)
        $$ [i c Hsl]
      · iexists 0, zero_val w8
        simp only [named]
        iframe
        ipureintro; exact ⟨Nat.zero_le _, fun j h => absurd h (Nat.not_lt_zero _)⟩
      wp_for IH
      have hsl : sint.Z sl.len = (N : Int) := by
        have := Hsll.1; rw [hBl] at this; have := Hsll.2; word
      have hkZ : sint.Z (W64 (k : Int)) = (k : Int) := by word
      rw [hsl, hkZ]
      by_cases hlt : (k : Int) < N
      · simp only [hlt, _root_.decide_true, ↓reduceIte]
        wp_auto
        rw [hkZ, hsl, ite_eq_left_of_eq_true _ _ (eq_true ⟨by omega, hlt⟩)]
        obtain ⟨bk, hbk⟩ : ∃ bk, B[k]? = some bk :=
          ⟨B[k]'(by omega), List.getElem?_eq_getElem (by omega)⟩
        icases ownSlice_elem_acc (k : Int) bk sl _ B (by omega) (by simpa using hbk) $$ Hsl
          with ⟨He, Hsl⟩
        wp_auto
        ihave Hsl := Hsl $$ He
        rw [show (k : Int).toNat = k from rfl, list_set_lookup_self B k bk hbk]
        by_cases hz : bk = W8 0
        · subst hz
          wp_auto
          wp_for_post
          iframe
          iexists k + 1, W8 0
          simp only [named]
          rw [show W64 ((k + 1 : Nat) : Int) = W64 (k : Int) + W64 1 by word]
          iframe
          ipureintro
          refine ⟨by omega, fun j hj => ?_⟩
          rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h | h
          · exact Hk.2 j h
          · subst h; exact hbk
        · rw [decide_eq_false hz]
          wp_auto
          iapply wp_for_post_return
          wp_auto
          iapply HΦ
          rw [fileOwn_eq]
          iframe
          ileft
          ipureintro
          exact ⟨rfl, ⟨fun h => (nomatch h),
            fun h => absurd (h bk (List.mem_of_getElem? hbk)) hz⟩⟩
      · simp only [hlt, _root_.decide_false, intoVal_eq_iff, Bool.false_eq_true, ↓reduceIte,
          decide_eq_true_eq]
        wp_auto
        iapply HΦ
        rw [fileOwn_eq]
        iframe
        ileft
        ipureintro
        refine ⟨rfl, ⟨fun _ b hb => ?_, fun _ => rfl⟩⟩
        obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hb
        have := Hk.2 j (by omega)
        rw [List.getElem?_eq_getElem hj] at this
        exact Option.some.inj this
    · wp_auto
      iapply HΦ
      rw [fileOwn_eq]
      iframe
      iright
      isplitr
      · ipureintro; intro h; cases h
      · iapply fmtErrorOkOrNil_ne (interface.mkOk (go.GoType.PointerType io.fs.PathError.ty) #pe)
          (by intro h; cases h) $$ Hek

end spec

end bbolt
end EtcdGrove
end Perennial
