/-
`uuid.New()` returns some `UUID` (`github_com.google.uuid.New.spec`, `Dsverify/Proof/github_com/
imdea_software/swiftpaxos/lib/LibSpecs.lean`), **proved** from uuid's translation (its model
`models/uuid`, dsv-retire-2, #49 step 2): `New` is `Must(NewRandom())`, and the model's `NewRandom`
fills a local `[16]byte` with two `primitive.RandomUint64()` big-endian (`binary.BigEndian.PutUint64`
on `uuid[0:8]` and `uuid[8:16]`), sets the version and variant bits and returns it with a `nil` error,
so `Must` returns it. The model's premise (`models/uuid/doc.go`, `Base.lean`): the program never
assigns `crypto/rand.Reader` and is not built with boringcrypto, so v1.3.1's `io.ReadFull` of 16
bytes cannot fail. A trust-boundary axiom from dsv-fix4 (mit-pdos/etcd-grove#49 fix 4) until
dsv-retire-2; the spec gained `[github_com.google.uuid.Assumptions]` then (ledger
`notes/specs-only/ledger.md`, 2026-11-25). Review of the axiom: `notes/axiom-review/dsv-fix4/google-uuid.md`.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.lib.LibSpecs
public import Dsverify.Proof.github_com.google.uuid.Base
public import Perennial.Proof.encoding.binary.Results
public import Perennial.Proof.github_com.goose_lang.primitive.Link
public import Perennial.Proof.crypto.sha1.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp

section proof
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [package_sem : github_com.google.uuid.Assumptions]

/-- `PutUint64(a[k:k+8], v)` on a `[16]byte` array `a` (`k` is 0 or 8): the array keeps its length. -/
theorem github_com.google.uuid.put64_at (a : Loc) (k : Nat) (hk : k + 8 ≤ 16) (vs : List w8)
    (hvs : vs.length = 16) (v : w64) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.encoding.binary ∗
        (a ↦ (array.mk 16 vs : GoArray w8 16) : IProp GF) }}
      (App (App (Val ((globalAddr encoding.binary.BigEndian) @!!
          go.GoType.PointerType encoding.binary.bigEndian.ty @!! go!"PutUint64"))
        (Val #(slice.mk (arrayIndexRef w8 (sint.Z (W64 (k : Int))) a) (W64 ((k : Int) + 8) - W64 (k : Int))
          (W64 16 - W64 (k : Int))))) (Val #v))
    {{ RET #(); ∃ vs' : List w8, a ↦ (array.mk 16 vs' : GoArray w8 16) ∗ ⌜vs'.length = 16⌝ }} := by
  iintro %Φ ⟨#Hbin, Ha⟩ HΦ
  have hkZ : sint.Z (W64 (k : Int)) = (k : Int) := by word
  have hkn : sint.nat (W64 (k : Int)) = k := by word
  have hsplit := array_split (V := w8) (GF := GF) (W64 (k : Int)) a (DFrac.own 1) 16
    (array.mk 16 vs) ⟨by omega, by omega⟩
  icases hsplit.1 $$ Ha with ⟨Ha1, Ha2⟩
  ihave %Hnn2 := typedPointsto_not_null _ _ _ $$ Ha2
  have e8 : W64 ((k : Int) + 8) - W64 (k : Int) = W64 8 := by word
  have hc : (8 : Int) ≤ sint.Z (W64 16 - W64 (k : Int)) := by word
  -- the slice `a[k:k+8]` is the first 8 bytes of the array's tail
  have h8n : sint.nat (W64 8) = 8 := rfl
  have hsplit2 := array_split (V := w8) (GF := GF) (W64 8) (arrayIndexRef w8 (sint.Z (W64 (k : Int))) a)
    (DFrac.own 1) (16 - sint.Z (W64 (k : Int))) (array.mk _ (vs.drop k)) ⟨by word, by word⟩
  rw [hkn]
  rw [h8n] at hsplit2
  icases hsplit2.1 $$ Ha2 with ⟨Hs, Ha3⟩
  ihave %Hnns := typedPointsto_not_null _ _ _ $$ Hs
  ihave Hs := crypto.sha1.slice_of_array_int _ 8 ⟨by omega, by omega⟩ _ _ (W64 16 - W64 (k : Int)) hc $$ [Hs]
  · iexact Hs
  rw [e8]
  wp_apply (encoding.binary.wp_BigEndian_PutUint64 _ ((vs.drop k).take 8) [] v
    (by simp; omega)) $$ [Hs] as Hs
  · rw [List.append_nil]; iexact Hs
  ihave Hs := crypto.sha1.array_of_slice_int _ 8 ⟨by omega, by omega⟩ _ _ _ Hnns $$ [Hs]
  · rw [List.append_nil]; iexact Hs
  have j2 := crypto.sha1.array_join (GF := GF) (arrayIndexRef w8 (sint.Z (W64 (k : Int))) a) (W64 8)
    (16 - sint.Z (W64 (k : Int))) (u64Le v).reverse ((vs.drop k).drop 8)
    (DFrac.own 1) ⟨by word, by word⟩ (by rw [List.length_reverse, u64Le_length, h8n])
  ihave Ha2 := j2 $$ [Hs Ha3]
  · iframe
  have j1 := crypto.sha1.array_join (GF := GF) a (W64 (k : Int)) 16 (vs.take k)
    ((u64Le v).reverse ++ (vs.drop k).drop 8) (DFrac.own 1)
    ⟨by omega, by omega⟩ (by rw [List.length_take, hkn]; omega)
  ihave Ha := j1 $$ [Ha1 Ha2]
  · iframe
  iapply HΦ
  iexists _
  iframe Ha
  ipureintro
  simp only [List.length_append, List.length_take, List.length_reverse, u64Le_length,
    List.length_drop, hvs]
  omega

/-- `put64_at` at the slice bounds as the code writes them (`uuid[0:8]`, `uuid[8:16]`). -/
theorem github_com.google.uuid.put64_at_w (a : Loc) (k hi : w64) (hk : 0 ≤ sint.Z k ∧ sint.Z k + 8 ≤ 16)
    (hhi : sint.Z hi = sint.Z k + 8) (vs : List w8) (hvs : vs.length = 16) (v : w64) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.encoding.binary ∗
        (a ↦ (array.mk 16 vs : GoArray w8 16) : IProp GF) }}
      (App (App (Val ((globalAddr encoding.binary.BigEndian) @!!
          go.GoType.PointerType encoding.binary.bigEndian.ty @!! go!"PutUint64"))
        (Val #(slice.mk (arrayIndexRef w8 (sint.Z k) a) (hi - k) (W64 16 - k)))) (Val #v))
    {{ RET #(); ∃ vs' : List w8, a ↦ (array.mk 16 vs' : GoArray w8 16) ∗ ⌜vs'.length = 16⌝ }} := by
  obtain ⟨n, rfl, hn8⟩ : ∃ n : Nat, k = W64 (n : Int) ∧ n ≤ 8 := ⟨sint.nat k, by word, by word⟩
  have hn : n + 8 ≤ 16 := by omega
  obtain rfl : hi = W64 ((n : Int) + 8) := by word
  exact github_com.google.uuid.put64_at a n hn vs hvs v

/-- A byte load from a `[16]byte` array, at an index in range. -/
theorem github_com.google.uuid.load_byte (a : Loc) (vs : List w8) (hvs : vs.length = 16) (i : w64)
    (hi : 0 ≤ sint.Z i ∧ sint.Z i < 16) :
    {{ (a ↦ (array.mk 16 vs : GoArray w8 16) : IProp GF) }}
      (App (Val (GoInstruction (GoLoad go.byte))) (Val #(arrayIndexRef w8 (sint.Z i) a)))
    {{ (b : w8), RET #b; a ↦ (array.mk 16 vs : GoArray w8 16) }} := by
  have hlt : (sint.Z i).toNat < vs.length := by omega
  iintro %Φ Ha HΦ
  iapply (crypto.sha1.wp_load_array_elem_int a 16 vs (sint.Z i) (vs[(sint.Z i).toNat]'hlt) hi.1
    (List.getElem?_eq_getElem hlt)) $$ [Ha]
  · iexact Ha
  iintro !> Ha
  iapply HΦ $$ Ha

/-- A byte store into a `[16]byte` array, at an index in range: the array keeps its length. -/
theorem github_com.google.uuid.store_byte (a : Loc) (vs : List w8) (hvs : vs.length = 16) (i : w64)
    (hi : 0 ≤ sint.Z i ∧ sint.Z i < 16) (b : w8) :
    {{ (a ↦ (array.mk 16 vs : GoArray w8 16) : IProp GF) }}
      (App (Val (GoInstruction (GoStore go.byte))) (Val (PairV #(arrayIndexRef w8 (sint.Z i) a) #b)))
    {{ RET #(); ∃ vs' : List w8, a ↦ (array.mk 16 vs' : GoArray w8 16) ∗ ⌜vs'.length = 16⌝ }} := by
  iintro %Φ Ha HΦ
  iapply (crypto.sha1.wp_store_array_elem_int a 16 vs (sint.Z i) ⟨hi.1, by omega⟩ b) $$ [Ha]
  · iexact Ha
  iintro !> Ha
  iapply HΦ
  iexists _
  iframe Ha
  ipureintro
  rw [List.length_set]; exact hvs

/-- The model's `NewRandom()`: some `UUID`, with a `nil` error. -/
theorem github_com.google.uuid.NewRandom.wp_spec :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.google.uuid }}
      (App (Val (@! github_com.google.uuid.NewRandom)) (Val #()))
    {{ (u : github_com.google.uuid.UUID), RET (PairV #u #(interface.nil : GoInterface)); True }} := by
  wp_start as #Hpkg
  ihave #Hbin : isPkgInit (PROP := IProp GF) pkg_id.encoding.binary $$ []
  · iPkgInit
  wp_auto
  wp_apply github_com.goose_lang.primitive.wp_RandomUint64 as %x1 -
  try wp_auto
  have hz16 : (_root_.Perennial.zero_val (GoArray w8 16)) = array.mk 16 (List.replicate 16 (W8 0)) := rfl
  rw [hz16]
  wp_apply (github_com.google.uuid.put64_at_w uuid_ptr (W64 0) (W64 8) ⟨by decide, by decide⟩ (by decide)
    (List.replicate 16 (W8 0)) (by simp) x1) $$ [uuid]
    as ⟨%vs1, uuid, %Hvs1⟩
  · iexact uuid
  try wp_auto
  wp_apply github_com.goose_lang.primitive.wp_RandomUint64 as %x2 -
  try wp_auto
  wp_apply (github_com.google.uuid.put64_at_w uuid_ptr (W64 8) (W64 16) ⟨by decide, by decide⟩ (by decide)
    vs1 Hvs1 x2) $$ [uuid]
    as ⟨%vs2, uuid, %Hvs2⟩
  · iexact uuid
  try wp_auto
  wp_apply (github_com.google.uuid.load_byte uuid_ptr vs2 Hvs2 (W64 6) ⟨by decide, by decide⟩) $$ [uuid]
    as %b6 uuid
  · iexact uuid
  try wp_auto
  wp_apply (github_com.google.uuid.store_byte uuid_ptr vs2 Hvs2 (W64 6) ⟨by decide, by decide⟩) $$ [uuid]
    as ⟨%vs3, uuid, %Hvs3⟩
  · iexact uuid
  try wp_auto
  wp_apply (github_com.google.uuid.load_byte uuid_ptr vs3 Hvs3 (W64 8) ⟨by decide, by decide⟩) $$ [uuid]
    as %b8 uuid
  · iexact uuid
  try wp_auto
  wp_apply (github_com.google.uuid.store_byte uuid_ptr vs3 Hvs3 (W64 8) ⟨by decide, by decide⟩) $$ [uuid]
    as ⟨%vs4, uuid, %Hvs4⟩
  · iexact uuid
  try wp_auto
  iapply HΦ
  itrivial

/-- `Must(u, nil)` returns `u`. -/
theorem github_com.google.uuid.Must.wp_spec_nil (u : github_com.google.uuid.UUID) :
    {{ (True : IProp GF) }}
      (App (App (Val (@! github_com.google.uuid.Must)) (Val #u)) (Val #(interface.nil : GoInterface)))
    {{ RET #u; True }} := by
  wp_start
  wp_auto
  iapply HΦ
  itrivial

/-- `New()`: some `UUID` (the file header). -/
theorem github_com.google.uuid.New.wp_proof : github_com.google.uuid.New.spec (GF := GF) := by
  wp_start as #Hpkg
  wp_auto
  wp_apply github_com.google.uuid.NewRandom.wp_spec as %u -
  try wp_auto
  wp_apply github_com.google.uuid.Must.wp_spec_nil
  try wp_auto
  iapply HΦ
  itrivial

end proof

end Perennial
