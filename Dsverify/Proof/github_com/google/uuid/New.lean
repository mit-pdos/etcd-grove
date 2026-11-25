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
  have hsplit2 := array_split (V := w8) (GF := GF) (W64 8) (arrayIndexRef w8 (sint.Z (W64 (k : Int))) a)
    (DFrac.own 1) (16 - sint.Z (W64 (k : Int))) (array.mk _ (vs.drop k)) ⟨by word, by word⟩
  rw [hkn] at Ha2
  icases hsplit2.1 $$ Ha2 with ⟨Hs, Ha3⟩
  ihave %Hnns := typedPointsto_not_null _ _ _ $$ Hs
  ihave Hs := crypto.sha1.slice_of_array_int _ 8 ⟨by omega, by omega⟩ _ _ (W64 16 - W64 (k : Int)) hc $$ [Hs]
  · simp only [show sint.Z (W64 8) = 8 by rfl]
    iexact Hs
  rw [e8]
  wp_apply (encoding.binary.wp_BigEndian_PutUint64 _ ((vs.drop k).take (sint.nat (W64 8))) [] v
    (by simp [show sint.nat (W64 8) = 8 by rfl]; omega)) $$ [Hs] as Hs
  · iframe Hbin; rw [List.append_nil]; iexact Hs
  ihave Hs := crypto.sha1.array_of_slice_int _ 8 ⟨by omega, by omega⟩ _ _ _ Hnns $$ [Hs]
  · rw [List.append_nil]; iexact Hs
  have j2 := crypto.sha1.array_join (GF := GF) (arrayIndexRef w8 (sint.Z (W64 (k : Int))) a) (W64 8)
    (16 - sint.Z (W64 (k : Int))) (encoding.binary.u64Le v).reverse ((vs.drop k).drop (sint.nat (W64 8)))
    (DFrac.own 1) ⟨by word, by word⟩ (by simp [encoding.binary.u64Le]; rfl)
  ihave Ha2 := j2 $$ [Hs Ha3]
  · iframe
  have j1 := crypto.sha1.array_join (GF := GF) a (W64 (k : Int)) 16
    ((array.mk 16 vs : GoArray w8 16).arr.take (sint.nat (W64 (k : Int))))
    ((encoding.binary.u64Le v).reverse ++ (vs.drop k).drop (sint.nat (W64 8))) (DFrac.own 1)
    ⟨by omega, by omega⟩ (by simp only [List.length_take]; omega)
  ihave Ha := j1 $$ [Ha1 Ha2]
  · iframe
  iapply HΦ
  iexists _
  iframe Ha
  ipureintro
  simp [encoding.binary.u64Le, show sint.nat (W64 8) = 8 by rfl, hkn]
  omega

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
  wp_auto
  wp_apply (github_com.google.uuid.put64_at uuid_ptr 0 (by omega) _ (by simp) x1) $$ [uuid]
    as ⟨%vs1, uuid, %Hvs1⟩
  · iframe Hbin; iexact uuid
  wp_auto
  wp_apply github_com.goose_lang.primitive.wp_RandomUint64 as %x2 -
  wp_auto
  wp_apply (github_com.google.uuid.put64_at uuid_ptr 8 (by omega) vs1 Hvs1 x2) $$ [uuid]
    as ⟨%vs2, uuid, %Hvs2⟩
  · iframe Hbin; iexact uuid
  wp_auto
  obtain ⟨b6, hb6⟩ : ∃ b, vs2[(sint.Z (W64 6)).toNat]? = some b :=
    ⟨vs2[6]'(by omega), by simp [show (sint.Z (W64 6)).toNat = 6 by rfl]⟩
  wp_apply (crypto.sha1.wp_load_array_elem_int uuid_ptr 16 vs2 (sint.Z (W64 6)) b6 (by decide) hb6)
    $$ [uuid] as uuid
  · iexact uuid
  wp_auto
  wp_apply (crypto.sha1.wp_store_array_elem_int uuid_ptr 16 vs2 (sint.Z (W64 6))
    ⟨by decide, by simp [show (sint.Z (W64 6)).toNat = 6 by rfl]; omega⟩ _) $$ [uuid] as uuid
  · iexact uuid
  wp_auto
  have Hvs3 : (vs2.set (sint.Z (W64 6)).toNat ((b6 &&& W8 15) ||| W8 64)).length = 16 := by
    simp [Hvs2]
  obtain ⟨b8, hb8⟩ : ∃ b, (vs2.set (sint.Z (W64 6)).toNat ((b6 &&& W8 15) ||| W8 64))[(sint.Z (W64 8)).toNat]?
      = some b :=
    ⟨_, (List.getElem?_eq_getElem (by rw [Hvs3]; decide))⟩
  wp_apply (crypto.sha1.wp_load_array_elem_int uuid_ptr 16 _ (sint.Z (W64 8)) b8 (by decide) hb8)
    $$ [uuid] as uuid
  · iexact uuid
  wp_auto
  wp_apply (crypto.sha1.wp_store_array_elem_int uuid_ptr 16 _ (sint.Z (W64 8))
    ⟨by decide, by rw [Hvs3]; decide⟩ _) $$ [uuid] as uuid
  · iexact uuid
  wp_auto
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
  wp_auto
  wp_apply github_com.google.uuid.Must.wp_spec_nil as -
  wp_auto
  iapply HΦ
  itrivial

end proof

end Perennial
