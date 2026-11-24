/-
The proof of `klog.serialize.FormatKVs.spec` (`Spec/k8s_io/klog/v2/internal/serialize/FormatKVs.lean`)
over the trusted model `FormatKVs.impl` (`TrustedCode/k8s_io/klog/v2/internal/serialize.lean`;
klog-infos, 2026-11-23, etcd-grove#25): the model reads every key and value (`model.checkAll`,
`model.checkKVs`), each `klog.infoSArgOk` (`model.kvOk` returns `true`), then writes an arbitrary
string through `bytes.Buffer.Write`. Lean-first.
-/
module

public import Spec.k8s_io.klog.v2.internal.serialize.FormatKVs
public import Perennial.Proof.bytes.Link
public import Perennial.Proof.arbitraryString

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.klog.v2.internal.serialize.Assumptions]
variable [time_sem : _root_.Perennial.time.Assumptions]
variable [schema_sem : k8s_io.apimachinery.pkg.runtime.schema.Assumptions]

open k8s_io.klog.v2.internal.serialize

theorem klog.serialize.groupResource_ty :
    model.GroupResource = k8s_io.apimachinery.pkg.runtime.schema.GroupResource.ty := by
  unfold model.GroupResource k8s_io.apimachinery.pkg.runtime.schema.GroupResource.ty; rfl

/-- The model's `kvOk x` returns `true` for a key or value `klog.infoSArgOk`. -/
theorem klog.serialize.wp_kvOk (x : GoInterface) (hx : klog.infoSArgOk x) :
    {{ (True : IProp GF) }} (App (Val model.kvOk) (Val #x)) {{ RET #true; True }} := by
  obtain ⟨⟨ty, v⟩, rfl, hty⟩ := hx
  iintro %Φ - HΦ
  unfold model.kvOk
  rw [klog.serialize.groupResource_ty]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hty
  rcases hty with rfl | rfl | rfl | rfl <;>
  · repeat (first | wp_auto | simp)
    iapply HΦ; itrivial

/-- The model's `checkKVs s`: reads every element of `s`, each `klog.infoSArgOk`, and returns. -/
theorem klog.serialize.wp_checkKVs :
    ⊢ ∀ (s : GoSlice) (xs : List GoInterface) (dq : DFrac) (Φ : val → IProp GF),
      ⌜∀ x ∈ xs, klog.infoSArgOk x⌝ -∗ (s ↦*{dq} xs : IProp GF) -∗
      (s ↦*{dq} xs -∗ Φ #()) -∗
      WP (App (Val model.checkKVs) (Val #s)) {{ Φ }} := by
  unfold model.checkKVs
  iloeb as IH
  iintro %s %xs %dq %Φ %hok Hs HΦ
  ihave %Hlen := ownSlice_len $$ Hs
  ihave %Hwf := ownSlice_wf s _ xs $$ Hs
  wp_pures
  wp_if_destruct
  · wp_pures
    rw [if_pos ⟨Int.le_refl _, by word⟩]
    obtain ⟨x, rest, rfl⟩ : ∃ x rest, xs = x :: rest := by
      cases xs with
      | nil => simp at Hlen; word
      | cons x rest => exact ⟨x, rest, rfl⟩
    rw [show sint.Z (W64 0) = 0 from rfl]
    wp_apply (wp_load_slice_index s 0 (x :: rest) dq x (by omega)) $$ [$Hs] as Hs
    · ipureintro; rfl
    wp_bind (App (Val model.kvOk) _)
    wp_apply klog.serialize.wp_kvOk x (hok x (List.mem_cons_self))
    wp_pures
    icases (ownSlice_split_all (W64 1) s _ _ ⟨by decide, by word⟩).1 $$ Hs with ⟨H0, Hrest⟩
    rw [show List.drop (sint.nat (W64 1)) (x :: rest) = rest from rfl]
    wp_pures
    rw [if_pos ⟨by decide, by word, Hwf.2⟩]
    iapply IH $$ %_ %_ %_ %_ %(fun y hy => hok y (List.mem_cons_of_mem _ hy)) Hrest
    iintro Hrest
    iapply HΦ
    iapply (ownSlice_split_all (W64 1) s _ (x :: rest) ⟨by decide, by word⟩).2
    iframe
  · iapply HΦ $$ Hs

/-- The model's `checkAll kvs`: `checkKVs` of every slice of `kvs`. -/
theorem klog.serialize.wp_checkAll :
    ⊢ ∀ (kvs : GoSlice) (sls : List GoSlice) (xss : List (List GoInterface)) (dq dq' : DFrac)
      (Φ : val → IProp GF),
      ⌜∀ xs ∈ xss, ∀ x ∈ xs, klog.infoSArgOk x⌝ -∗ (kvs ↦*{dq'} sls : IProp GF) -∗
      ([∗list] sl;xs ∈ sls;xss, sl ↦*{dq} xs) -∗
      (kvs ↦*{dq'} sls -∗ ([∗list] sl;xs ∈ sls;xss, sl ↦*{dq} xs) -∗ Φ #()) -∗
      WP (App (Val model.checkAll) (Val #kvs)) {{ Φ }} := by
  unfold model.checkAll
  iloeb as IH
  iintro %kvs %sls %xss %dq %dq' %Φ %hok Hkvs Hsls HΦ
  ihave %Hlen := ownSlice_len $$ Hkvs
  ihave %Hwf := ownSlice_wf kvs _ sls $$ Hkvs
  wp_pures
  wp_if_destruct
  · wp_pures
    rw [if_pos ⟨Int.le_refl _, by word⟩]
    obtain ⟨sl, srest, rfl⟩ : ∃ sl srest, sls = sl :: srest := by
      cases sls with
      | nil => simp at Hlen; word
      | cons sl srest => exact ⟨sl, srest, rfl⟩
    rw [show sint.Z (W64 0) = 0 from rfl]
    wp_apply (wp_load_slice_index kvs 0 (sl :: srest) dq' sl (by omega)) $$ [$Hkvs] as Hkvs
    · ipureintro; rfl
    icases (BigSepL2.bigSepL2_cons_inv_left).1 $$ Hsls with ⟨%xs, %xrest, %hx, Hsl, Hsls⟩
    subst hx
    wp_bind (App (Val model.checkKVs) _)
    iapply klog.serialize.wp_checkKVs $$ %_ %_ %_ %_ %(hok xs (List.mem_cons_self)) Hsl
    iintro Hsl
    wp_pures
    icases (ownSlice_split_all (W64 1) kvs _ _ ⟨by decide, by word⟩).1 $$ Hkvs with ⟨H0, Hrest⟩
    rw [show List.drop (sint.nat (W64 1)) (sl :: srest) = srest from rfl]
    wp_pures
    rw [if_pos ⟨by decide, by word, Hwf.2⟩]
    iapply IH $$ %_ %_ %xrest %_ %_ %_ %(fun ys hy => hok ys (List.mem_cons_of_mem _ hy)) Hrest Hsls
    iintro Hrest Hsls
    iapply HΦ $$ [H0 Hrest] [Hsl Hsls]
    · iapply (ownSlice_split_all (W64 1) kvs _ (sl :: srest) ⟨by decide, by word⟩).2
      iframe
    · iapply (BigSepL2.bigSepL2_cons).2
      iframe
  · iapply HΦ $$ Hkvs Hsls

theorem klog.serialize.FormatKVs.wp_proof : klog.serialize.FormatKVs.spec (GF := GF) (hG := hG) := by
  intro b bs kvs sls xss dq dq' hok
  wp_start as ⟨Hbuf, Hkvs, Hsls⟩
  wp_bind (App (Val model.checkAll) _)
  iapply klog.serialize.wp_checkAll $$ %_ %_ %_ %_ %_ %_ %hok Hkvs Hsls
  iintro Hkvs Hsls
  wp_pures
  wp_apply _root_.Perennial.fmt.wp_arbitraryString as %s -
  wp_apply wp_string_to_bytes as %sl ⟨Hs, -⟩
  wp_apply bytes.Buffer.wp_Write _ bs _ (DFrac.own 1) _ $$ [$Hbuf $Hs] as ⟨Hbuf, -⟩
  try wp_auto
  iapply HΦ
  iframe

end proof

end EtcdGrove
end Perennial
