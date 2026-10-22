/-
Lean-first (no Rocq counterpart).

The proof of `storage.PrepareKey`: its four tests, in order, as `prepareKeyM`'s.
-/
module

public import Spec.k8s_io.apiserver.pkg.storage.PrepareKey
public import Spec.strings.HasSuffix
public import Spec.strings.Contains
public import Spec.fmt.Errorf
public import Perennial.Spec.strings.HasPrefix

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

/-- A string argument of `fmt.Errorf` (`%q`) is well formed. -/
theorem argWf_string [FfiSyntax] [GoGlobalContext] (x : GoString) :
    _root_.Perennial.fmt.ArgWf ⟨go.string, #x⟩ := by
  refine ⟨fun _ => ⟨x, rfl⟩, fun h => ?_, Or.inl rfl⟩
  exfalso
  simp only [_root_.Perennial.fmt.IsIntType, go.string, go.int, go.int64, go.int32, go.int16,
    go.int8, go.uint, go.uint64, go.uint32, go.uint16, go.uint8] at h
  rcases h with h | h | h | h | h | h | h | h | h | h <;> cases h

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apiserver.pkg.storage.Assumptions]

theorem storage.PrepareKey.wp_proof (wp_HasPrefix : strings.HasPrefix.spec (GF := GF) (hG := hG))
    (wp_HasSuffix : strings.HasSuffix.spec (GF := GF) (hG := hG))
    (wp_Contains : strings.Contains.spec (GF := GF) (hG := hG))
    (wp_Errorf : fmt.Errorf.spec (GF := GF) (hG := hG)) :
    storage.PrepareKey.spec (GF := GF) (hG := hG) := by
  intro rp key r
  wp_start
  ihave #Ps : isPkgInit (PROP := IProp GF) pkg_id.strings $$ []
  · iPkgInit
  ihave #Pf : isPkgInit (PROP := IProp GF) pkg_id.fmt $$ []
  · iPkgInit
  wp_auto
  -- `..` segments
  wp_if_destruct
  ·
    (try wp_auto)
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %sl ⟨Hsl, -⟩
    wp_apply wp_Errorf $$ [$Hsl] as %e -
    · iframe #
      simp only [EtcdGrove.fmt.argsOk, EtcdGrove.fmt.argOk]
      isplitl
      · ileft; ipureintro; exact argWf_string _
      · itrivial
    iapply HΦ
    ipureintro
    simp_all [k8s.prepareKeyM, k8s.dotDot, k8s.dotSeg]
  wp_apply wp_HasPrefix
  wp_if_destruct
  ·
    (try wp_auto)
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %sl ⟨Hsl, -⟩
    wp_apply wp_Errorf $$ [$Hsl] as %e -
    · iframe #
      simp only [EtcdGrove.fmt.argsOk, EtcdGrove.fmt.argOk]
      isplitl
      · ileft; ipureintro; exact argWf_string _
      · itrivial
    iapply HΦ
    ipureintro
    simp_all [k8s.prepareKeyM, k8s.dotDot, k8s.dotSeg]
  wp_apply wp_HasSuffix
  wp_if_destruct
  ·
    (try wp_auto)
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %sl ⟨Hsl, -⟩
    wp_apply wp_Errorf $$ [$Hsl] as %e -
    · iframe #
      simp only [EtcdGrove.fmt.argsOk, EtcdGrove.fmt.argOk]
      isplitl
      · ileft; ipureintro; exact argWf_string _
      · itrivial
    iapply HΦ
    ipureintro
    simp_all [k8s.prepareKeyM, k8s.dotDot, k8s.dotSeg]
  wp_apply wp_Contains
  wp_if_destruct
  ·
    (try wp_auto)
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %sl ⟨Hsl, -⟩
    wp_apply wp_Errorf $$ [$Hsl] as %e -
    · iframe #
      simp only [EtcdGrove.fmt.argsOk, EtcdGrove.fmt.argOk]
      isplitl
      · ileft; ipureintro; exact argWf_string _
      · itrivial
    iapply HΦ
    ipureintro
    simp_all [k8s.prepareKeyM, k8s.dotDot, k8s.dotSeg]
  -- `.` segments
  wp_if_destruct
  ·
    (try wp_auto)
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %sl ⟨Hsl, -⟩
    wp_apply wp_Errorf $$ [$Hsl] as %e -
    · iframe #
      simp only [EtcdGrove.fmt.argsOk, EtcdGrove.fmt.argOk]
      isplitl
      · ileft; ipureintro; exact argWf_string _
      · itrivial
    iapply HΦ
    ipureintro
    simp_all [k8s.prepareKeyM, k8s.dotDot, k8s.dotSeg]
  wp_apply wp_HasPrefix
  wp_if_destruct
  ·
    (try wp_auto)
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %sl ⟨Hsl, -⟩
    wp_apply wp_Errorf $$ [$Hsl] as %e -
    · iframe #
      simp only [EtcdGrove.fmt.argsOk, EtcdGrove.fmt.argOk]
      isplitl
      · ileft; ipureintro; exact argWf_string _
      · itrivial
    iapply HΦ
    ipureintro
    simp_all [k8s.prepareKeyM, k8s.dotDot, k8s.dotSeg]
  wp_apply wp_HasSuffix
  wp_if_destruct
  ·
    (try wp_auto)
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %sl ⟨Hsl, -⟩
    wp_apply wp_Errorf $$ [$Hsl] as %e -
    · iframe #
      simp only [EtcdGrove.fmt.argsOk, EtcdGrove.fmt.argOk]
      isplitl
      · ileft; ipureintro; exact argWf_string _
      · itrivial
    iapply HΦ
    ipureintro
    simp_all [k8s.prepareKeyM, k8s.dotDot, k8s.dotSeg]
  wp_apply wp_Contains
  wp_if_destruct
  ·
    (try wp_auto)
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %sl ⟨Hsl, -⟩
    wp_apply wp_Errorf $$ [$Hsl] as %e -
    · iframe #
      simp only [EtcdGrove.fmt.argsOk, EtcdGrove.fmt.argOk]
      isplitl
      · ileft; ipureintro; exact argWf_string _
      · itrivial
    iapply HΦ
    ipureintro
    simp_all [k8s.prepareKeyM, k8s.dotDot, k8s.dotSeg]
  -- the empty key, `/`
  wp_if_destruct
  ·
    (try wp_auto)
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %sl ⟨Hsl, -⟩
    wp_apply wp_Errorf $$ [$Hsl] as %e -
    · iframe #
      simp only [EtcdGrove.fmt.argsOk, EtcdGrove.fmt.argOk]
      isplitl
      · ileft; ipureintro; exact argWf_string _
      · itrivial
    iapply HΦ
    ipureintro
    simp_all [k8s.prepareKeyM, k8s.dotDot, k8s.dotSeg]
  wp_if_destruct
  ·
    (try wp_auto)
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %sl ⟨Hsl, -⟩
    wp_apply wp_Errorf $$ [$Hsl] as %e -
    · iframe #
      simp only [EtcdGrove.fmt.argsOk, EtcdGrove.fmt.argOk]
      isplitl
      · ileft; ipureintro; exact argWf_string _
      · itrivial
    iapply HΦ
    ipureintro
    simp_all [k8s.prepareKeyM, k8s.dotDot, k8s.dotSeg]
  -- a recursive key ends in `/`, then the resource prefix
  wp_if_destruct
  · -- not recursive
    wp_apply wp_HasPrefix
    wp_if_destruct
    · iapply HΦ
      ipureintro
      simp_all [k8s.prepareKeyM, k8s.dotDot, k8s.dotSeg]
    ·
      (try wp_auto)
      wp_apply wp_slice_literal
      isplitr
      · ipureintro; rfl
      iintro %sl ⟨Hsl, -⟩
      wp_apply wp_Errorf $$ [$Hsl] as %e -
      · iframe #
        rw [show sint.nat (W64 (0 + 1)) = 1 from rfl]
        simp only [List.set, EtcdGrove.fmt.argsOk, EtcdGrove.fmt.argOk]
        isplitl
        · ileft; ipureintro; exact argWf_string _
        isplitl
        · ileft; ipureintro; exact argWf_string _
        · itrivial
      iapply HΦ
      ipureintro
      simp_all [k8s.prepareKeyM, k8s.dotDot, k8s.dotSeg]
  · -- recursive
    wp_apply wp_HasSuffix
    wp_if_destruct
    · (try wp_auto)
      wp_apply wp_HasPrefix
      wp_if_destruct
      · iapply HΦ
        ipureintro
        simp_all [k8s.prepareKeyM, k8s.dotDot, k8s.dotSeg]
      ·
        (try wp_auto)
        wp_apply wp_slice_literal
        isplitr
        · ipureintro; rfl
        iintro %sl ⟨Hsl, -⟩
        wp_apply wp_Errorf $$ [$Hsl] as %e -
        · iframe #
          rw [show sint.nat (W64 (0 + 1)) = 1 from rfl]
          simp only [List.set, EtcdGrove.fmt.argsOk, EtcdGrove.fmt.argOk]
          isplitl
          · ileft; ipureintro; exact argWf_string _
          isplitl
          · ileft; ipureintro; exact argWf_string _
          · itrivial
        iapply HΦ
        ipureintro
        simp_all [k8s.prepareKeyM, k8s.dotDot, k8s.dotSeg]
    · (try wp_auto)
      wp_apply wp_HasPrefix
      wp_if_destruct
      · iapply HΦ
        ipureintro
        simp_all [k8s.prepareKeyM, k8s.dotDot, k8s.dotSeg]
      ·
        (try wp_auto)
        wp_apply wp_slice_literal
        isplitr
        · ipureintro; rfl
        iintro %sl ⟨Hsl, -⟩
        wp_apply wp_Errorf $$ [$Hsl] as %e -
        · iframe #
          rw [show sint.nat (W64 (0 + 1)) = 1 from rfl]
          simp only [List.set, EtcdGrove.fmt.argsOk, EtcdGrove.fmt.argOk]
          isplitl
          · ileft; ipureintro; exact argWf_string _
          isplitl
          · ileft; ipureintro; exact argWf_string _
          · itrivial
        iapply HΦ
        ipureintro
        simp_all [k8s.prepareKeyM, k8s.dotDot, k8s.dotSeg]

end proof

end EtcdGrove
end Perennial
