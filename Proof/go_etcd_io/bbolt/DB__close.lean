module
public import Spec.go_etcd_io.bbolt.DB__close
public import Spec.go_etcd_io.bbolt.DB__munmap
public import Spec.go_etcd_io.bbolt.funlock
public import Spec.os.File__Close
public import Perennial.Proof.fmt

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

theorem DB.close.wp_proof (hmunmap : DB.munmap.spec (GF := GF) (hG := hG))
    (hfunlock : funlock.spec (GF := GF) (hG := hG))
    (hClose : os.File.Close.spec (GF := GF) (hG := hG)) :
    DB.close.spec (GF := GF) (hG := hG) := by
  intro dbl f fd bs path p ro fl wa dr dp ds m0 m1 n hf
  wp_start as ⟨Hop, Hfl, Hwa, Hm0, Hm1, Hdr, Hdp, Hds, Hbytes, Hmap, Hfile, Hro, Hp, #Hof, Hfp⟩
  wp_auto
  wp_apply hmunmap dbl dr dp ds m0 m1 fd bs n $$ [Hm0 Hm1 Hdr Hdp Hds Hbytes Hmap]
    as ⟨Hdr, Hdp, Hds, Hm0, Hm1, Hbytes, Hmap⟩
  · iframe
  try wp_auto
  rw [decide_eq_false hf]
  ihave Hs : ((zero_val GoSlice : GoSlice) ↦* ([] : List GoInterface)) $$ []
  · iapply ownSlice_nil
  ihave Hc : ownSliceCap GoInterface (zero_val GoSlice : GoSlice) (DFrac.own 1) $$ []
  · iapply ownSliceCap_nil
  cases ro
  · -- writable: unlock the file; a failure is recorded
    try wp_auto
    wp_apply hfunlock dbl f fd (DFrac.own 1) $$ [Hfile] as %e1 ⟨Hfile, %He1⟩
    · iframe; iframe #
    try wp_auto
    rcases He1 with rfl | ⟨x, rfl⟩
    · try wp_auto
      wp_apply hClose f fd bs path $$ [Hof Hbytes Hfp Hmap] as %e2 Hfs
      · iframe; iframe #
      try wp_auto
      cases e2 with
      | nil =>
        try wp_auto
        icases persistent_entails_left (ownSlice_len _ _ _) $$ Hs with ⟨Hs, %Hxl⟩
        first
          | (wp_if_destruct
             · simp only [show (0 : Int) ≤ sint.Z (W64 0) from by decide, Hif, _root_.and_self, ↓reduceIte]
               wp_apply wp_load_slice_index _ _ _ _ _ (by decide) $$ [Hs] as Hs
               · iframe; ipureintro; rfl
               try wp_auto
               iapply HΦ
               iframe
             · try wp_auto
               iapply HΦ
               iframe)
          | (try wp_auto
             iapply HΦ
             iframe)
      | ok ei2 =>
        try wp_auto
        wp_apply wp_slice_literal
        isplitr
        · ipureintro; rfl
        iintro %sl ⟨Hsl, -⟩
        wp_apply fmt.wp_Errorf $$ [$Hsl] as %e3 _
        try wp_auto
        wp_apply wp_slice_literal
        isplitr
        · ipureintro; rfl
        iintro %sl2 ⟨Hsl2, -⟩
        wp_apply wp_slice_append $$ [$Hs $Hc $Hsl2] as %es' ⟨Hs, Hc, -⟩
        try wp_auto
        icases persistent_entails_left (ownSlice_len _ _ _) $$ Hs with ⟨Hs, %Hxl⟩
        first
          | (wp_if_destruct
             · simp only [show (0 : Int) ≤ sint.Z (W64 0) from by decide, Hif, _root_.and_self, ↓reduceIte]
               wp_apply wp_load_slice_index _ _ _ _ _ (by decide) $$ [Hs] as Hs
               · iframe; ipureintro; rfl
               try wp_auto
               iapply HΦ
               iframe
             · try wp_auto
               iapply HΦ
               iframe)
          | (try wp_auto
             iapply HΦ
             iframe)
    · try wp_auto
      wp_apply wp_slice_literal
      isplitr
      · ipureintro; rfl
      iintro %sl ⟨Hsl, -⟩
      wp_apply fmt.wp_Errorf $$ [$Hsl] as %e3 _
      try wp_auto
      wp_apply wp_slice_literal
      isplitr
      · ipureintro; rfl
      iintro %sl2 ⟨Hsl2, -⟩
      wp_apply wp_slice_append $$ [$Hs $Hc $Hsl2] as %es' ⟨Hs, Hc, -⟩
      try wp_auto
      wp_apply hClose f fd bs path $$ [Hof Hbytes Hfp Hmap] as %e2 Hfs
      · iframe; iframe #
      try wp_auto
      cases e2 with
      | nil =>
        try wp_auto
        icases persistent_entails_left (ownSlice_len _ _ _) $$ Hs with ⟨Hs, %Hxl⟩
        first
          | (wp_if_destruct
             · simp only [show (0 : Int) ≤ sint.Z (W64 0) from by decide, Hif, _root_.and_self, ↓reduceIte]
               wp_apply wp_load_slice_index _ _ _ _ _ (by decide) $$ [Hs] as Hs
               · iframe; ipureintro; rfl
               try wp_auto
               iapply HΦ
               iframe
             · try wp_auto
               iapply HΦ
               iframe)
          | (try wp_auto
             iapply HΦ
             iframe)
      | ok ei2 =>
        try wp_auto
        wp_apply wp_slice_literal
        isplitr
        · ipureintro; rfl
        iintro %sl ⟨Hsl, -⟩
        wp_apply fmt.wp_Errorf $$ [$Hsl] as %e3 _
        try wp_auto
        wp_apply wp_slice_literal
        isplitr
        · ipureintro; rfl
        iintro %sl2 ⟨Hsl2, -⟩
        wp_apply wp_slice_append $$ [$Hs $Hc $Hsl2] as %es' ⟨Hs, Hc, -⟩
        try wp_auto
        icases persistent_entails_left (ownSlice_len _ _ _) $$ Hs with ⟨Hs, %Hxl⟩
        first
          | (wp_if_destruct
             · simp only [show (0 : Int) ≤ sint.Z (W64 0) from by decide, Hif, _root_.and_self, ↓reduceIte]
               wp_apply wp_load_slice_index _ _ _ _ _ (by decide) $$ [Hs] as Hs
               · iframe; ipureintro; rfl
               try wp_auto
               iapply HΦ
               iframe
             · try wp_auto
               iapply HΦ
               iframe)
          | (try wp_auto
             iapply HΦ
             iframe)
  · -- read-only
    try wp_auto
    wp_apply hClose f fd bs path $$ [Hof Hbytes Hfp Hmap] as %e2 Hfs
    · iframe; iframe #
    try wp_auto
    cases e2 with
    | nil =>
      try wp_auto
      icases persistent_entails_left (ownSlice_len _ _ _) $$ Hs with ⟨Hs, %Hxl⟩
      first
        | (wp_if_destruct
           · simp only [show (0 : Int) ≤ sint.Z (W64 0) from by decide, Hif, _root_.and_self, ↓reduceIte]
             wp_apply wp_load_slice_index _ _ _ _ _ (by decide) $$ [Hs] as Hs
             · iframe; ipureintro; rfl
             try wp_auto
             iapply HΦ
             iframe
           · try wp_auto
             iapply HΦ
             iframe)
        | (try wp_auto
           iapply HΦ
           iframe)
    | ok ei2 =>
      try wp_auto
      wp_apply wp_slice_literal
      isplitr
      · ipureintro; rfl
      iintro %sl ⟨Hsl, -⟩
      wp_apply fmt.wp_Errorf $$ [$Hsl] as %e3 _
      try wp_auto
      wp_apply wp_slice_literal
      isplitr
      · ipureintro; rfl
      iintro %sl2 ⟨Hsl2, -⟩
      wp_apply wp_slice_append $$ [$Hs $Hc $Hsl2] as %es' ⟨Hs, Hc, -⟩
      try wp_auto
      icases persistent_entails_left (ownSlice_len _ _ _) $$ Hs with ⟨Hs, %Hxl⟩
      first
        | (wp_if_destruct
           · simp only [show (0 : Int) ≤ sint.Z (W64 0) from by decide, Hif, _root_.and_self, ↓reduceIte]
             wp_apply wp_load_slice_index _ _ _ _ _ (by decide) $$ [Hs] as Hs
             · iframe; ipureintro; rfl
             try wp_auto
             iapply HΦ
             iframe
           · try wp_auto
             iapply HΦ
             iframe)
        | (try wp_auto
           iapply HΦ
           iframe)

end proof

end bbolt
end EtcdGrove
end Perennial
