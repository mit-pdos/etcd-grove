/-
Lean-first (no Rocq counterpart). #33 S3b-2 (2026-11-23): the proof of `Concat`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Concat

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace AntCheck

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Assumptions]

theorem Concat.wp_proof : Concat.spec (GF := GF) (hG := hG) := by
  intro al a bl b
  wp_start as ⟨#Ha, #Hb, %Hlen⟩
  iunfold logRO at Ha Hb
  icases Ha with ⟨%es, #Hes, #Hae⟩
  icases Hb with ⟨%fs, #Hfs, #Hbf⟩
  ihave %Hel := ownSlice_len $$ Hes
  ihave %Hfl := ownSlice_len $$ Hfs
  ihave %Hael := BigSepL2.bigSepL2_length $$ Hae
  ihave %Hbfl := BigSepL2.bigSepL2_length $$ Hbf
  iapply wp_fupd
  wp_auto
  have hle : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) ≤ sint.Z (al.len + bl.len) := by
    have := Hel.2; have := Hfl.2; constructor <;> word
  wp_apply wp_slice_make3 (V := G.Entry) (W64 0) (al.len + bl.len) hle as %out ⟨Hout, Hcap, -⟩
  try wp_auto
  wp_apply wp_slice_append out _ al es DFrac.discard $$ [Hout Hcap Hes] as %s1 ⟨Hs1, Hcap1, -⟩
  · iframe Hout Hcap Hes
  try wp_auto
  wp_apply wp_slice_append s1 _ bl fs DFrac.discard $$ [Hs1 Hcap1 Hfs] as %s2 ⟨Hs2, -, -⟩
  · iframe Hs1 Hcap1 Hfs
  try wp_auto
  imod ownSlice_persist $$ Hs2 with #Hs2
  imodintro
  iapply HΦ
  iunfold logRO
  iexists es ++ fs
  rw [List.replicate_zero, List.nil_append]
  iframe Hs2
  iapply (BigSepL2.bigSepL2_app_wand (Φ := fun _ e x => entryRO (GF := GF) e x)) $$ Hae Hbf

end proof

end AntCheck
end EtcdGrove
end Perennial
