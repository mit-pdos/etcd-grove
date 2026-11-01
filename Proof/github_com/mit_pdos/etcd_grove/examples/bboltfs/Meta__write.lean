/- Lean-first (no Rocq counterpart). The proof of `(*Meta).write`. -/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.bboltfs.Meta__write
public import Spec.github_com.mit_pdos.etcd_grove.examples.bboltfs.Meta__sum64
public import Spec.github_com.mit_pdos.etcd_grove.examples.bboltfs.Page__meta

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bboltfs

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode github_com.mit_pdos.etcd_grove.examples.bboltfs

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.bboltfs.Assumptions]

theorem Meta.write.wp_proof (wp_sum64 : Meta.sum64.spec (GF := GF) (hG := hG))
    (wp_meta : Page.«meta».spec (GF := GF) (hG := hG)) :
    Meta.write.spec (GF := GF) (hG := hG) := by
  intro m p v hdr old
  wp_start as ⟨Hm, Hp, Ho, %Hpos⟩
  have hmn : m ≠ null := by intro h; subst h; simp [null] at Hpos
  have hpn : p ≠ null := by intro h; subst h; simp [null] at Hpos
  have hp16 : 0 < (p +ₗ 16).addr := by simp only [Loc.add]; omega
  icases (typedPointsto_bytes (p +ₗ 16) old _ hp16).1 $$ Ho with Ho
  ihave %Hob := bytesPointsto_in_bounds _ _ _ (ByteEncoding.encode_ne_nil old (by decide)) $$ Ho
  icases (typedPointsto_bytes (p +ₗ 16) old _ hp16).2 $$ Ho with Ho
  icases typedPointsto_split _ _ _ $$ Hm with Hm
  simp only [TypedPointsto.typedPointstoDef]
  icases Hm with ⟨Hmagic, Hversion, HpageSize, Hflags, Hroot, Hfreelist, Hpgid, Htxid, Hchecksum, -⟩
  icases typedPointsto_split _ _ _ $$ Hp with Hp
  simp only [TypedPointsto.typedPointstoDef]
  icases Hp with ⟨Hid, Hpflags, Hcount, Hoverflow, -⟩
  wp_auto
  ihave Hm : m ↦ v $$ [Hmagic Hversion HpageSize Hflags Hroot Hfreelist Hpgid Htxid Hchecksum]
  · iapply typedPointsto_combine _ _ _ hmn
    simp only [TypedPointsto.typedPointstoDef]
    iframe
  wp_apply wp_sum64 m v (DFrac.own 1) $$ [Hm] as Hm
  · iframe Hm; ipureintro; exact Hpos.1
  wp_apply wp_meta
  · ipureintro; simp only [Loc.add] at Hob ⊢; omega
  iapply HΦ
  iframe Hm Ho
  iapply typedPointsto_combine _ _ _ hpn
  simp only [TypedPointsto.typedPointstoDef]
  iframe

end proof

end bboltfs
end EtcdGrove
end Perennial
