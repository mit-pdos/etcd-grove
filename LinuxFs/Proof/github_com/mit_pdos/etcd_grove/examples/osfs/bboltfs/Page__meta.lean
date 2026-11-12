/- Lean-first (no Rocq counterpart). The proof of `(*Page).meta`: `unsafe.Add(p, 16)`. -/
module

public import LinuxFs.Spec.github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs.Page__meta

@[expose] public section

noncomputable section

namespace Perennial

open Fs
namespace EtcdGrove
namespace osfs_bboltfs

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs.Assumptions]

theorem Page.«meta».wp_proof : Page.«meta».spec (GF := GF) (hG := hG) := by
  intro p
  wp_start as %H
  wp_auto
  wp_func_call
  wp_call
  wp_apply wp_pointer_plus
  · rw [show sint.Z (W64 16) = 16 from rfl]; simp only [Loc.add]; omega
  rw [show sint.Z (W64 16) = 16 from rfl]
  iapply HΦ
  itrivial

end proof

end osfs_bboltfs
end EtcdGrove
end Perennial
