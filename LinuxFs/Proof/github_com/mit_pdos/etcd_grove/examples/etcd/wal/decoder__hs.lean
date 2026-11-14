/- Lean-first (no Rocq counterpart). The proof of `(*decoder).hs` (W4c U5): three `u64`s. -/
module

public import LinuxFs.Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.decoder__hs
public import LinuxFs.Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.decoder__u64

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_wal

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.etcd.wal

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.wal.Assumptions]

theorem decoder.hs.wp_proof (wp_u64 : decoder.u64.spec (GF := GF) (hG := hG)) :
    decoder.hs.spec (GF := GF) (hG := hG) := by
  intro d bs k h r hdrop
  obtain ⟨t, v, c⟩ := h
  have h1 : bs.drop k = tU64 t ++ (tU64 v ++ (tU64 c ++ r)) := by
    rw [hdrop]; simp [tHsBytes]
  have h2 := drop_app' h1
  have h3 := drop_app' h2
  rw [tU64_length] at h2 h3
  wp_start as Hd
  wp_auto
  wp_apply wp_u64 d bs k t _ h1 $$ Hd as Hd
  wp_apply wp_u64 d bs (k + 8) v _ h2 $$ Hd as Hd
  wp_apply wp_u64 d bs (k + 8 + 8) c _ h3 $$ Hd as Hd
  iapply HΦ
  iexact Hd

end proof

end etcd_wal
end EtcdGrove
end Perennial
