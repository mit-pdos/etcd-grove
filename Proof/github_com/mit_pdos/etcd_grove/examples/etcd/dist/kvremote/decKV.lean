/-
The proof of `decKV` (`Spec/.../dist/kvremote/decKV.lean`): the fields' reads, in order, chained through
`decPost_elim` and back through `decPost_intro`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote.decKV
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.enc.Dec__Str
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote.decVR

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote

open github_com.mit_pdos.etcd_grove.examples.etcd.dist.enc
open github_com.mit_pdos.etcd_grove.examples.etcd.txnlin

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote.Assumptions]
variable [enc_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.enc.Assumptions]

theorem decKV.wp_proof (wp_Str : Dec.Str.spec (GF := GF) (hG := hG)) (wp_decVR : decVR.spec (GF := GF) (hG := hG)) :
    decKV.spec (GF := GF) (hG := hG) := by
  intro d bs ok
  wp_start as Hd
  ihave #Penc : isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.dist.enc $$ []
  · iPkgInit
  try wp_auto
  wp_apply wp_Str d bs ok $$ [Hd] as %y1 Hd
  · iframe
  icases decPost_elim _ _ _ _ _ $$ Hd with ⟨%r1, %ok1, Hd, %H1⟩
  try wp_auto
  wp_apply wp_decVR d r1 ok1 $$ [Hd] as %y2 Hd
  · iframe
  icases decPost_elim _ _ _ _ _ $$ Hd with ⟨%r2, %ok2, Hd, %H2⟩
  try wp_auto
  iapply HΦ
  iapply decPost_intro _ _ r2 _ ok2 _ _ ?_ $$ Hd
  · intro h
    obtain ⟨h2a, h2b⟩ := H2 h
    obtain ⟨h1a, h1b⟩ := H1 h2a
    refine ⟨h1a, ?_⟩
    subst h1b h2b
    simp only [kvBytes, List.append_assoc]

end proof

end github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote
end Perennial
