/-
The proof of `decTRes` (`Spec/.../dist/kvremote/decTRes.lean`): the fields' reads, in order, chained through
`decPost_elim` and back through `decPost_intro`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote.decTRes
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.enc.Dec__Int
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.enc.Dec__Bool
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote.decVR
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.enc.Dec__I64

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote

open github_com.mit_pdos.etcd_grove.examples.etcd.dist.enc
open github_com.mit_pdos.etcd_grove.examples.lib.txnwork

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote.Assumptions]
variable [enc_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.enc.Assumptions]

theorem decTRes.wp_proof (wp_Int : Dec.Int.spec (GF := GF) (hG := hG)) (wp_Bool : Dec.Bool.spec (GF := GF) (hG := hG)) (wp_decVR : decVR.spec (GF := GF) (hG := hG)) (wp_I64 : Dec.I64.spec (GF := GF) (hG := hG)) :
    decTRes.spec (GF := GF) (hG := hG) := by
  intro d bs ok
  wp_start as Hd
  ihave #Penc : isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.dist.enc $$ []
  · iPkgInit
  try wp_auto
  wp_apply wp_Int d bs ok $$ [Hd] as %y1 Hd
  · iframe
  icases decPost_elim _ _ _ _ _ $$ Hd with ⟨%r1, %ok1, Hd, %H1⟩
  try wp_auto
  wp_apply wp_Bool d r1 ok1 $$ [Hd] as %y2 Hd
  · iframe
  icases decPost_elim _ _ _ _ _ $$ Hd with ⟨%r2, %ok2, Hd, %H2⟩
  try wp_auto
  wp_apply wp_decVR d r2 ok2 $$ [Hd] as %y3 Hd
  · iframe
  icases decPost_elim _ _ _ _ _ $$ Hd with ⟨%r3, %ok3, Hd, %H3⟩
  try wp_auto
  wp_apply wp_I64 d r3 ok3 $$ [Hd] as %y4 Hd
  · iframe
  icases decPost_elim _ _ _ _ _ $$ Hd with ⟨%r4, %ok4, Hd, %H4⟩
  try wp_auto
  iapply HΦ
  iapply decPost_intro _ _ r4 _ ok4 _ _ ?_ $$ Hd
  · intro h
    obtain ⟨h4a, h4b⟩ := H4 h
    obtain ⟨h3a, h3b⟩ := H3 h4a
    obtain ⟨h2a, h2b⟩ := H2 h3a
    obtain ⟨h1a, h1b⟩ := H1 h2a
    refine ⟨h1a, ?_⟩
    subst h1b h2b h3b h4b
    simp only [tResBytes, List.append_assoc]

end proof

end github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote
end Perennial
