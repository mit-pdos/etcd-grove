/-
The proof of `DecOutput` (`Spec/.../dist/kvremote/DecOutput.lean`): the fields' reads, in order, chained through
`decPost_elim`, then `Done`: when it accepts, every read succeeded and nothing is left.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote.DecOutput
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.enc.Dec__Bool
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.enc.Dec__I64
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote.decVR
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.enc.Dec__Int
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote.decTRes
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote.decKV
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.enc.NewDec
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.enc.Dec__Done

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

theorem DecOutput.wp_proof (wp_Bool : Dec.Bool.spec (GF := GF) (hG := hG)) (wp_I64 : Dec.I64.spec (GF := GF) (hG := hG)) (wp_decVR : decVR.spec (GF := GF) (hG := hG)) (wp_Int : Dec.Int.spec (GF := GF) (hG := hG)) (wp_decTRes : decTRes.spec (GF := GF) (hG := hG)) (wp_decKV : decKV.spec (GF := GF) (hG := hG)) (wp_NewDec : NewDec.spec (GF := GF) (hG := hG)) (wp_Done : Dec.Done.spec (GF := GF) (hG := hG)) :
    DecOutput.spec (GF := GF) (hG := hG) := by
  intro b bs dq
  wp_start as Hb
  ihave #Penc : isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.dist.enc $$ []
  · iPkgInit
  try wp_auto
  wp_apply wp_NewDec b bs dq $$ [Hb] as %d Hd
  · iframe
  try wp_auto
  wp_apply wp_Bool d bs true $$ [Hd] as %y1 Hd
  · iframe
  icases decPost_elim _ _ _ _ _ $$ Hd with ⟨%r1, %ok1, Hd, %H1⟩
  try wp_auto
  wp_apply wp_I64 d r1 ok1 $$ [Hd] as %y2 Hd
  · iframe
  icases decPost_elim _ _ _ _ _ $$ Hd with ⟨%r2, %ok2, Hd, %H2⟩
  try wp_auto
  wp_apply wp_Bool d r2 ok2 $$ [Hd] as %y3 Hd
  · iframe
  icases decPost_elim _ _ _ _ _ $$ Hd with ⟨%r3, %ok3, Hd, %H3⟩
  try wp_auto
  wp_apply wp_decVR d r3 ok3 $$ [Hd] as %y4 Hd
  · iframe
  icases decPost_elim _ _ _ _ _ $$ Hd with ⟨%r4, %ok4, Hd, %H4⟩
  try wp_auto
  wp_apply wp_I64 d r4 ok4 $$ [Hd] as %y5 Hd
  · iframe
  icases decPost_elim _ _ _ _ _ $$ Hd with ⟨%r5, %ok5, Hd, %H5⟩
  try wp_auto
  wp_apply wp_Bool d r5 ok5 $$ [Hd] as %y6 Hd
  · iframe
  icases decPost_elim _ _ _ _ _ $$ Hd with ⟨%r6, %ok6, Hd, %H6⟩
  try wp_auto
  wp_apply wp_Int d r6 ok6 $$ [Hd] as %y7 Hd
  · iframe
  icases decPost_elim _ _ _ _ _ $$ Hd with ⟨%r7, %ok7, Hd, %H7⟩
  try wp_auto
  wp_apply wp_decTRes d r7 ok7 $$ [Hd] as %y8 Hd
  · iframe
  icases decPost_elim _ _ _ _ _ $$ Hd with ⟨%r8, %ok8, Hd, %H8⟩
  try wp_auto
  wp_apply wp_decTRes d r8 ok8 $$ [Hd] as %y9 Hd
  · iframe
  icases decPost_elim _ _ _ _ _ $$ Hd with ⟨%r9, %ok9, Hd, %H9⟩
  try wp_auto
  wp_apply wp_decTRes d r9 ok9 $$ [Hd] as %y10 Hd
  · iframe
  icases decPost_elim _ _ _ _ _ $$ Hd with ⟨%r10, %ok10, Hd, %H10⟩
  try wp_auto
  wp_apply wp_Int d r10 ok10 $$ [Hd] as %y11 Hd
  · iframe
  icases decPost_elim _ _ _ _ _ $$ Hd with ⟨%r11, %ok11, Hd, %H11⟩
  try wp_auto
  wp_apply wp_decKV d r11 ok11 $$ [Hd] as %y12 Hd
  · iframe
  icases decPost_elim _ _ _ _ _ $$ Hd with ⟨%r12, %ok12, Hd, %H12⟩
  try wp_auto
  wp_apply wp_decKV d r12 ok12 $$ [Hd] as %y13 Hd
  · iframe
  icases decPost_elim _ _ _ _ _ $$ Hd with ⟨%r13, %ok13, Hd, %H13⟩
  try wp_auto
  wp_apply wp_decKV d r13 ok13 $$ [Hd] as %y14 Hd
  · iframe
  icases decPost_elim _ _ _ _ _ $$ Hd with ⟨%r14, %ok14, Hd, %H14⟩
  try wp_auto
  wp_apply wp_Done d r14 ok14 $$ [Hd] as %dn %Hdn
  · iframe
  try wp_auto
  iapply HΦ
  ipureintro
  intro hd
  obtain ⟨hok, hnil⟩ := Hdn hd
  obtain ⟨h14a, h14b⟩ := H14 hok
  obtain ⟨h13a, h13b⟩ := H13 h14a
  obtain ⟨h12a, h12b⟩ := H12 h13a
  obtain ⟨h11a, h11b⟩ := H11 h12a
  obtain ⟨h10a, h10b⟩ := H10 h11a
  obtain ⟨h9a, h9b⟩ := H9 h10a
  obtain ⟨h8a, h8b⟩ := H8 h9a
  obtain ⟨h7a, h7b⟩ := H7 h8a
  obtain ⟨h6a, h6b⟩ := H6 h7a
  obtain ⟨h5a, h5b⟩ := H5 h6a
  obtain ⟨h4a, h4b⟩ := H4 h5a
  obtain ⟨h3a, h3b⟩ := H3 h4a
  obtain ⟨h2a, h2b⟩ := H2 h3a
  obtain ⟨h1a, h1b⟩ := H1 h2a
  subst h1b h2b h3b h4b h5b h6b h7b h8b h9b h10b h11b h12b h13b h14b
  subst hnil
  simp only [outputBytes, List.append_assoc, List.append_nil]

end proof

end github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote
end Perennial
