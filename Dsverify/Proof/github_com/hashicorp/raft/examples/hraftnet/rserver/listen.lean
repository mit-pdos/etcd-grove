/-
`rserver.listen`'s proof (hraft_robust; the copy of hraftnet's, `listen.lean`): `net.Listen` retried (as vr's `awaitConf`'s loop).
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.rserver.listen
public import Perennial.Proof.time.Link
public import Net.Proof.net.AtAddr

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace github_com.hashicorp.raft.examples.hraftnet.rserver

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : Assumptions]

set_option goose.wp.extras true

theorem listen.wp_proof (wp_Listen : net.Listen.spec (GF := GF) (hG := hG)) :
    listen.spec (GF := GF) := by
  intro a
  wp_start as ⟨%Hok, #Hau⟩
  ihave #Hnet : isPkgInit (PROP := IProp GF) pkg_id.net $$ []
  · iPkgInit
  wp_auto
  wp_apply ((net.Listen.spec_addrOk wp_Listen) go!"tcp" net.tcpNet_tcp a) as %lv %err Hres
  · isplitr; · ipureintro; exact Hok
    iexact Hau
  ihave HL : (∃ (lv err : GoInterface), "l" ∷ l_ptr ↦ lv ∗ "err" ∷ err_ptr ↦ err ∗
      "Hres" ∷ ((⌜err = GoInterface.nil⌝ ∗ ∃ l, net.isListener lv l ∗
          netLis (extLocalGS netExt (L := hG.goose_localGS)) l a true ∗
          netLisAt (extLocalGS netExt (L := hG.goose_localGS)) l a) ∨
        ⌜err ≠ GoInterface.nil⌝) : IProp GF) $$ [l err Hres]
  · iexists lv, err; iframe l err
    icases Hres with (H | ⟨%x, -, #HE⟩)
    · ileft; iexact H
    · iright
      icases net.resErr_netErr _ _ _ _ _ _ _ $$ HE with %Hne
      ipureintro; exact net.netErr_ne_nil (Hne.2 (by simp))
  wp_for HL
  icases Hres with (⟨%He, %l, #Hl, Hlis, Hla⟩ | %Hne)
  rotate_left
  · cases err with
    | nil => exact absurd rfl Hne
    | ok i =>
    wp_auto
    simp only [_root_.decide_true, ↓reduceIte]
    wp_auto
    wp_apply time.wp_Sleep
    wp_apply ((net.Listen.spec_addrOk wp_Listen) go!"tcp" net.tcpNet_tcp a) as %lv2 %err2 Hres
    · isplitr; · ipureintro; exact Hok
      iexact Hau
    wp_for_post
    iframe
    iexists lv2, err2; iframe
    icases Hres with (H | ⟨%x, -, #HE⟩)
    · ileft; iexact H
    · iright
      icases net.resErr_netErr _ _ _ _ _ _ _ $$ HE with %Hne
      ipureintro; exact net.netErr_ne_nil (Hne.2 (by simp))
  subst He
  wp_auto
  rw [dec_val_false']
  simp only [Bool.false_eq_true, _root_.decide_true, ↓reduceIte]
  wp_auto
  iapply HΦ
  iexists l
  iframe
  iexact Hl

end proof

end github_com.hashicorp.raft.examples.hraftnet.rserver

end Perennial
