/- Lean-first (no Rocq counterpart).

# `Client`'s proof

The sessions' wait group is `sync.tokJoin`'s (as rpcdriver's `callOn`: each `Add(1)` deposits the
caller's thread token, the goroutine's deferred `Done` gives one back), with no lending. Each
goroutine runs `session` (`session.spec`, from the persistent `drvFacts` and `drvAddr`); after
`Wait`, `reached` returns (`drvFacts`).
-/
module

public import Net.Spec.github_com.mit_pdos.etcd_grove.examples.net.httpdriver.Client
public import Net.Spec.github_com.mit_pdos.etcd_grove.examples.net.httpdriver.session
public import Net.Spec.github_com.mit_pdos.etcd_grove.examples.net.httpdriver.below
public import Perennial.Proof.sync.WaitGroupTokJoin
public import Perennial.Proof.sync.Results
public import Perennial.Proof.sync.Link

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net
open net.http (HttpProtoGS)

namespace github_com.mit_pdos.etcd_grove.examples.net.httpdriver

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : Assumptions] [field_sem : net.FieldAssumptions]
variable [π : NetProtoGS] [hπ : HttpProtoGS]

attribute [local instance] GooseGlobalGS.gooseInvGS

/-- The namespace of the sessions' wait group. -/
def sessN : Namespace := nroot.@"httpdriver.sessions"

theorem Client.wp_proof (wp_below : below.spec (GF := GF) (hG := hG))
    (wp_session : session.spec (GF := GF) (hG := hG)) :
    Client.spec (GF := GF) (hG := hG) := by
  wp_start as ⟨#Hf, #Haddr, %Hb, Htok⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  ihave #Hf' := Hf
  iunfold drvFacts at Hf'
  icases Hf' with ⟨%fr, #Hrg, #Hrf⟩
  try wp_auto
  irename wg => Hwg0
  icases typedPointsto_not_null_dup _ _ _ $$ Hwg0 with ⟨Hwg0, %Hwgnn⟩
  imod sync.init_WaitGroup (sessN.@"wg") wg_ptr $$ Hwg0 with ⟨%γwg, #Hiswg, Hctr0, Hwait⟩
  ihave #Hlaw := sync.tokJoin.lendLaw_false (GF := GF) sessN
  imod sync.tokJoin.init sessN iprop(False) wg_ptr γwg ⊤ (Nat.le_trans Hb (by decide))
    $$ [$Hiswg $Hctr0 $Hwait $Hlaw] with Hadd
  wp_apply wp_below (W64 4) as %w0 -
  try wp_auto
  ihave IH : iprop(∃ (k : w64) (m : Nat) (Pw : IProp GF), "k" ∷ k_ptr ↦ k ∗
      "Hadd" ∷ sync.tokJoin.ownAdder sessN iprop(False) wg_ptr m Pw ∗ "Htok" ∷ threadTok)
      $$ [k Hadd Htok]
  · iexists W64 0, 0, iprop(True)
    iframe k Hadd Htok
  wp_for IH
  wp_if_destruct
  · -- a session
    try wp_auto
    wp_apply (sync.tokJoin.WaitGroup.wp_Add iprop(True) sessN iprop(False) wg_ptr m Pw)
      $$ [$Hsync $Hadd $Htok] as ⟨Hadd, Hdone⟩
    wp_bind (Fork _)
    iapply wp_fork_tok_self $$ [Hdone]
    · inext
      try wp_auto
      wp_apply wp_with_defer as %defer Hdefer
      try wp_auto
      wp_apply wp_session $$ [$Hf $Haddr]
      try wp_auto
      wp_apply (sync.tokJoin.WaitGroup.wp_Done sessN iprop(False) wg_ptr iprop(True))
        $$ [$Hsync $Hdone] as Htok
      try wp_auto
      iframe Htok
    · inext
      iintro Htok
      try wp_auto
      wp_for_post
      iframe
      iexists k + W64 1, m + 1, iprop(Pw ∗ True)
      iframe
  · try wp_auto
    wp_apply (sync.tokJoin.WaitGroup.wp_Wait sessN iprop(False) wg_ptr m Pw) $$ [$Hsync $Hadd]
      as ⟨-, -⟩
    try wp_auto
    wp_bind (App (Val #fr) (Val _))
    iapply wp_wand $$ (Hrf $$ %go!"concurrent-connections")
    iintro %v %Hv
    subst Hv
    try wp_auto
    iapply HΦ
    iexact Htok

end proof

end github_com.mit_pdos.etcd_grove.examples.net.httpdriver
end Perennial
