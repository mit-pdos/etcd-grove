/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/third_party/bridge/bridge__serveConn.lean`. The local
wait group joins the two copy goroutines, each with half of the connection's share of
`b.blackholec` (`pairInv`); the deferred function deposits the share (`doneQ`), closes `donec`
with it, and, if the connection is still in the map, takes it back to the mutex's resource
itself. Lean-first (no Rocq counterpart).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.third_party.bridge.bridge__serveConn
public import Spec.github_com.mit_pdos.etcd_grove.third_party.bridge.bridge__ioCopy
public import Spec.github_com.mit_pdos.etcd_grove.third_party.bridge.bridgeConn__close
public import Spec.github_com.mit_pdos.etcd_grove.third_party.bridge.bridgeConn__Close
public import Proof.github_com.mit_pdos.etcd_grove.third_party.bridge.Lemmas

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bridgeP

open Iris Iris.BI Iris.ProofMode github_com.mit_pdos.etcd_grove.third_party

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.third_party.bridge.Assumptions]

/-- The local wait group's namespace. -/
def pairWgN : Namespace := nroot.@"bridgePairWg"
/-- The pair's invariant's namespace. -/
def pairN : Namespace := nroot.@"bridgePair"

theorem pairWg_mask : (↑pairWgN : CoPset) ⊆ ⊤ \ ↑pairN :=
  sync.wg_mask_ndot_ne nroot "bridgePairWg" "bridgePair" (by decide)

theorem pairN_mask : (↑pairN : CoPset) ⊆ ⊤ \ ↑pairWgN :=
  sync.wg_mask_ndot_ne nroot "bridgePair" "bridgePairWg" (by decide)

/-- **The two copy goroutines' wait group** (`serveConn`'s `wg`, after its `Add(2)`): the counter is
the number not yet done, and each one done has deposited its resource `Pᵢ` and its token `γᵢ`;
once the waiter claimed them (its token `γc`), the tokens. -/
def pairInv (γw : sync.WaitGroupNames) (γ1 γ2 γc : GName) (P1 P2 : IProp GF) : IProp GF :=
  iprop((∃ (ctr : w32) (d1 d2 : Bool), sync.ownWaitGroup γw ctr ∗
      ⌜sint.Z ctr = (if d1 then 0 else 1) + (if d2 then 0 else 1)⌝ ∗
      (if d1 then P1 ∗ token γ1 else iprop(True)) ∗ (if d2 then P2 ∗ token γ2 else iprop(True))) ∨
    (token γc ∗ token γ1 ∗ token γ2 ∗ ∃ ctr : w32, sync.ownWaitGroup γw ctr))

section pair
variable [sync_sem : sync.Assumptions]

/-- **The first copy goroutine's `wg.Done()`**, with its token and its resource. -/
theorem wp_pair_Done1 (wg : Loc) (γw : sync.WaitGroupNames) (γ1 γ2 γc : GName) (P1 P2 : IProp GF)
    [Timeless P1] [Timeless P2] :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sync ∗ sync.isWaitGroup wg γw pairWgN ∗
        inv pairN (pairInv γw γ1 γ2 γc P1 P2) ∗ token γ1 ∗ P1 }}
      (App (Val (wg @!! go.GoType.PointerType sync.WaitGroup.ty @!! go!"Done")) (Val #()))
    {{ RET #(); True }} := by
  iintro %Φ ⟨#Hsync, #Hwg, #Hinv, Ht, HP⟩ HΦ
  iapply sync.WaitGroup.wp_Done wg γw pairWgN $$ [] [Ht HP HΦ]
  · iframe #
  iinv Hinv with Hi Hclose
  iapply fupd_mask_intro pairWg_mask
  iintro Hmask
  inext
  unfold pairInv
  icases Hi with (⟨%ctr, %d1, %d2, Hwgo, %Hc, H1, H2⟩ | ⟨-, Ht1, -, -⟩)
  · cases d1
    · simp only [Bool.false_eq_true, ↓reduceIte] at Hc ⊢
      have hlt : sint.Z ctr < 2 ^ 31 := by word
      have hz : sint.Z (ctr - W32 1) = sint.Z ctr - 1 := by
        have : 1 ≤ sint.Z ctr := by cases d2 <;> simp at Hc <;> omega
        word
      iexists ctr
      iframe Hwgo
      isplitr
      · ipureintro; cases d2 <;> simp at Hc <;> omega
      iintro Hwgo
      imod Hmask with -
      imod Hclose $$ [Hwgo HP Ht H2] with -
      · inext
        ileft
        iexists ctr - W32 1, true, d2
        simp only [↓reduceIte]
        iframe
        ipureintro; rw [hz, Hc]; omega
      imodintro
      iapply HΦ
      itrivial
    · simp only [↓reduceIte]
      icases H1 with ⟨-, Ht1⟩
      iexfalso
      iapply token_exclusive γ1 $$ Ht Ht1
  · iexfalso
    iapply token_exclusive γ1 $$ Ht Ht1

/-- **The second copy goroutine's `wg.Done()`**, with its token and its resource. -/
theorem wp_pair_Done2 (wg : Loc) (γw : sync.WaitGroupNames) (γ1 γ2 γc : GName) (P1 P2 : IProp GF)
    [Timeless P1] [Timeless P2] :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sync ∗ sync.isWaitGroup wg γw pairWgN ∗
        inv pairN (pairInv γw γ1 γ2 γc P1 P2) ∗ token γ2 ∗ P2 }}
      (App (Val (wg @!! go.GoType.PointerType sync.WaitGroup.ty @!! go!"Done")) (Val #()))
    {{ RET #(); True }} := by
  iintro %Φ ⟨#Hsync, #Hwg, #Hinv, Ht, HP⟩ HΦ
  iapply sync.WaitGroup.wp_Done wg γw pairWgN $$ [] [Ht HP HΦ]
  · iframe #
  iinv Hinv with Hi Hclose
  iapply fupd_mask_intro pairWg_mask
  iintro Hmask
  inext
  unfold pairInv
  icases Hi with (⟨%ctr, %d1, %d2, Hwgo, %Hc, H1, H2⟩ | ⟨-, -, Ht2, -⟩)
  · cases d2
    · simp only [Bool.false_eq_true, ↓reduceIte] at Hc ⊢
      have hlt : sint.Z ctr < 2 ^ 31 := by word
      have hz : sint.Z (ctr - W32 1) = sint.Z ctr - 1 := by
        have : 1 ≤ sint.Z ctr := by cases d1 <;> simp at Hc <;> omega
        word
      iexists ctr
      iframe Hwgo
      isplitr
      · ipureintro; cases d1 <;> simp at Hc <;> omega
      iintro Hwgo
      imod Hmask with -
      imod Hclose $$ [Hwgo HP Ht H1] with -
      · inext
        ileft
        iexists ctr - W32 1, d1, true
        simp only [↓reduceIte]
        iframe
        ipureintro; rw [hz, Hc]; omega
      imodintro
      iapply HΦ
      itrivial
    · simp only [↓reduceIte]
      icases H2 with ⟨-, Ht2⟩
      iexfalso
      iapply token_exclusive γ2 $$ Ht Ht2
  · iexfalso
    iapply token_exclusive γ2 $$ Ht Ht2

/-- **The waiter's `wg.Wait()`**, with the claim token and "no waiters": both resources. -/
theorem wp_pair_Wait (wg : Loc) (γw : sync.WaitGroupNames) (γ1 γ2 γc : GName) (P1 P2 : IProp GF)
    [Timeless P1] [Timeless P2] :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sync ∗ sync.isWaitGroup wg γw pairWgN ∗
        inv pairN (pairInv γw γ1 γ2 γc P1 P2) ∗ token γc ∗ sync.ownWaitGroupWaiters γw 0 }}
      (App (Val (wg @!! go.GoType.PointerType sync.WaitGroup.ty @!! go!"Wait")) (Val #()))
    {{ RET #(); P1 ∗ P2 }} := by
  iintro %Φ ⟨#Hsync, #Hwg, #Hinv, Htc, Hw0⟩ HΦ
  iapply fupd_wp
  imod fupd_mask_subseteq (E1 := ⊤) (E2 := ↑pairWgN) (fun _ _ => CoPset.mem_full) with Hmask
  imod sync.alloc_wait_token wg γw pairWgN 0 (by decide) $$ Hwg Hw0 with ⟨Hw1, Hwtok⟩
  imod Hmask with -
  imodintro
  iapply sync.WaitGroup.wp_Wait wg γw pairWgN $$ [Hwtok] [Htc HΦ]
  · iframe #; iframe
  iinv Hinv with Hi Hclose <;> try exact pairN_mask
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  unfold pairInv
  icases Hi with (⟨%ctr, %d1, %d2, Hwgo, %Hc, H1, H2⟩ | ⟨Htc', -, -, -⟩)
  · iexists ctr
    iframe Hwgo
    iintro %Hz Hwgo
    imod Hmask with -
    have hd1 : d1 = true := by
      cases d1 <;> cases d2 <;> simp only [Bool.false_eq_true, ↓reduceIte] at Hc <;>
        first | rfl | omega
    have hd2 : d2 = true := by
      cases d1 <;> cases d2 <;> simp only [Bool.false_eq_true, ↓reduceIte] at Hc <;>
        first | rfl | omega
    subst hd1 hd2
    simp only [↓reduceIte]
    icases H1 with ⟨HP1, Ht1⟩
    icases H2 with ⟨HP2, Ht2⟩
    imod Hclose $$ [Htc Ht1 Ht2 Hwgo] with -
    · inext
      iright
      iframe
    imodintro
    iintro -
    iapply HΦ
    iframe
  · iexfalso
    iapply token_exclusive γc $$ Htc Htc'

end pair

theorem bridge.serveConn.wp_proof (wp_ioCopy : bridge.ioCopy.spec (GF := GF) (hG := hG))
    (wp_close : bridgeConn.close.spec (GF := GF) (hG := hG))
    (wp_Close : bridgeConn.Close.spec (GF := GF) (hG := hG)) :
    bridge.serveConn.spec (GF := GF) (hG := hG) := by
  intro b γ addr c q γt lo inc outc donec γd ch γbh
  wp_start as ⟨#Hb, Hrun, #Hcf, #Hin, #Hout, Hdp, #Hrc, Hbh, #Hbhc, Hd1, Hd2⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  ihave #Hbi := Hb
  iunfold isBridge at Hbi
  icases Hbi with ⟨%l, %sc, %γsc, #Hd, #Hl, #Hrl, #Hsc, #Hscb, #Hmu, #Hwg, #Hwgi, %Htb⟩
  ihave #Hcf' := Hcf
  iunfold connFields at Hcf'
  icases Hcf' with ⟨#Hci, #Hco, #Hcd⟩
  wp_apply wp_with_defer as %defer defer
  imod sync.init_WaitGroup pairWgN wg_ptr $$ wg with ⟨%γw, #Hwgl, Hctr, Hwait⟩
  imod token_alloc with ⟨%γ1, Ht1⟩
  imod token_alloc with ⟨%γ2, Ht2⟩
  imod token_alloc with ⟨%γc, Htc⟩
  wp_bind (App (Val (wg_ptr @!! go.GoType.PointerType sync.WaitGroup.ty @!! go!"Add")) (Val #(W64 2)))
  iapply (sync.WaitGroup.wp_Add wg_ptr (W64 2) γw pairWgN) $$ [] [Hctr Hwait Ht1 Ht2 Htc Hrun Hdp Hbh Hd1 Hd2 HΦ b bc defer]
  · iframe #
  iapply fupd_mask_intro (fun _ _ => CoPset.mem_full)
  iintro Hmask
  inext
  iexists W32 0
  iframe Hctr
  isplitr
  · ipureintro; decide
  iright
  iframe Hwait
  iintro Hwait Hctr
  imod Hmask with -
  have e := typedPointsto_frac_add (GF := GF) (bF b go!"blackholec") ch q.half q.half
  rw [Qp.half_add_half] at e
  icases e.1 $$ Hbh with ⟨Hq1, Hq2⟩
  imod inv_alloc pairN ⊤ (pairInv γw γ1 γ2 γc (bF b go!"blackholec" ↦{DFrac.own q.half} ch)
      (bF b go!"blackholec" ↦{DFrac.own q.half} ch)) $$ [Hctr] with #Hpair
  · inext
    unfold pairInv
    ileft
    iexists W32 0 + W32 (sint.Z (W64 2)), false, false
    simp only [Bool.false_eq_true, ↓reduceIte]
    iframe
    ipureintro; decide
  imodintro
  ipersist b
  ipersist bc
  wp_auto
  wp_apply wp_fork $$ [Ht1 Hq1 Hd1]
  · wp_auto
    wp_apply wp_ioCopy b q.half ch γbh lo inc outc [] $$ [Hq1 Hd1] as %err Hq1
    · iframe #; iframe
    wp_apply wp_close c inc outc donec $$ []
    · iframe #
    wp_apply wp_pair_Done1 wg_ptr γw γ1 γ2 γc (bF b go!"blackholec" ↦{DFrac.own q.half} ch)
      (bF b go!"blackholec" ↦{DFrac.own q.half} ch) $$ [Ht1 Hq1]
    · iframe #; iframe
    itrivial
  wp_apply wp_fork $$ [Ht2 Hq2 Hd2]
  · wp_auto
    wp_apply wp_ioCopy b q.half ch γbh lo outc inc [] $$ [Hq2 Hd2] as %err Hq2
    · iframe #; iframe
    wp_apply wp_close c inc outc donec $$ []
    · iframe #
    wp_apply wp_pair_Done2 wg_ptr γw γ1 γ2 γc (bF b go!"blackholec" ↦{DFrac.own q.half} ch)
      (bF b go!"blackholec" ↦{DFrac.own q.half} ch) $$ [Ht2 Hq2]
    · iframe #; iframe
    itrivial
  wp_apply wp_pair_Wait wg_ptr γw γ1 γ2 γc (bF b go!"blackholec" ↦{DFrac.own q.half} ch)
      (bF b go!"blackholec" ↦{DFrac.own q.half} ch) $$ [Htc Hwait] as ⟨Hq1, Hq2⟩
  · iframe #; iframe
  ihave Hbh := e.2 $$ [Hq1 Hq2]
  · iframe
  imod inv_alloc bridgeDoneN ⊤ iprop(token γt ∨ ∃ ch' : GoChan,
      bF b go!"blackholec" ↦{DFrac.own q} ch') $$ [Hbh] with #HQi
  · inext; iright; iexists ch; iexact Hbh
  ihave #HQ : doneQ b q γt $$ []
  · unfold doneQ; iexact HQi
  wp_apply wp_broadcast_chan_close donec γd (doneQ b q γt) $$ [$Hdp] as Hdd
  · iframe #
  ihave #Hdu := ownBroadcastChan_Unknown _ _ _ _ $$ Hdd
  ihave #Hco' : connOk b c q γt $$ []
  · unfold connOk; iexists inc, outc, donec, γd; iframe #
  wp_apply wp_Close b c q γt $$ [] as -
  · iframe #
  wp_apply sync.Mutex.wp_Lock $$ [] as ⟨Hlocked, Hi⟩
  · iframe #
  iunfold lockInv at Hi
  icases Hi with ⟨%m, %conns, %shares, %reg, %pc, %bhc, %γpc, %γbh, %holed, %ql, Hconns, Hm, %Hdom,
    Hpausec, #Hpc, Hpcst, Hbh, #Hbhc', Hholed, Hbhst, Hwand, Hregs, Hreg, #Hregf, %Hsub⟩
  wp_auto
  wp_apply wp_mapDelete m conns c (go.GoType.PointerType bridge.bridgeConn.ty)
    (go.GoType.StructType []) $$ [$Hm] as Hm
  icombine Hrc Hreg gives %Hrl
  -- the connection's entry, if still there, taken back
  iapply fupd_wp
  ihave Hrest : iprop(|={⊤}=> ∃ (shares' : GMap Loc (Qp × GName)) (ql' : Qp),
      ⌜∀ c', (GMap.delete c conns !! c').isSome = (shares' !! c').isSome⌝ ∗
      ⌜∀ c' x, shares'.lookup c' = some x → reg.lookup c' = some x⌝ ∗
      bF b go!"blackholec" ↦{DFrac.own ql'} bhc ∗
      (bF b go!"blackholec" ↦{DFrac.own ql'} bhc ∗ sharesPts b bhc shares' -∗
        bF b go!"blackholec" ↦ bhc) ∗
      [∗map] c' ↦ x ∈ shares', connOk b c' x.1 x.2 ∗ token x.2) $$ [Hbh Hwand Hregs]
  · rcases hsh : shares.lookup c with _ | x
    · imodintro
      iexists shares, ql
      iframe
      ipureintro
      refine ⟨fun c' => ?_, Hsub⟩
      by_cases hc : c' = c
      · subst hc
        have h1 := Hdom c'
        rw [GMap.lookup_delete]
        have : shares !! c' = none := hsh
        rw [this] at h1 ⊢
        rfl
      · rw [GMap.lookup_delete_ne _ (Ne.symm hc)]
        exact Hdom c'
    · have hx : x = (q, γt) := by
        have h1 := Hsub c x hsh
        rw [Hrl] at h1
        exact (Option.some.inj h1).symm
      subst hx
      icases (BigSepM.bigSepM_delete (Φ := fun c (x : Qp × GName) =>
        iprop(connOk (GF := GF) b c x.1 x.2 ∗ token x.2)) hsh).1 $$ Hregs with ⟨⟨-, Htok⟩, Hregs⟩
      iinv HQi with Hi Hclose
      imod Hi with (Ht' | ⟨%ch', Hx⟩)
      · iexfalso
        iapply token_exclusive γt $$ Htok Ht'
      imod Hclose $$ [Htok] with -
      · inext; ileft; iexact Htok
      icombine Hbh Hx gives %Heq
      subst Heq
      icases share_in b bhc shares ql c (q, γt) hsh $$ [Hbh Hwand Hx] with ⟨Hbh, Hwand⟩
      · iframe
      imodintro
      iexists shares.delete c, ql + q
      isplitr
      · ipureintro
        intro c'
        by_cases hc : c' = c
        · subst hc; rw [GMap.lookup_delete, GMap.lookup_delete]; rfl
        · rw [GMap.lookup_delete_ne _ (Ne.symm hc), GMap.lookup_delete_ne _ (Ne.symm hc)]
          exact Hdom c'
      isplitr
      · ipureintro
        intro c' x h
        by_cases hc : c' = c
        · subst hc; rw [GMap.lookup_delete] at h; cases h
        · rw [GMap.lookup_delete_ne _ (Ne.symm hc)] at h
          exact Hsub c' x h
      iframe
  imod Hrest with ⟨%shares', %ql', %Hdom', %Hsub', Hbh, Hwand, Hregs⟩
  imodintro
  wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hconns Hm Hpausec Hpcst Hbh Hholed Hbhst Hwand
    Hregs Hreg]
  · iframe #
    iunfold lockInv
    iexists m, GMap.delete c conns, shares', reg, pc, bhc, γpc, γbh, holed, ql'
    iframe
    iframe #
    ipureintro
    exact ⟨Hdom', Hsub'⟩
  wp_apply wp_bridgeWg_Done b γ $$ [Hrun] as Htok
  · iframe #; iframe
  iapply HΦ
  iexact Htok

end proof

end bridgeP
end EtcdGrove
end Perennial
