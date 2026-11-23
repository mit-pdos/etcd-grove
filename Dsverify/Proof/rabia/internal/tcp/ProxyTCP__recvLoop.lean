/-
(Ported from dsverify-lab `examples/rabia/proof/Proof/rabia/internal/tcp/ProxyTCP__recvLoop.lean`,
run `rabia-r1wake-1`, onto `Net/`'s connections and the revised bufio: the reader is `rdOwn`; the
protocol's facts of a request come through `rdOwn_proto` one step later (a later credit).)

The proof of `rabia/internal/tcp.(*ProxyTCP).recvLoop`: the receive routine of one accepted
connection of client `c` reads its requests in order; on the first request (the connection is the
established one) it claims the client's receipts, and passes each request on `ClientsToProxy` with
its receipt.
-/
module

public import Dsverify.Proof.rabia.internal.tcp.ProxyLemmas
public import Perennial.Proof.sync

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.rabia.internal.tcp

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode model Net rabia
  rabia.internal.message rabia.internal.config

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [π : NetProtoGS]
variable [sem : go.Semantics] [package_sem : rabia.internal.tcp.Assumptions]
variable [_root_.Perennial.bufio.Assumptions] [_root_.Perennial.io.Assumptions]
variable [net.Assumptions] [net.FieldAssumptions] [go.BasicIntoValInj]
variable [msg_sem : rabia.internal.message.Assumptions] [sync.Assumptions]

instance pRcpt_timeless (γl : SrvNames) (c n : Nat) : Timeless (pRcpt (GF := GF) γl c n) := by
  unfold pRcpt; infer_instance

instance estab_timeless (γ : Names) (c k : Nat) (cid : Nat) : Timeless (estab (GF := GF) γ c k cid) := by
  unfold estab; infer_instance

theorem rcpt_claim_gen (N : Namespace) (B : IProp GF) [Timeless B] (γ : Names) (c k : Nat)
    (cid : Nat) :
    inv N iprop(B ∨ ∃ cid : Nat, estab (GF := GF) γ c k cid ∗ connFresh (Gg := hG.goose_globalGS) cid true) ∗
      estab γ c k cid ∗ connFresh (Gg := hG.goose_globalGS) cid true ⊢ |={⊤}=> B := by
  iintro ⟨#Hinv, #Hest, Hfresh⟩
  iinv Hinv with Hb Hclose
  icases Hb with (>Hr | >Hr')
  · imod Hclose $$ [Hfresh] with -
    · inext; iright; iexists cid; iframe Hfresh; iexact Hest
    imodintro; iexact Hr
  · icases Hr' with ⟨%cid', #Hest', Hfresh'⟩
    unfold estab
    ihave %Heq := ghostMapElem_agree $$ Hest Hest'
    cases Heq
    iexfalso
    iapply connFresh_excl $$ [$Hfresh $Hfresh']

/-- The receive routine of client `c`'s established connection `cid` claims its receipts (once:
its fresh token). -/
theorem rcpt_claim (γ : Names) (k : Nat) (γl : SrvNames) (c : Nat) (cid : Nat) :
    inv (rcptN k c) (rcptBody (GF := GF) γ k γl c) ∗ estab γ c k cid ∗
      connFresh (Gg := hG.goose_globalGS) cid true ⊢
      |={⊤}=> [∗list] n ∈ List.range opBudget, pRcpt γl c n :=
  rcpt_claim_gen (rcptN k c) _ γ c k cid

theorem range'_split (nx s m : Nat) (h1 : nx ≤ s) (h2 : s < m) :
    List.range' nx (m - nx) = List.range' nx (s - nx) ++ s :: List.range' (s + 1) (m - (s + 1)) := by
  rw [show m - nx = (s - nx) + ((m - (s + 1)) + 1) by omega, ← List.range'_append]
  simp only [Nat.one_mul, show nx + (s - nx) = s by omega]
  rfl

theorem range'_pop (j m : Nat) (h : j < m) :
    List.range' j (m - j) = j :: List.range' (j + 1) (m - (j + 1)) := by
  rw [show m - j = (m - (j + 1)) + 1 by omega]
  rfl

set_option goose.wp.extras true

theorem wp_ProxyTCP_recvLoop (D : TcpDeps (GF := GF)) (γ : Names) (cf : RCfg) (k : Nat) (γl : SrvNames) (p : Loc) (c : Nat)
    (hc : c < nC) (hck : c % cf.n = k) (br : Loc) (cid : Nat) (toProxy : GoChan) (wg : Loc) :
  {{ isPkgInit (PROP := IProp GF) pkg_id.rabia.internal.tcp ∗
      p.[ProxyTCP, go!"RecvChan"] ↦□ toProxy ∗ isChanBag γl.c2p toProxy (c2pP γ cf k γl) ∗
      p.[ProxyTCP, go!"Wg"] ↦□ wg ∗ wgTok wg ∗
      rdOwn br cid true (proxyP γ k) (hsBytes c) ∗
      connFresh (Gg := hG.goose_globalGS) cid true ∗ inv (rcptN k c) (rcptBody γ k γl c) }}
    (App (Val (p @!! go.GoType.PointerType ProxyTCP.ty @!! go!"recvLoop")) (Val #br))
  {{ RET #(); True }} := by
  wp_start as ⟨#HRC, #Hbag, #HWg, Htok, Hbr, Hfresh, #Hinv⟩
  wp_apply wp_with_defer as %defer Hdefer
  wp_apply (wp_slice_make2 (V := w8) _) as %sl ⟨Hsl, -⟩
  · ipureintro; decide
  ihave %Hsl0 := ownSlice_len _ _ _ $$ Hsl
  have hsl : sint.nat sl.len = 409600 := by rw [← Hsl0.1, List.length_replicate]
  ihave HI : (∃ (qs : List CmdV) (ds : List w8), "Hsl" ∷ sl ↦* ds ∗
      "Hbr" ∷ rdOwn br cid true (proxyP γ k) (hsBytes c ++ frames (qs.map encCmd)) ∗
      "%Hqs" ∷ ⌜∀ q ∈ qs, (encCmd q).length < 2 ^ 32⌝ ∗
      "Hst" ∷ ((⌜qs = []⌝ ∗ connFresh (Gg := hG.goose_globalGS) cid true) ∨
        (∃ nx, ⌜qs ≠ [] ∧ nx ≤ opBudget ∧ (∀ q' ∈ qs, q'.cliSeq.toNat < nx) ∧
          ∃ q' ∈ qs, q'.cliSeq.toNat + 1 = nx⌝ ∗
          [∗list] n ∈ List.range' nx (opBudget - nx), pRcpt γl c n)) :
      IProp GF) $$ [Hsl Hbr Hfresh]
  · iexists [], _
    simp only [List.map_nil, frames_nil, List.append_nil]
    iframe
    isplitr
    · ipureintro; simp
    ileft; iframe
  wp_for HI
  ihave %Hdl := ownSlice_len _ _ _ $$ Hsl
  have hdl : ds.length = 409600 := by rw [Hdl.1, hsl]
  ihave #HF := proxyP_frameIs γ k cid c hc qs Hqs
  ihave #Hpkgm : (isPkgInit (PROP := IProp GF) pkg_id.rabia.internal.message) $$ []
  · iPkgInit
  wp_apply wp_cmdReadUnmarshal D c_ptr br cid true (proxyP γ k) _ sl ds $$ [$Hpkgm $c $Hbr $HF $Hsl]
    as %e ⟨%ds', Hsl, Hres⟩
  icases Hres with (⟨%He, %v, %q, %Hq, Hcmd, #Hrep, Hbr⟩ | ⟨%He, %R', %v, %HR', Hcmd, Hbr⟩)
  · subst He
    have Hq' : (encCmd q).length < 2 ^ 32 := by omega
    wp_auto_lc 1
    ihave ⟨Hbr, Hpp⟩ := rdOwn_proto br cid true (proxyP γ k) _ $$ Hbr
    iapply fupd_wp
    imod (lc_fupd_elim_later (GF := GF) (E := ⊤)) $$ Hlc1 Hpp with #Hpp
    imodintro
    ihave ⟨%Hseq, #Hreq, #Hest⟩ := proxyP_read γ k cid c hc qs Hqs q Hq' $$ Hpp
    -- the receipts: claimed at the first request; the requests' numbers increase
    ihave Hrs : |={⊤}=> ∃ nx, ⌜nx ≤ q.cliSeq.toNat⌝ ∗
        [∗list] n ∈ List.range' nx (opBudget - nx), pRcpt γl c n $$ [Hst]
    · icases Hst with (⟨%Hnil, Hfresh⟩ | ⟨%nx, %Hnx, Hrs⟩)
      · subst Hnil
        iexists 0
        simp only [Nat.sub_zero, ← List.range_eq_range']
        isplitr
        · ipureintro; omega
        iapply rcpt_claim γ k γl c cid $$ [$Hinv $Hest $Hfresh]
      · imodintro
        iexists nx
        iframe Hrs
        ipureintro
        obtain ⟨-, -, -, q', hq', hnx⟩ := Hnx
        have := Hseq.2 q' hq'
        omega
    imod Hrs with ⟨%nx, %Hnx, Hrs⟩
    rw [range'_split nx q.cliSeq.toNat opBudget Hnx Hseq.1]
    icases BigSepL.bigSepL_append.1 $$ Hrs with ⟨-, Hrs⟩
    icases BigSepL.bigSepL_cons.1 $$ Hrs with ⟨Hr, Hrs⟩
    wp_apply wp_bag_send γl.c2p toProxy v (c2pP γ cf k γl) $$ [$Hbag Hr]
    · unfold c2pP
      iexists c, q
      iframe #
      iframe Hr
      ipureintro
      exact ⟨hc, hck, Hseq.1, by unfold cmdBound; omega⟩
    wp_for_post
    iframe
    iexists qs ++ [q], ds'
    simp only [List.map_append, List.map_cons, List.map_nil, frames_append, frames_cons, frames_nil,
      List.append_nil, List.append_assoc, List.length_append, List.length_singleton]
    iframe
    isplitr
    · ipureintro
      intro r hr
      simp only [List.mem_append, List.mem_singleton] at hr
      rcases hr with hr | rfl
      · exact Hqs r hr
      · exact Hq'
    iright
    iexists q.cliSeq.toNat + 1
    isplitr
    · ipureintro
      refine ⟨by simp, by omega, ?_, q, by simp, rfl⟩
      intro r hr
      simp only [List.mem_append, List.mem_singleton] at hr
      rcases hr with hr | rfl
      · have := Hseq.2 r hr; omega
      · omega
    iexact Hrs
  · rcases e with ei | _
    · wp_auto
      wp_for_post
      wp_apply wp_wgDone wg $$ [$Htok]
      iapply HΦ
      itrivial
    · exact absurd rfl He

end proof

end Perennial.rabia.internal.tcp
