/-
Lean-first (no Rocq counterpart). keepfix (c), 2026-11-27: the ghost lemmas of raft's boot law
(`raftBootFix.law`, `~/coordinator-notes/plans/raft-boot-law-brief.md`, the sub-lemma
decomposition): the commit certificate's term bound on its log (L1a) and the commit raised to a
committed index at a larger term (L3).
-/
module

public import Proof.go_etcd_io.raft.v3.Protocol.GhostState

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI GMap go_etcd_io.raft.v3

section ghost
variable [GooseExts]
variable {GF : BundledGFunctors} [AllG GF] [ReceiptGS GF] [InvGS GF]

/-- (L1a) **A commit certificate at a nonzero term `tm` bounds the terms of its log up to the
commit index**: by the bootstrap log (terms `1`) or by the certifying leader's log (`cq` at a term
`≤ tm`, which agrees with `F` below `c`: full-log matching), whose terms are at most its term. -/
theorem commitIn_termLe (γ : RaftNames) (F : List EntryM) (c tm : w64) :
    PlogWf base0 F → uint.Z tm ≠ 0 →
    ⊢ logRecs (GF := GF) γ base0 F -∗ commitIn γ F c tm -∗
      ⌜∀ (j x : w64), uint.Z j ≤ uint.Z c → plogTermAt base0 F j = some x → uint.Z x ≤ uint.Z tm⌝ := by
  intro Hwf Htm
  iintro #Hr #Hc
  ihave #Hj := commitIn_j γ F c tm $$ Hc
  unfold commitJ
  icases Hj with (%Hb | ⟨%t', %n, %G, #Hcq, %Hcn⟩)
  · -- the bootstrap log's prefix: every entry of term `1`
    icases logRecs_boot γ F Hwf $$ Hr with %HB
    ipureintro
    intro j x Hjc Hx
    have Hrng := plogTermAt_some_range _ _ _ _ Hx
    rw [base0_index] at Hrng
    by_cases Hj0 : uint.Z j = 0
    · -- the boundary: term `0`
      have : plogTermAt base0 F j = some (W64 0) := by
        unfold plogTermAt; rw [base0_index]
        simp only [show ¬ (uint.Z j < 0) by omega, Hj0, ↓reduceIte]; rfl
      rw [this] at Hx; cases Hx; word
    obtain ⟨e, He⟩ : ∃ e, F[(uint.Z j - 1).toNat]? = some e := by
      unfold plogLastIndexZ at Hrng; rw [base0_index] at Hrng
      exact ⟨_, List.getElem?_eq_getElem (by omega)⟩
    have Hxe : x = e.Term' := by
      unfold plogTermAt at Hx; rw [base0_index] at Hx
      simp only [show ¬ (uint.Z j < 0) by omega, Hj0, ↓reduceIte] at Hx
      rw [show (uint.Z j - 0 - 1).toNat = (uint.Z j - 1).toNat by omega, He] at Hx
      simp at Hx; exact Hx.symm
    have := (HB _ e He (by omega)).2
    rw [Hxe, this]; word
  · -- a certificate: the leader's log agrees with `F` up to `c`, its terms at most `t' ≤ tm`
    obtain ⟨Hcn, Htt, Hag⟩ := Hcn
    icases cq_base γ t' n G $$ Hcq with ⟨%HGn, #Hf⟩
    icases leadFull_wf γ t' G $$ Hf with ⟨%HGp, #HGr⟩
    obtain ⟨HGwf, HGt⟩ := HGp
    have HGrng := plogTermAt_some_range _ _ _ _ HGn
    have HGc : (plogTermAt base0 G c).isSome :=
      plogTermAt_in_range base0 G c ⟨by rw [base0_index]; exact uint_Z_nonneg c, by omega⟩
    icases full_match γ G F c HGwf Hwf HGc Hag $$ HGr Hr with %HM
    ipureintro
    intro j x Hjc Hx
    have := HGt j x (by rw [HM j Hjc]; exact Hx)
    omega

/-- (L1a) **A commit certificate's log reaches its commit index**: the certifying log (the
bootstrap log, or the leader's, which reaches its quorum index `n ≥ c`) has a term at `c`, and `F`
has the same. -/
theorem commitIn_has (γ : RaftNames) (F : List EntryM) (c tm : w64) :
    ⊢ commitIn (GF := GF) γ F c tm -∗ ⌜(plogTermAt base0 F c).isSome⌝ := by
  iintro #Hc
  ihave #Hj := commitIn_j γ F c tm $$ Hc
  unfold commitJ
  icases Hj with (%Hb | ⟨%t', %n, %G, #Hcq, %Hcn⟩)
  · ipureintro
    rw [← Hb.2]
    exact plogTermAt_in_range base0 γ.reBoot c
      ⟨by rw [base0_index]; exact uint_Z_nonneg c,
       by unfold plogLastIndexZ; rw [base0_index]; omega⟩
  · obtain ⟨Hcn, -, Hag⟩ := Hcn
    icases cq_base γ t' n G $$ Hcq with ⟨%HGn, -⟩
    have HGrng := plogTermAt_some_range _ _ _ _ HGn
    ipureintro
    rw [← Hag]
    exact plogTermAt_in_range base0 G c ⟨by rw [base0_index]; exact uint_Z_nonneg c, by omega⟩

/-- (L3) **The commit raised to a committed index at a larger term, on a log agreeing there**: a
certificate of `F` at `c ≥ ci` and term `tm ≤ tm'`, for a log `F'` with records agreeing with `F`
at `ci`. -/
theorem commitIn_boot (γ : RaftNames) (F F' : List EntryM) (c ci tm tm' : w64) :
    PlogWf base0 F → PlogWf base0 F' → uint.Z ci ≤ uint.Z c → uint.Z tm ≤ uint.Z tm' →
    (plogTermAt base0 F ci).isSome → plogTermAt base0 F' ci = plogTermAt base0 F ci →
    ⊢ logRecs (GF := GF) γ base0 F -∗ logRecs γ base0 F' -∗ commitIn γ F c tm -∗
      commitIn γ F' ci tm' := by
  intro Hw Hw' Hle Htm Hs Heq
  iintro #Hr #Hr' #Hc
  ihave #Hc' := commitIn_le γ F c ci tm Hw Hle $$ Hr Hc
  iapply commitIn_move γ F F' ci tm tm' Htm Hw Hw' Hs Heq $$ Hr Hr' Hc'

/-- (L4) **The durable invariants across a term raise with the vote cleared and the new term's
campaign key closed** (no node running: the boot step's raise): every promise is of a term `≤
S.term < T`, so the vote map has no key `T`, the acknowledgements none at `T`, and the histories'
bound grows (`hist_mono`); the closed key gives the campaign link (`campNone`'s empty log) and the
closure. -/
theorem durPers_raise (γ : RaftNames) (id : w64) (S : RaftState) (E : DurMaps) (T : w64) :
    uint.Z S.term < uint.Z T →
    durPers (GF := GF) γ id S E ⊢
      durPers γ id { S with term := T, vote := W64 0 } (E.add (.close T)) := by
  intro HT
  iintro #Hd
  iunfold durPers at Hd
  icases Hd with ⟨%kd, %fp, %Hp, #HrS, #Hb, #Hfp, #Hvl, #Hhs, -, -, #Hci, #Hc, #Hinv, #Hai, -, -⟩
  obtain ⟨Hvh, Hak, Hcp, Hev, Hfull, Hwf, Hterms, Hbc, Hcl⟩ := Hp
  have Hfresh : E.camps !! T = none := by
    cases h : E.camps !! T with
    | none => rfl
    | some x => exfalso; have := Hcp T (by rw [h]; rfl); omega
  have Hvfresh : E.voted !! T = none := by
    cases h : E.voted !! T with
    | none => rfl
    | some x => exfalso; have := Hvh.1 T (by rw [h]; rfl); omega
  unfold durPers
  simp only [DurMaps.add, klOkD]
  iexists none, fp
  isplitr
  · ipureintro
    refine ⟨⟨fun t h => ?_, ?_⟩, fun k h => ?_, fun T' h => ?_, ?_, Hfull, Hwf,
      fun j x h => ?_, Hbc, Hcl⟩
    · have := Hvh.1 t h; simp only; omega
    · simp [Hvfresh]
    · have := Hak k h; (try simp only); omega
    · by_cases hT : T = T'
      · subst hT; (try simp only); omega
      · rw [GMap.lookup_insert_ne _ _ hT] at h; have := Hcp T' h; (try simp only); omega
    · obtain ⟨a, b, c, d⟩ := Hev
      exact ⟨a, fun e he => by have := b e he; (try simp only); omega, c, d⟩
    · have := Hterms j x h; (try simp only); omega
  isplitr; · iexact HrS
  isplitr; · iexact Hb
  isplitr; · iexact Hfp
  isplitr
  · iapply BigSepM.bigSepM_impl $$ Hvl
    iintro !> %k %x %_ ⟨%Hx, #H⟩
    isplitr; · ipureintro; omega
    iexact H
  isplitr
  · iapply BigSepM.bigSepM_impl $$ Hhs
    iintro !> %k %_u %_ #H
    iapply hist_mono γ _ k.1 k.2 (bndD S kd) _ ?_ $$ H
    unfold bndD; cases kd <;> simp only <;> omega
  isplitr; · ipureintro; trivial
  isplitr
  · iapply BigSepM.bigSepM_impl $$ Hhs
    iintro !> %k %_u %Hk -
    iintro %Hkt
    exfalso
    have Hk' : E.acks !! k = some _u := Hk
    have h2 := Hak k (by rw [Hk']; rfl)
    have h1 : k.1 = T := Hkt.1
    rw [h1] at h2; omega
  isplitr
  · iapply commitIn_agree γ (fp ++ S.ents) (fp ++ S.ents) S.commit S.term T (by omega) rfl rfl $$ Hci
  isplitr; · iexact Hc
  isplitr; · iexact Hinv
  isplitr
  · iintro !> #Hf
    iapply Hai
    iapply durFrags_mono γ id E
      { voted := E.voted, acks := E.acks, camps := <[T := campNone]> E.camps, vlogs := E.vlogs,
        evs := E.evs } (DurLe_add E (.close T) Hfresh) $$ Hf
  isplitr
  · iapply campLink_close γ id E.camps T
    iapply campLink_none γ id E.camps T _ Hfresh
  · ipureintro; right; simp

/-- (L5) **The durable invariants across a commit raise within the log** (branch A of the boot
step: the log holds the committed entry at `ci`): a certificate of a log `F` with records at `c ≥ ci`
and a term `≤ S.term`, agreeing with `S`'s log at `ci`, gives `ci`'s certificate in `S`'s full log
(`commitIn_boot`) and its committed prefix (`full_take_eq`); the acknowledgements above `ci` are
among those above `S.commit`. -/
theorem durPers_commitRaise (γ : RaftNames) (id : w64) (S : RaftState) (E : DurMaps)
    (F : List EntryM) (ci c tm : w64) :
    uint.Z S.commit ≤ uint.Z ci → (plogTermAt S.base S.ents ci).isSome →
    PlogWf base0 F → uint.Z ci ≤ uint.Z c → uint.Z tm ≤ uint.Z S.term →
    plogTermAt base0 F ci = plogTermAt S.base S.ents ci →
    durPers (GF := GF) γ id S E ∗ logRecs γ base0 F ∗ commitIn γ F c tm ∗
        isCommitted γ (F.take (uint.Z c).toNat) ⊢
      durPers γ id { S with commit := ci } E := by
  intro Hsc Hsome HwF Hcic Htm HagF
  iintro ⟨#Hd, #HrF, #HcF, #HkF⟩
  iunfold durPers at Hd
  icases Hd with ⟨%kd, %fp, %Hp, #HrS, #Hb, #Hfp, #Hvl, #Hhs, #Hkl, #Haa, -, -, #Hinv, #Hai, #Hcl, %Hclo⟩
  obtain ⟨Hvh, Hak, Hcp, Hev, Hfull, Hwf, Hterms, Hbc, Hcl2⟩ := Hp
  have HwFull := full_wf _ _ _ Hfull Hwf
  ihave #HrFull := logRecs_full γ S.base fp S.ents Hfull $$ Hfp HrS
  obtain ⟨x, Hx⟩ := Option.isSome_iff_exists.mp Hsome
  have Hrng := plogTermAt_some_range _ _ _ _ Hx
  have Hfat : plogTermAt base0 (fp ++ S.ents) ci = plogTermAt S.base S.ents ci :=
    full_term_at _ _ _ _ Hfull Hrng.1
  have HsomeF : (plogTermAt base0 F ci).isSome := by rw [HagF]; exact Hsome
  have hbnd : bndD { S with commit := ci } kd = bndD S kd := by cases kd <;> rfl
  have hkl : klOkD (GF := GF) γ id { S with commit := ci } kd = klOkD γ id S kd := by cases kd <;> rfl
  unfold durPers
  iexists kd, fp
  rw [hbnd, hkl]
  dsimp only
  isplitr
  · ipureintro
    exact ⟨Hvh, Hak, Hcp, Hev, Hfull, Hwf, Hterms, by omega, by omega⟩
  isplitr; · iexact HrS
  isplitr; · iexact Hb
  isplitr; · iexact Hfp
  isplitr; · iexact Hvl
  isplitr; · iexact Hhs
  isplitr; · iexact Hkl
  isplitr
  · iapply BigSepM.bigSepM_impl $$ Haa
    iintro !> %k %_u %_ #H %Hk
    iapply H
    exact ⟨Hk.1, by have := Hk.2; omega⟩
  isplitr
  · iapply commitIn_boot γ F (fp ++ S.ents) c ci tm S.term HwF HwFull Hcic Htm HsomeF
      (by rw [Hfat, HagF]) $$ HrF HrFull HcF
  isplitr
  · icases full_take_eq γ F (fp ++ S.ents) ci HwF HwFull HsomeF (by rw [Hfat, HagF]) $$ HrF HrFull
      with %Htk
    rw [← Htk]
    iapply isCommitted_mono γ (F.take (uint.Z ci).toNat) (F.take (uint.Z c).toNat)
      (List.take_prefix_take_left (by omega)) $$ HkF
  isplitr; · iexact Hinv
  isplitr; · iexact Hai
  isplitr; · iexact Hcl
  ipureintro; exact Hclo

/-- The durable state of branch B of the boot step (`raftBootFix`'s second case, the term raised
to `Tn`): the empty log at the base `(t, ci)`. -/
def bootSnapState (Tn t ci : w64) : RaftState :=
  { term := Tn, vote := W64 0, base := entryID.mk t ci, ents := [], commit := ci, wcommit := ci }

/-- A full log's prefix of length `n` has its terms at the indices up to `n`. -/
theorem plogTermAt_take_base0 (F : List EntryM) (n : Nat) (j : w64) (h : uint.Z j ≤ n) :
    plogTermAt base0 (F.take n) j = plogTermAt base0 F j := by
  unfold plogTermAt
  simp only [base0_index]
  by_cases h1 : uint.Z j < 0
  · simp [h1]
  by_cases h2 : uint.Z j = 0
  · simp [h1, h2]
  simp only [h1, h2, ↓reduceIte]
  rw [List.getElem?_take, if_pos (by omega)]

/-- A full log's prefix of length `ci` has no term past `ci`. -/
theorem plogTermAt_take_none (F : List EntryM) (ci j : w64) (h : uint.Z ci < uint.Z j) :
    plogTermAt base0 (F.take (uint.Z ci).toNat) j = none := by
  have := uint_Z_nonneg ci
  unfold plogTermAt
  simp only [base0_index, show ¬ (uint.Z j < 0) by omega, show ¬ (uint.Z j = 0) by omega,
    ↓reduceIte]
  rw [List.getElem?_take, if_neg (by omega)]
  rfl

/-- Histories across a cut at `L`: the new log `F'` is `Y` up to `L` and empty past it, `Y` is
an `okL` log at every index up to `L`, and the old log `F` disagreed with `Y` at `L`
(`hist_replace` with the replaced range starting at `1` and an `okL` log in place of a leader's).
-/
theorem hist_cut (γ : RaftNames) (F F' Y : List EntryM) (t i : w64) (B B' : Int) (L : w64) :
    B ≤ B' → 0 < uint.Z L →
    (∀ j : w64, uint.Z j ≤ uint.Z L →
       plogTermAt base0 F' j = plogTermAt base0 Y j ∧ (plogTermAt base0 Y j).isSome) →
    plogTermAt base0 F L ≠ plogTermAt base0 Y L →
    (∀ j : w64, uint.Z L < uint.Z j → plogTermAt base0 F' j = none) →
    ⊢ (∀ (j : w64), ∀ (_ : uint.Z j ≤ uint.Z L), okL (GF := GF) γ t B' j Y) -∗
      hist γ F t i B -∗ hist γ F' t i B' := by
  intro HB HL Hmid Hdiff Hhigh
  iintro #HY #Hh
  unfold hist
  iintro %j %Hj
  by_cases HjL : uint.Z j ≤ uint.Z L
  · obtain ⟨Heq, Hs⟩ := Hmid j HjL
    ileft; iexists Y
    isplitr; · iapply HY $$ %j %HjL
    ipureintro; rw [Heq]; exact ⟨Hs, rfl⟩
  · iright
    have HsY := (Hmid L (Int.le_refl _)).2
    icases Hh $$ %L %(⟨HL, by omega⟩ : 0 < uint.Z L ∧ uint.Z L ≤ uint.Z i) with
      (⟨%X, #HX, %Hs⟩ | ⟨%j', %X1, %X2, %Hj', #H1, #H2, %Hd⟩)
    · iexists L, X, Y
      isplitr; · ipureintro; omega
      isplitr; · iapply okL_mono γ t B B' L X HB $$ HX
      isplitr; · iapply HY $$ %L %(Int.le_refl _)
      ipureintro; exact ⟨Hs.1, HsY, by rw [Hs.2]; exact Hdiff⟩
    · iexists j', X1, X2
      isplitr; · ipureintro; omega
      isplitr; · iapply okL_mono γ t B B' j' X1 HB $$ H1
      isplitr; · iapply okL_mono γ t B B' j' X2 HB $$ H2
      ipureintro; exact Hd

/-- A node whose votes are all of terms below `T` is in no quorum that won `T`: a member's vote
for the winner would be in its vote map (`durShares`'s authority). -/
theorem durShares_noVote (γ : RaftNames) (id : w64) (Q : Qp) (E : DurMaps) (ldr T : w64)
    (q : GSet w64) :
    (∀ t, (E.voted !! t).isSome → uint.Z t < uint.Z T) →
    ⊢ durShares (GF := GF) γ id Q E -∗ isWin γ ldr T q -∗ ⌜id ∉ q⌝ ∗ durShares γ id Q E := by
  intro Hlt
  iintro Hsh #Hw
  by_cases hq : id ∈ q
  · ihave #Hvs := isWin_votes γ ldr T q $$ Hw
    ihave #Hv := BigSepM.bigSepM_lookup (Φ := fun v _ => isVote (GF := GF) γ v T ldr)
      ((GMap.elem_of_gset _ _).mp hq) $$ Hvs
    unfold durShares isVote
    icases Hsh with ⟨%γv, %γa, %γc, %γl, %γe, %Hn, Hv', Ha, Hc, Hl, He⟩
    icases Hv with ⟨%γv', %Hγv', #Hf⟩
    rw [Hn.1] at Hγv'; cases Hγv'
    ihave %Hk := ghost_map_lookup $$ Hv' Hf
    have := Hlt T (by rw [Hk]; rfl)
    exact absurd this (Int.lt_irrefl _)
  · iframe Hsh
    ipureintro; exact hq

/-- (L6b, one acknowledgement, a certificate `cq t' n G` with `ci ≤ c ≤ n`) The cut keeps a
history: `G` agrees with `F` up to `c` and is an `okL` log of `t` at every index up to `ci` -- as
the leader's log of `t' ≥ t`, or as a committed log of `t' < t`. -/
theorem bootB_hist_cert (γ : RaftNames) (Fo F G : List EntryM) (ci c n t' t Ta i : w64)
    (B B' : Int) :
    B ≤ B' → uint.Z t' < B' → 0 < uint.Z ci → uint.Z ci ≤ uint.Z c → uint.Z c ≤ uint.Z n →
    plogTermAt base0 F ci = some t → plogTermAt base0 Fo ci ≠ some t →
    (∀ j : w64, uint.Z j ≤ uint.Z c → plogTermAt base0 G j = plogTermAt base0 F j) →
    ⊢ cq (GF := GF) γ t' n G -∗ hist γ Fo Ta i B -∗ hist γ (F.take (uint.Z ci).toNat) Ta i B' := by
  intro HB Ht' Hci0 Hcic Hcn HtF Hdiff HM
  iintro #Hcq #Hh
  icases cq_base γ t' n G $$ Hcq with ⟨-, #Hf⟩
  ihave #HY : (∀ (j : w64), ∀ (_ : uint.Z j ≤ uint.Z ci), okL (GF := GF) γ Ta B' j G) $$ []
  · iintro %j %Hj
    unfold okL
    by_cases Hta : uint.Z Ta ≤ uint.Z t'
    · ileft; iexists t'
      isplitr; · ipureintro; omega
      iexact Hf
    · iright; ileft; iexists t', n
      isplitr; · ipureintro; omega
      iexact Hcq
  iapply hist_cut γ Fo (F.take (uint.Z ci).toNat) G Ta i B B' ci HB Hci0
    (fun j hj => by
      rw [plogTermAt_take_base0 F _ j (by omega), HM j (by omega)]
      exact ⟨rfl, full_term_at_some F j ci (by rw [HtF]; rfl) hj⟩)
    (by rw [HM ci Hcic, HtF]; exact Hdiff)
    (fun j hj => plogTermAt_take_none F ci j hj) $$ HY Hh

/-- (L6b, one acknowledgement, the certificate the bootstrap log, `ci` within it) The cut keeps a
history: `F`'s prefix is the bootstrap log's, an `okL` log at every index within it. -/
theorem bootB_hist_boot (γ : RaftNames) (Fo F : List EntryM) (ci t Ta i : w64) (B B' : Int) :
    B ≤ B' → 0 < uint.Z ci → uint.Z ci ≤ γ.reBoot.length →
    plogTermAt base0 F ci = some t → plogTermAt base0 Fo ci ≠ some t →
    F.take (uint.Z ci).toNat = γ.reBoot.take (uint.Z ci).toNat →
    ⊢ hist (GF := GF) γ Fo Ta i B -∗ hist γ (F.take (uint.Z ci).toNat) Ta i B' := by
  intro HB Hci0 Hcib HtF Hdiff Htk
  iintro #Hh
  ihave #HY : (∀ (j : w64), ∀ (_ : uint.Z j ≤ uint.Z ci), okL (GF := GF) γ Ta B' j γ.reBoot) $$ []
  · iintro %j %Hj
    unfold okL
    iright; iright
    ipureintro; exact ⟨by omega, rfl⟩
  have HB' : ∀ j : w64, uint.Z j ≤ uint.Z ci →
      plogTermAt base0 γ.reBoot j = plogTermAt base0 F j := fun j hj => by
    rw [← plogTermAt_take_base0 F (uint.Z ci).toNat j (by omega), Htk,
      plogTermAt_take_base0 _ (uint.Z ci).toNat j (by omega)]
  iapply hist_cut γ Fo (F.take (uint.Z ci).toNat) γ.reBoot Ta i B B' ci HB Hci0
    (fun j hj => by
      rw [plogTermAt_take_base0 F _ j (by omega), HB' j hj]
      exact ⟨rfl, full_term_at_some F j ci (by rw [HtF]; rfl) hj⟩)
    (by rw [HB' ci (Int.le_refl _), HtF]; exact Hdiff)
    (fun j hj => plogTermAt_take_none F ci j hj) $$ HY Hh

/-- (L6b, design N3) **The acknowledgements' histories in branch B**: the full log replaced by the
committed prefix `F.take ci` of a certified log `F` (certificate at `c ≥ ci`, term `rt ≤ Tn`), where
the old full log disagrees with `F` at `ci` (`plogTermAt S.base S.ents ci ≠ some t`), at the raised
term `Tn > S.term` with the vote cleared; the old base is at most `ci`, so the old full log
disagrees with `F` at `ci`. Each entered acknowledgement `(T_a, i)` keeps its history (`hist_cut`,
from an `okL` log agreeing with `F` through `ci`: the bootstrap log, or the certificate's log, as its
leader's log when `T_a ≤ t'` and as a committed log when `t' < T_a`); a known leader `kd'` of `Tn`
when the certificate's term is `Tn` (`klOkD`: the node has no vote at `Tn`, `durShares_noVote`).
Opens no invariant. -/
theorem bootB_hists (Em : CoPset) (γ : RaftNames) (id : w64) (S : RaftState) (E : DurMaps)
    (kd : Option w64) (fp F : List EntryM) (ci c rt Tn t : w64) :
    ↑(raftN γ) ⊆ Em →
    FullOk S.base fp → PlogWf S.base S.ents → PlogWf base0 F →
    uint.Z S.commit < uint.Z ci → uint.Z ci ≤ uint.Z c →
    plogTermAt base0 F ci = some t → plogTermAt S.base S.ents ci ≠ some t →
    uint.Z S.term < uint.Z Tn → uint.Z rt ≤ uint.Z Tn →
    (∀ k, (E.acks !! k).isSome → uint.Z k.1 ≤ uint.Z S.term) →
    VoteHistOkD E.voted S → uint.Z S.base.index' ≤ uint.Z ci →
    ⊢ raftCommitInv (GF := GF) γ -∗ logRecs γ base0 F -∗ commitIn γ F c rt -∗
      isCommitted γ (F.take (uint.Z c).toNat) -∗
      logRecs γ base0 fp -∗ logRecs γ S.base S.ents -∗
      isCommitted γ ((fp ++ S.ents).take (uint.Z S.commit).toNat) -∗
      durFrags γ id E -∗ □ (durFrags γ id E -∗ [∗map] k ↦ _u ∈ E.acks, ackInF γ k.1 k.2) -∗
      ([∗map] k ↦ _u ∈ E.acks, hist γ (fp ++ S.ents) k.1 k.2 (bndD S kd)) -∗
      durShares γ id (1 : Qp).half E ={Em}=∗
      durShares γ id (1 : Qp).half E ∗ ∃ kd' : Option w64,
        klOkD γ id (bootSnapState Tn t ci) kd' ∗
        [∗map] k ↦ _u ∈ E.acks,
          hist γ (F.take (uint.Z ci).toNat) k.1 k.2 (bndD (bootSnapState Tn t ci) kd') := by
  intro _HEm Hfull _Hwf HwF Hsc Hcic HtF HtS HT HrT Hak Hvh Hbi
  iintro - #HrF #HcF - - - - - - Hhs Hsh
  have Hci0 : 0 < uint.Z ci := by have := uint_Z_nonneg S.commit; omega
  have Hdiff : plogTermAt base0 (fp ++ S.ents) ci ≠ some t := by
    rw [full_term_at _ _ _ _ Hfull Hbi]; exact HtS
  have HBle : bndD S kd ≤ uint.Z Tn := by unfold bndD; cases kd <;> simp only <;> omega
  ihave #Hj := commitIn_j γ F c rt $$ HcF
  iunfold commitJ at Hj
  icases Hj with (%Hb | ⟨%t', %n, %G, #Hcq, %Hcn⟩)
  · -- the bootstrap log: `F`'s prefix up to `ci` is the bootstrap log's
    icases logRecs_boot_take γ F HwF $$ HrF with %Htk0
    have HtR := plogTermAt_some_range _ _ _ _ HtF
    unfold plogLastIndexZ at HtR; rw [base0_index] at HtR
    have Htk := Htk0 (uint.Z ci).toNat (by omega) (by omega)
    imodintro
    iframe Hsh
    iexists none
    isplitr; · unfold klOkD; ipureintro; trivial
    iapply BigSepM.bigSepM_impl $$ Hhs
    iintro !> %k %_u %_Hk #Hh
    iapply bootB_hist_boot γ (fp ++ S.ents) F ci t k.1 k.2 (bndD S kd)
      (bndD (bootSnapState Tn t ci) none) HBle Hci0 (by omega)
      HtF Hdiff Htk $$ Hh
  · -- a certificate `cq t' n G`: `G` agrees with `F` up to `c`
    obtain ⟨Hcn, Htr, Hag⟩ := Hcn
    icases cq_base γ t' n G $$ Hcq with ⟨%HGn, #Hf⟩
    icases leadFull_wf γ t' G $$ Hf with ⟨%HGp, #HGr⟩
    have HGc : (plogTermAt base0 G c).isSome := full_term_at_some G c n (by rw [HGn]; rfl) Hcn
    icases full_match γ G F c HGp.1 HwF HGc Hag $$ HGr HrF with %HM
    -- its leader, which (at `Tn`) the node did not vote for: its votes are of terms `≤ S.term`
    icases leadFull_camp γ t' G $$ Hf with ⟨%ldr, %F0, #Hl, -, -⟩
    iunfold isLeader at Hl
    icases Hl with ⟨%q, #Hw⟩
    ihave ⟨%Hnq, Hsh⟩ : ⌜uint.Z t' = uint.Z Tn → id ∉ q⌝ ∗ durShares γ id (1 : Qp).half E $$ [Hsh]
    · by_cases Htn : uint.Z t' = uint.Z Tn
      · icases durShares_noVote γ id _ E ldr t' q
          (fun t0 h => by have := Hvh.1 t0 h; omega) $$ Hsh Hw with ⟨%Hq, Hsh⟩
        iframe Hsh
        ipureintro; intro _; exact Hq
      · iframe Hsh
        ipureintro; intro h; exact absurd h Htn
    imodintro
    iframe Hsh
    by_cases Htn : uint.Z t' = uint.Z Tn
    · -- the certificate's term is `Tn`: its leader is known, the bound `Tn + 1`
      have HtT : t' = Tn := uint_Z_inj.mp Htn
      iexists some ldr
      isplitr
      · unfold klOkD bootSnapState
        dsimp only
        iexists q
        rw [← HtT]
        iframe Hw
        ipureintro; intro _; exact Hnq Htn
      iapply BigSepM.bigSepM_impl $$ Hhs
      iintro !> %k %_u %_Hk #Hh
      iapply bootB_hist_cert γ (fp ++ S.ents) F G ci c n t' t k.1 k.2 (bndD S kd)
        (bndD (bootSnapState Tn t ci) (some ldr))
        (by show bndD S kd ≤ uint.Z Tn + 1; omega)
        (by show uint.Z t' < uint.Z Tn + 1; omega) Hci0 Hcic Hcn HtF Hdiff HM $$ Hcq Hh
    · iexists none
      isplitr; · unfold klOkD; ipureintro; trivial
      iapply BigSepM.bigSepM_impl $$ Hhs
      iintro !> %k %_u %_Hk #Hh
      iapply bootB_hist_cert γ (fp ++ S.ents) F G ci c n t' t k.1 k.2 (bndD S kd)
        (bndD (bootSnapState Tn t ci) none) HBle
        (by show uint.Z t' < uint.Z Tn; omega) Hci0 Hcic Hcn HtF Hdiff HM $$ Hcq Hh

/-- (L6a) **The durable invariants of branch B** (the log replaced by the committed prefix
`F.take ci`, at the base `(t, ci)`, the term raised to `Tn` with the vote cleared and its campaign key
closed), given the acknowledgements' histories and the known leader in the new log (`bootB_hists`).
-/
theorem durPers_snapBase (γ : RaftNames) (id : w64) (S : RaftState) (E : DurMaps) (F : List EntryM)
    (ci c rt Tn t : w64) (kd' : Option w64) :
    uint.Z S.term < uint.Z Tn → uint.Z rt ≤ uint.Z Tn → uint.Z ci ≤ uint.Z c → 0 < uint.Z ci →
    PlogWf base0 F → plogTermAt base0 F ci = some t →
    (∀ (j x : w64), uint.Z j ≤ uint.Z c → plogTermAt base0 F j = some x → uint.Z x ≤ uint.Z rt) →
    durPers (GF := GF) γ id S E ∗ logRecs γ base0 F ∗ commitIn γ F c rt ∗
        isCommitted γ (F.take (uint.Z c).toNat) ∗ klOkD γ id (bootSnapState Tn t ci) kd' ∗
        ([∗map] k ↦ _u ∈ E.acks,
          hist γ (F.take (uint.Z ci).toNat) k.1 k.2 (bndD (bootSnapState Tn t ci) kd')) ⊢
      durPers γ id (bootSnapState Tn t ci) (E.add (.close Tn)) := by
  intro HT HrT Hcic Hci0 HwF HtF HtermF
  iintro ⟨#Hd, #HrF, #HcF, #HkF, #Hkl', #Hhs'⟩
  iunfold durPers at Hd
  icases Hd with ⟨%kd, %fp, %Hp, -, -, -, #Hvl, -, -, -, -, -, #Hinv, #Hai, -, -⟩
  obtain ⟨Hvh, Hak, Hcp, Hev, -, -, -, -, -⟩ := Hp
  have Hfresh : E.camps !! Tn = none := by
    cases h : E.camps !! Tn with
    | none => rfl
    | some x => exfalso; have := Hcp Tn (by rw [h]; rfl); omega
  have Hvfresh : E.voted !! Tn = none := by
    cases h : E.voted !! Tn with
    | none => rfl
    | some x => exfalso; have := Hvh.1 Tn (by rw [h]; rfl); omega
  have HtR := plogTermAt_some_range _ _ _ _ HtF
  rw [base0_index] at HtR
  have HfB : FullOk (entryID.mk t ci) (F.take (uint.Z ci).toNat) := FullOk_take F t ci HwF HtF
  have HwT : PlogWf base0 (F.take (uint.Z ci).toNat) := PlogWf_take _ _ _ HwF
  have HtT : plogTermAt base0 (F.take (uint.Z ci).toNat) ci = plogTermAt base0 F ci :=
    plogTermAt_take_base0 F _ ci (by omega)
  have HsomeF : (plogTermAt base0 F ci).isSome := by rw [HtF]; rfl
  have Hnil : F.take (uint.Z ci).toNat ++ ([] : List EntryM) = F.take (uint.Z ci).toNat :=
    List.append_nil _
  have HlenT : ((F.take (uint.Z ci).toNat).length : Int) = uint.Z ci := HfB.1
  iunfold bootSnapState at Hkl'
  iunfold bootSnapState at Hhs'
  unfold durPers
  iexists kd', F.take (uint.Z ci).toNat
  simp only [bootSnapState, DurMaps.add]
  rw [Hnil]
  isplitr
  · ipureintro
    refine ⟨⟨fun t' h => ?_, ?_⟩, fun k h => ?_, fun T' h => ?_, ?_, HfB, fun k e h => by simp at h,
      fun j x h => ?_, Int.le_refl _, ?_⟩
    · have := Hvh.1 t' h; (try simp only); omega
    · simp [Hvfresh]
    · have := Hak k h; (try simp only); omega
    · by_cases hT : Tn = T'
      · subst hT; (try simp only); omega
      · rw [GMap.lookup_insert_ne _ _ hT] at h; have := Hcp T' h; (try simp only); omega
    · obtain ⟨a, b, c, d⟩ := Hev
      exact ⟨a, fun e he => by have := b e he; (try simp only); omega, c, d⟩
    · have Hr := plogTermAt_some_range _ _ _ _ h
      unfold plogLastIndexZ at Hr; rw [base0_index] at Hr
      have Hj : uint.Z j ≤ uint.Z ci := by (try simp only); omega
      rw [plogTermAt_take_base0 F _ j (by (try simp only); omega)] at h
      have := HtermF j x (by (try simp only); omega) h; (try simp only); omega
    · unfold plogLastIndexZ; simp
  isplitr; · unfold logRecs; simp only [List.length_nil]; iempintro
  isplitr
  · unfold baseOk
    iright
    obtain ⟨e, He, Hei, Het⟩ := plogTermAt_some_entry base0 F ci t (PlogWf_wfR _ _ HwF) HtF
      (by rw [base0_index]; omega)
    rw [base0_index] at He
    ihave ⟨%pt, -, #Her⟩ := logRecs_lookup γ F _ e He
      (by have := uint_Z_lt ci; omega) $$ HrF
    unfold isSnapMeta
    iexists e
    isplitr
    · unfold isEntry; iexists pt; iexact Her
    ipureintro; exact ⟨Het, Hei⟩
  isplitr; · iapply logRecs_take γ F _ $$ HrF
  isplitr
  · iapply BigSepM.bigSepM_impl $$ Hvl
    iintro !> %k %x %_ ⟨%Hx, #H⟩
    isplitr; · ipureintro; omega
    iexact H
  isplitr; · iexact Hhs'
  isplitr; · iexact Hkl'
  isplitr
  · iapply BigSepM.bigSepM_impl $$ Hhs'
    iintro !> %k %_u %Hk -
    iintro %Hkt
    exfalso
    have Hk' : E.acks !! k = some _u := Hk
    have h2 := Hak k (by rw [Hk']; rfl)
    have h1 : k.1 = Tn := Hkt.1
    rw [h1] at h2; omega
  isplitr
  · ihave #HrTk := logRecs_take γ F (uint.Z ci).toNat $$ HrF
    iapply commitIn_boot γ F (F.take (uint.Z ci).toNat) c ci rt Tn HwF HwT Hcic HrT HsomeF HtT
      $$ HrF HrTk HcF
  isplitr
  · rw [List.take_take, Nat.min_self]
    iapply isCommitted_mono γ (F.take (uint.Z ci).toNat) (F.take (uint.Z c).toNat)
      (List.take_prefix_take_left (by omega)) $$ HkF
  isplitr; · iexact Hinv
  isplitr
  · iintro !> #Hf
    iapply Hai
    iapply durFrags_mono γ id E
      { voted := E.voted, acks := E.acks, camps := <[Tn := campNone]> E.camps, vlogs := E.vlogs,
        evs := E.evs } (DurLe_add E (.close Tn) Hfresh) $$ Hf
  isplitr
  · iapply campLink_close γ id E.camps Tn
    iapply campLink_none γ id E.camps Tn _ Hfresh
  · ipureintro; right; simp

end ghost

end EtcdGrove
end Perennial
