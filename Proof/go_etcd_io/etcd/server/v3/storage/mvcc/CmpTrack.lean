/-
**The compaction tracking, kept by the store's writers** (F2, stage 2,
`notes/image-cmp-f2-plan.md`). Lean-first (no Rocq counterpart).

The batch lock's tracking (`cmpTrack`, `InvStore.lean`) moves with every write to the backend's
`Key` bucket or its compaction keys; this file has its laws for the moves the store makes: a write
transaction's commit (`writerTrk_commit`: the session's puts are the committed revision's entries,
`cmpFacts_snoc`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.CmpCut

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvcc

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- **A commit closes the write session's tracking at the committed log** (`storeTxnWrite.End` with
a change): the tie moves to `ilog ++ [pend]` (both halves held: the tracking's and the
transaction's), and the facts follow (`cmpFacts_snoc`). -/
theorem writerTrk_commit (γ : StoreNames) (ilog : Log) (pend : List Change)
    (hwf : IdxWf ilog pend) (hne : ilog ≠ []) :
    writerTrk (GF := GF) γ ilog pend ==∗
      kbLog γ.kb (1 : Qp).half.half (ilog ++ [pend]) ∗ kbLog γ.kb (1 : Qp).half.half (ilog ++ [pend]) ∗
        kbTrack γ.kb (ilog ++ [pend]) := by
  obtain ⟨hwf', hl, hpl, hcs⟩ := hwf
  have hb : LogB (ilog ++ [pend]) := by
    refine ⟨by simp; omega, fun cs h => ?_⟩
    rcases List.mem_append.1 h with h | h
    · exact hcs cs h
    · rw [List.mem_singleton] at h; rw [h]; exact hpl
  unfold writerTrk kbTrackW kbLog kbTrack
  generalize γ.kb = kb
  cases kb with
  | none => iintro -; imodintro; isplitl <;> (try isplitl) <;> itrivial
  | some d =>
    simp only
    unfold cmpTrack trackW bkPV
    cases hcm : d.cm with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      iintro ⟨-, %vd0, %v, ⟨%vd, Hp, -⟩, Hc, -⟩
      imodintro
      isplitl []
      · itrivial
      isplitl []
      · itrivial
      iexists vd, v
      iframe Hp Hc
    | true =>
      simp only [↓reduceIte]
      iintro ⟨Hlg, %vd0, %v, ⟨%vd, Hp, %hk⟩, Hc, Hon⟩
      unfold cmpTrackOn
      icases Hon with ⟨%r, %c, %p, %n, Hl, Hs, Hj, Hn, %hn, %hf⟩
      imod ghostVar_update_halves (ilog ++ [pend]) d.ties.lg ilog ilog $$ Hlg Hl with ⟨Hlg, Hl⟩
      icases (ghostVar_split_half d.ties.lg (1 : Qp).half (ilog ++ [pend])).1 $$ Hlg with ⟨H1, H2⟩
      imodintro
      iframe H1 H2
      iexists vd, v
      iframe Hp Hc
      iexists r, c, p, n
      iframe Hl Hs Hj Hn
      ipureintro
      exact ⟨hn, cmpFacts_snoc hf hb hwf' hne hk⟩

/-- **Raising the scheduled record keeps the facts** (pure; `updateCompactRev`'s session): the
scheduled record set to `rev`, at or above the records' revision, a positive revision of the log,
makes `rev` the records' revision (the finished record is at most the old one), and the facts hold
of the new records, the compaction keys' values after the put (the cut is at a higher revision,
`entsCutAt_mono`; the cursor is unchanged). -/
theorem cmpFacts_sched {L : Log} {r : CmpRecs} {vd : backend.VData} {v : backend.FkVals} {c : Int}
    {p : Rev} (rev : w64) (hf : cmpFacts L r vd v c p) (hc : r.crev ≤ sint.Z rev)
    (h1 : 1 ≤ sint.Z rev) (hr : sint.Z rev < L.length) :
    cmpFacts L { r with sched := some rev } vd
        (fkSet schedKeyBytes (revBytes ⟨rev, W64 0⟩ false) v) c p ∧
      ({ r with sched := some rev } : CmpRecs).crev = sint.Z rev := by
  obtain ⟨⟨ents, hk, hok, hpos, hcut⟩, hv, hcc, -, hcd, hb, hwf⟩ := hf
  have hfr : r.finRev ≤ r.crev := by
    unfold CmpRecs.crev CmpRecs.resumes
    split
    · rename_i h; simp only [decide_eq_true_eq] at h; omega
    · exact Int.le_refl _
  have hf' : ({ r with sched := some rev } : CmpRecs).finRev = r.finRev := rfl
  have hs' : ({ r with sched := some rev } : CmpRecs).schedRev = sint.Z rev := rfl
  have hcr : ({ r with sched := some rev } : CmpRecs).crev = sint.Z rev := by
    unfold CmpRecs.crev CmpRecs.resumes
    rw [hs', hf']
    split
    · rfl
    · rename_i h
      simp only [decide_eq_true_eq, not_and] at h
      have := h (by omega)
      omega
  refine ⟨⟨⟨ents, hk, ⟨hok.1, fun x hx => ?_⟩, ⟨hpos.1, fun x hx => ?_⟩, ?_⟩, ?_, ?_, ?_, hcd,
    hb, hwf⟩, hcr⟩
  · simp only [Option.some.injEq] at hx; subst hx; exact ⟨by omega, hr⟩
  · simp only [Option.some.injEq] at hx; subst hx; exact h1
  · rw [hcr]; exact entsCutAt_mono hb (CmpRecs.crev_ge L r hok) hc hr hcut
  · have hne : schedKeyBytes ≠ finKeyBytes := by decide
    unfold fkSet; rw [if_neg hne, hv]; rfl
  · rw [hcr]; omega
  · intro _; rw [hcr]; exact hs'

end proof

section proofLc
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- **`updateCompactRev`'s swap** (F2, stage 2): with `s.mu` held exclusively (the whole of its
deposit ghost `γ.wr`), the committed log `log` (`s.revMu`'s half of `γ.clog`) and the compaction
right's tie at `c` (`kbCrev`), `SetScheduledCompact`'s session's swap of the batch lock's resource
for its write right, lending the compaction keys' values: the batch lock's log is `log`
(`writerInv_clog`, one later credit, captured), so the put of the scheduled record at `rev` (above
`c`, a positive revision of `log`) keeps the tracking's facts (`cmpFacts_sched`), and the tie moves
to `rev`, both halves (the tracking's and the right's, given back). -/
theorem mwSwapCK_sched (s : Loc) (γ : StoreNames) (d : KBReal) (dq : DFrac) (o : StoreObjs)
    (log : Log) (c : Int) (rev : w64) (hkb : γ.kb = some d) (hcm : d.cm = true)
    (hc : c ≤ sint.Z rev) (h1 : 1 ≤ sint.Z rev) (hr : sint.Z rev < log.length) :
    ⊢ physCmp (GF := GF) s γ -∗ writerInv s γ -∗ £ 1 -∗ curAt γ dq o -∗ ghostVar γ.wr 1 () -∗
      ghostVar γ.clog (1 : Qp).half log -∗ kbCrev γ.kb c -∗
      mwSwapCK (storeW s γ) (kbMW γ.kb γ.bucket) (storeCK γ) schedKeyBytes
        (revBytes ⟨rev, W64 0⟩ false)
        iprop(curAt γ dq o ∗ ghostVar γ.wr 1 () ∗ ghostVar γ.clog (1 : Qp).half log ∗
          kbCrev γ.kb (sint.Z rev) ∗ kbCrevLb γ.kb (sint.Z rev)) := by
  have hcM : kbCmpM γ.kb := by rw [hkb]; exact hcm
  have eT : ∀ L, kbTrack (GF := GF) γ.kb L ⊣⊢ iprop(∃ (vd : backend.VData) (v : backend.FkVals),
      backend.pvHalf d.γB vd ∗ backend.ckHalf d.γB v ∗
      ∃ (r : CmpRecs) (c : Int) (p : Rev) (n : Nat),
        ghostVar d.ties.lg (1 : Qp).half L ∗ ghostVar d.ties.sg (1 : Qp).half r.crev ∗
        ghostVar d.ties.jg (1 : Qp).half (c, p.main, p.sub) ∗ monoNatAuthOwn d.ties.sl 1 n ∗
        ⌜slOk n r⌝ ∗ ⌜cmpFacts L r vd v c p⌝) := by
    intro L; rw [hkb]; unfold kbTrack cmpTrack cmpTrackOn; simp only [hcm, ↓reduceIte] <;> exact .rfl
  have eC : ∀ c, kbCrev (GF := GF) γ.kb c ⊣⊢ ghostVar d.ties.sg (1 : Qp).half c := by
    intro c; rw [hkb]; unfold kbCrev; simp only [hcm, ↓reduceIte] <;> exact .rfl
  have eB : ∀ c, kbCrevLb (GF := GF) γ.kb c ⊣⊢ monoNatLbOwn d.ties.sl (crevN c) := by
    intro c; rw [hkb]; unfold kbCrevLb; simp only [hcm, ↓reduceIte] <;> exact .rfl
  have eK : ∀ v, storeCK (GF := GF) γ v ⊣⊢ backend.ckHalf d.γB v := by
    intro v; simp only [storeCK, hkb] <;> exact .rfl
  iintro #Hph #Hwi Hlc0 Hpin Hwr Hcl Hcr
  icases (physCmp_on s γ hcM).1 $$ Hph with ⟨#Hmi, #Hreg⟩
  iunfold mwSwapCK
  iintro ⟨HW, Hlc⟩
  imod storeW_open s γ ⊤ (by solve_ndisj) $$ Hreg HW with ⟨HW, #Hregd⟩
  iunfold writerRes at HW
  icases HW with ⟨%L, Hwk, Hwv, Hbv, #Hcert, %Hne, Hcres, Hlg, Htrk⟩
  imod writerInv_clog s γ dq o L log $$ Hlc0 Hwi Hpin Hwr Hwv Hcl with ⟨%HL, Hpin, Hwr, Hwv, Hcl⟩
  subst HL
  iunfold compactRes at Hcres
  icases Hcres with ⟨%sch, %fin, %n, Hmeta, Hfin, %Hn, Hslot⟩
  ihave Hk := (mwSlot_on γ hcM).1 $$ Hslot
  ihave #Hsw := mwSwap_of_inv γ iprop(True) $$ Hmi
  iunfold mwSwap at Hsw
  imod Hsw $$ [Hk Hlc] with ⟨HMW, Hback⟩
  · isplitl [Hk]
    · iframe Hk
    · iexact Hlc
  icases (eT L).1 $$ Htrk with ⟨%vd, %v, Hpv, Hck, %r, %c', %p, %nl, Hlgt, Hsg, Hjg, Hsl, %Hsl, %Hf⟩
  icases (eC c).1 $$ Hcr with Hcr
  ihave %Hsc := ghostVar_agree d.ties.sg r.crev _ c _ $$ Hsg Hcr
  imod ghostVar_update_halves (sint.Z rev) d.ties.sg r.crev c $$ Hsg Hcr with ⟨Hsg, Hcr⟩
  obtain ⟨Hf', Hcr'⟩ := cmpFacts_sched rev Hf (by omega) h1 hr
  have hnle : nl ≤ crevN (sint.Z rev) := Nat.le_trans Hsl.1 (crevN_mono (by omega))
  imod mono_nat_own_update (crevN (sint.Z rev)) hnle $$ Hsl with ⟨Hsl, #Hlb⟩
  imodintro
  iframe HMW
  iexists v
  isplitl [Hck]
  · iapply (eK v).2; iexact Hck
  iintro ⟨HMW, Hck⟩
  ihave Hck := (eK _).1 $$ Hck
  imod Hback $$ HMW with ⟨Hk, -⟩
  ihave Hslot := (mwSlot_on γ hcM).2 $$ Hk
  imodintro
  iframe Hpin Hwr Hcl
  isplitr [Hcr]
  · iapply storeW_put s γ
    iframe Hregd
    iunfold writerRes
    iexists L
    simp only [named]
    iframe Hwk Hwv Hbv Hcert Hlg
    isplitr
    · ipureintro; exact Hne
    isplitl [Hmeta Hfin Hslot]
    · iunfold compactRes; iexists sch, fin, n; iframe Hmeta Hfin Hslot; ipureintro; exact Hn
    iapply (eT L).2
    iexists vd, fkSet schedKeyBytes (revBytes ⟨rev, W64 0⟩ false) v
    iframe Hpv Hck
    iexists { r with sched := some rev }, c', p, crevN (sint.Z rev)
    iframe Hlgt Hjg Hsl
    rw [Hcr']
    iframe Hsg
    ipureintro
    refine ⟨⟨by rw [Hcr']; exact Nat.le_refl _, fun _ => by rw [Hcr']; rfl⟩, Hf'⟩
  isplitl [Hcr]
  · iapply (eC _).2; iexact Hcr
  iapply (eB _).2; iexact Hlb

/-- `mwSwapCK_sched` for both backends (`storeCmp`): mvcc's assumed backend has no tracking (its
compaction keys' values and the tie are nothing), and the plain swap (`mwSwap_of_physOk`) serves. -/
theorem mwSwapCK_schedM (s : Loc) (γ : StoreNames) (dq : DFrac) (o : StoreObjs)
    (log : Log) (c : Int) (rev : w64) (h : kbCmpM γ.kb)
    (hc : c ≤ sint.Z rev) (h1 : 1 ≤ sint.Z rev) (hr : sint.Z rev < log.length) :
    ⊢ physCmp (GF := GF) s γ -∗ writerInv s γ -∗ £ 1 -∗ curAt γ dq o -∗ ghostVar γ.wr 1 () -∗
      ghostVar γ.clog (1 : Qp).half log -∗ kbCrev γ.kb c -∗
      mwSwapCK (storeW s γ) (kbMW γ.kb γ.bucket) (storeCK γ) schedKeyBytes
        (revBytes ⟨rev, W64 0⟩ false)
        iprop(curAt γ dq o ∗ ghostVar γ.wr 1 () ∗ ghostVar γ.clog (1 : Qp).half log ∗
          kbCrev γ.kb (sint.Z rev) ∗ kbCrevLb γ.kb (sint.Z rev)) := by
  rcases Option.eq_none_or_eq_some γ.kb with hkb | ⟨d, hkb⟩
  · iintro #Hph #Hwi Hlc0 Hpin Hwr Hcl Hcr
    ihave #Hsw := mwSwap_of_physOk s γ h $$ Hph
    iunfold mwSwap at Hsw
    iunfold mwSwapCK
    iintro ⟨HW, Hlc⟩
    imod Hsw $$ [HW Hlc] with ⟨HMW, Hback⟩
    · iframe HW Hlc
    imodintro
    iframe HMW
    iexists (none, none)
    isplitr
    · simp only [storeCK, hkb]; itrivial
    iintro ⟨HMW, -⟩
    imod Hback $$ HMW with HW
    imodintro
    iframe HW Hpin Hwr Hcl
    rw [hkb]; simp only [kbCrev, kbCrevLb]; isplitl <;> itrivial
  · have hcm : d.cm = true := by rw [hkb] at h; exact h
    exact mwSwapCK_sched s γ d dq o log c rev hkb hcm hc h1 hr

end proofLc

end mvcc
end EtcdGrove
end Perennial
