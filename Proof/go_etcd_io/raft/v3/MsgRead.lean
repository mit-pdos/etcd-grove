/-
**Reading a message held at a content through today's specs** (raft-entsize §4, 2026-11-10; out_size
C3, 2026-11-12: moved here from rafthttp, with `msgPtsCC_of_struct` from rafthttp's `MsgAppV2`, for
raft's outbox, decided by etcd-grove-81).

A received message is owned at a content (`msgPtsCC ml 1 1 true c`, what `netRecv` hands `Process` and
`stepIn_intro` takes, with the content's size fact), but the code reads it through specs stated over
today's form (`msgPtsC`: the getters, `proto.Size`, `isLinkHeartbeatMessage`), whose posts give
back some `msgPtsC`, not the content: two contents of one object cannot be shown equal (`pbMsg`'s
unknown fields live in an invariant). So the reader takes half of the object in today's form and keeps
the other half at the content (`msgPtsCC_read`): today's half given back, the halves agree on every
pointer and slice, and the kept half's persistent parts (presences, entries, unknown fields) rebuild
the whole object at the same content.

A conf state frozen at its content (`csOptCC`'s `discard` case) stays so; one owned whose half comes
back frozen is rebuilt frozen (`csOptCC_combine`).
-/
module

public import Proof.go_etcd_io.raft.v3.PbContentOwn

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section halves
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- Half of the whole (`(1 : Qp).half`). -/
abbrev dqh : DFrac := DFrac.own (1 : Qp).half

theorem dqh_op : dqh • dqh = DFrac.own 1 := by
  show DFrac.own ((1 : Qp).half + (1 : Qp).half) = _
  rw [Qp.half_add_half]

theorem tpt_halves {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] (l : Loc) (v : V) :
    typedPointsto (GF := GF) l v (DFrac.own 1) ⊣⊢
      typedPointsto (GF := GF) l v dqh ∗ typedPointsto (GF := GF) l v dqh :=
  typedPointsto_half_split l v 1

theorem slice_halves {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] (s : GoSlice)
    (vs : List V) : (s ↦*{DFrac.own 1} vs : IProp GF) ⊣⊢ s ↦*{dqh} vs ∗ s ↦*{dqh} vs := by
  have h := (ownSlice_dfractional (GF := GF) s vs).dfractional dqh dqh
  rw [dqh_op] at h
  exact h

/-- Two points-to of one location, kept, agree. -/
theorem tpt_agree_keep {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] (l : Loc) (d1 d2 : DFrac)
    (a b : V) :
    (typedPointsto (GF := GF) l a d1 ∗ typedPointsto (GF := GF) l b d2) ⊢
      (typedPointsto (GF := GF) l a d1 ∗ typedPointsto (GF := GF) l b d2) ∗ ⌜a = b⌝ :=
  persistent_entails_left (by
    iintro ⟨H1, H2⟩
    iapply (typedPointsto_agree_wand l d1 d2 a b) $$ H1 H2)

/-- Two slice points-to of one slice, kept, agree. -/
theorem slice_agree_keep {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] (s : GoSlice)
    (d1 d2 : DFrac) (a b : List V) :
    (s ↦*{d1} a ∗ s ↦*{d2} b : IProp GF) ⊢ (s ↦*{d1} a ∗ s ↦*{d2} b) ∗ ⌜a = b⌝ :=
  persistent_entails_left (by
    iintro ⟨H1, H2⟩
    iapply (ownSlice_agree s d1 d2 a b) $$ H1 H2)

/-- Two halves of one location, at one value, make the whole. -/
theorem tpt_join {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] (l : Loc) (a b : V) :
    (typedPointsto (GF := GF) l a dqh ∗ typedPointsto (GF := GF) l b dqh) ⊢
      typedPointsto (GF := GF) l a (DFrac.own 1) ∗ ⌜a = b⌝ := by
  iintro H
  ihave ⟨⟨H1, H2⟩, %e⟩ := tpt_agree_keep l dqh dqh a b $$ H
  subst e
  isplitl
  · iapply (tpt_halves l a).2; iframe
  · ipureintro; rfl

/-- Two halves of one slice, at one list, make the whole. -/
theorem slice_join {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] (s : GoSlice) (a b : List V) :
    (s ↦*{dqh} a ∗ s ↦*{dqh} b : IProp GF) ⊢ s ↦*{DFrac.own 1} a ∗ ⌜a = b⌝ := by
  iintro H
  ihave ⟨⟨H1, H2⟩, %e⟩ := slice_agree_keep s dqh dqh a b $$ H
  subst e
  isplitl
  · iapply (slice_halves s a).2; iframe
  · ipureintro; rfl

end halves

section cs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

theorem csPtsCC_split (p : Loc) (c : CSC) :
    csPtsCC (GF := GF) p (DFrac.own 1) c false ⊢ csPtsCC p dqh c false ∗ csPtsCC p dqh c false := by
  unfold csPtsCC
  iintro ⟨%sv, %sl, %so, %sn, %pa, %Hnn, HV, Hv, HL, Hl, HO, Ho, HN, Hn, HA, #cA, %Hal, #Hpb⟩
  icases (tpt_halves _ sv).1 $$ HV with ⟨HV1, HV2⟩
  icases (tpt_halves _ sl).1 $$ HL with ⟨HL1, HL2⟩
  icases (tpt_halves _ so).1 $$ HO with ⟨HO1, HO2⟩
  icases (tpt_halves _ sn).1 $$ HN with ⟨HN1, HN2⟩
  icases (tpt_halves _ pa).1 $$ HA with ⟨HA1, HA2⟩
  icases (slice_halves sv _).1 $$ Hv with ⟨Hv1, Hv2⟩
  icases (slice_halves sl _).1 $$ Hl with ⟨Hl1, Hl2⟩
  icases (slice_halves so _).1 $$ Ho with ⟨Ho1, Ho2⟩
  icases (slice_halves sn _).1 $$ Hn with ⟨Hn1, Hn2⟩
  isplitl [HV1 HL1 HO1 HN1 HA1 Hv1 Hl1 Ho1 Hn1]
  · iexists sv, sl, so, sn, pa
    iframe; iframe #; ipureintro; exact ⟨Hnn, Hal⟩
  · iexists sv, sl, so, sn, pa
    iframe; iframe #; ipureintro; exact ⟨Hnn, Hal⟩

theorem csPtsCC_join (p : Loc) (c c' : CSC) :
    csPtsCC (GF := GF) p dqh c false ∗ csPtsCC p dqh c' false ⊢ csPtsCC p (DFrac.own 1) c false := by
  unfold csPtsCC
  iintro ⟨⟨%sv, %sl, %so, %sn, %pa, %Hnn, HV, Hv, HL, Hl, HO, Ho, HN, Hn, HA, #cA, %Hal, #Hpb⟩,
    ⟨%sv', %sl', %so', %sn', %pa', -, HV', Hv', HL', Hl', HO', Ho', HN', Hn', HA', -, -, -⟩⟩
  ihave ⟨HV, %e1⟩ := tpt_join _ sv sv' $$ [$HV $HV']
  ihave ⟨HL, %e2⟩ := tpt_join _ sl sl' $$ [$HL $HL']
  ihave ⟨HO, %e3⟩ := tpt_join _ so so' $$ [$HO $HO']
  ihave ⟨HN, %e4⟩ := tpt_join _ sn sn' $$ [$HN $HN']
  ihave ⟨HA, %e5⟩ := tpt_join _ pa pa' $$ [$HA $HA']
  subst e1 e2 e3 e4 e5
  ihave ⟨Hv, -⟩ := slice_join sv _ _ $$ [$Hv $Hv']
  ihave ⟨Hl, -⟩ := slice_join sl _ _ $$ [$Hl $Hl']
  ihave ⟨Ho, -⟩ := slice_join so _ _ $$ [$Ho $Ho']
  ihave ⟨Hn, -⟩ := slice_join sn _ _ $$ [$Hn $Hn']
  iexists sv, sl, so, sn, pa
  iframe; iframe #; ipureintro; exact ⟨Hnn, Hal⟩

/-- An owned half and a frozen one: the conf state frozen. -/
theorem csPtsCC_join_ro (p : Loc) (c c' : CSC) :
    csPtsCC (GF := GF) p dqh c false ∗ csPtsCC p DFrac.discard c' true ⊢
      csPtsCC p DFrac.discard c true := by
  unfold csPtsCC
  iintro ⟨⟨%sv, %sl, %so, %sn, %pa, %Hnn, HV, Hv, HL, Hl, HO, Ho, HN, Hn, HA, #cA, -, #Hpb⟩,
    ⟨%sv', %sl', %so', %sn', %pa', -, #HV', #Hv', #HL', #Hl', #HO', #Ho', #HN', #Hn', #HA', -, %Hal', -⟩⟩
  ihave ⟨-, %e1⟩ := tpt_agree_keep _ _ _ sv sv' $$ [$HV $HV']
  ihave ⟨-, %e2⟩ := tpt_agree_keep _ _ _ sl sl' $$ [$HL $HL']
  ihave ⟨-, %e3⟩ := tpt_agree_keep _ _ _ so so' $$ [$HO $HO']
  ihave ⟨-, %e4⟩ := tpt_agree_keep _ _ _ sn sn' $$ [$HN $HN']
  ihave ⟨-, %e5⟩ := tpt_agree_keep _ _ _ pa pa' $$ [$HA $HA']
  subst e1 e2 e3 e4 e5
  ihave ⟨-, %f1⟩ := slice_agree_keep sv _ _ _ _ $$ [$Hv $Hv']
  ihave ⟨-, %f2⟩ := slice_agree_keep sl _ _ _ _ $$ [$Hl $Hl']
  ihave ⟨-, %f3⟩ := slice_agree_keep so _ _ _ _ $$ [$Ho $Ho']
  ihave ⟨-, %f4⟩ := slice_agree_keep sn _ _ _ _ $$ [$Hn $Hn']
  iexists sv, sl, so, sn, pa
  rw [f1, f2, f3, f4]
  iframe #; ipureintro; exact ⟨Hnn, Hal'⟩

theorem csOptCC_split (p : Loc) (o : Option CSC) :
    csOptCC (GF := GF) p (DFrac.own 1) o ⊢ csOptCC p dqh o ∗ csOptCC p dqh o := by
  cases o with
  | none => simp only [csOptCC]; iintro %h; isplitl <;> ipureintro <;> exact h
  | some c =>
    simp only [csOptCC]
    iintro (H | #H)
    · icases csPtsCC_split p c $$ H with ⟨H1, H2⟩
      isplitl [H1]
      · ileft; iexact H1
      · ileft; iexact H2
    · isplitl <;> (iright; iexact H)

theorem csPtsCC_nn (p : Loc) (dq : DFrac) (c : CSC) (al : Bool) :
    csPtsCC (GF := GF) p dq c al ⊢ ⌜p ≠ null⌝ := by
  unfold csPtsCC
  iintro ⟨%sv, %sl, %so, %sn, %pa, %Hnn, -⟩
  ipureintro; exact Hnn

/-- Two halves of a conf state. -/
theorem csOptCC_join (p : Loc) (o o' : Option CSC) :
    csOptCC (GF := GF) p dqh o ∗ csOptCC p dqh o' ⊢ csOptCC p (DFrac.own 1) o := by
  cases o with
  | none => simp only [csOptCC]; iintro ⟨%h1, -⟩; ipureintro; exact h1
  | some c =>
    cases o' with
    | none =>
      simp only [csOptCC]
      iintro ⟨(H1 | #H1), %h2⟩ <;>
      · ihave %Hn := csPtsCC_nn $$ H1
        exact absurd h2 Hn
    | some c' =>
      simp only [csOptCC]
      iintro ⟨(H1 | #H1), (H2 | #H2)⟩
      · ileft; iapply csPtsCC_join p c c'; isplitl [H1]; iexact H1; iexact H2
      · iright; iapply csPtsCC_join_ro p c c'; isplitl [H1]; iexact H1; iexact H2
      · iright; iexact H1
      · iright; iexact H1

end cs

section snap
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

theorem smPtsCC_split (p : Loc) (m : SnapMetaC) :
    smPtsCC (GF := GF) p (DFrac.own 1) m ⊢ smPtsCC p dqh m ∗ smPtsCC p dqh m := by
  unfold smPtsCC
  iintro ⟨%pc, %pi, %pt, %Hnn, HC, Hc, HI, #cI, HT, #cT, #Hpb⟩
  icases (tpt_halves _ pc).1 $$ HC with ⟨HC1, HC2⟩
  icases (tpt_halves _ pi).1 $$ HI with ⟨HI1, HI2⟩
  icases (tpt_halves _ pt).1 $$ HT with ⟨HT1, HT2⟩
  icases csOptCC_split pc _ $$ Hc with ⟨Hc1, Hc2⟩
  isplitl [HC1 HI1 HT1 Hc1]
  · iexists pc, pi, pt
    iframe; iframe #; ipureintro; exact Hnn
  · iexists pc, pi, pt
    iframe; iframe #; ipureintro; exact Hnn

theorem smPtsCC_join (p : Loc) (m m' : SnapMetaC) :
    smPtsCC (GF := GF) p dqh m ∗ smPtsCC p dqh m' ⊢ smPtsCC p (DFrac.own 1) m := by
  unfold smPtsCC
  iintro ⟨⟨%pc, %pi, %pt, %Hnn, HC, Hc, HI, #cI, HT, #cT, #Hpb⟩,
    ⟨%pc', %pi', %pt', -, HC', Hc', HI', -, HT', -, -⟩⟩
  ihave ⟨HC, %e1⟩ := tpt_join _ pc pc' $$ [$HC $HC']
  ihave ⟨HI, %e2⟩ := tpt_join _ pi pi' $$ [$HI $HI']
  ihave ⟨HT, %e3⟩ := tpt_join _ pt pt' $$ [$HT $HT']
  subst e1 e2 e3
  ihave Hc := csOptCC_join pc _ _ $$ [$Hc $Hc']
  iexists pc, pi, pt
  iframe; iframe #; ipureintro; exact Hnn

theorem smPtsCC_nn (p : Loc) (dq : DFrac) (m : SnapMetaC) :
    smPtsCC (GF := GF) p dq m ⊢ ⌜p ≠ null⌝ := by
  unfold smPtsCC
  iintro ⟨%pc, %pi, %pt, %Hnn, -⟩
  ipureintro; exact Hnn

theorem smOptCC_split (p : Loc) (o : Option SnapMetaC) :
    smOptCC (GF := GF) p (DFrac.own 1) o ⊢ smOptCC p dqh o ∗ smOptCC p dqh o := by
  cases o with
  | none => simp only [smOptCC]; iintro %h; isplitl <;> ipureintro <;> exact h
  | some m => simp only [smOptCC]; iintro H; iapply smPtsCC_split p m $$ H

theorem smOptCC_join (p : Loc) (o o' : Option SnapMetaC) :
    smOptCC (GF := GF) p dqh o ∗ smOptCC p dqh o' ⊢ smOptCC p (DFrac.own 1) o := by
  cases o with
  | none => simp only [smOptCC]; iintro ⟨%h1, -⟩; ipureintro; exact h1
  | some m =>
    cases o' with
    | none =>
      simp only [smOptCC]
      iintro ⟨H1, %h2⟩
      ihave %Hn := smPtsCC_nn $$ H1
      exact absurd h2 Hn
    | some m' => simp only [smOptCC]; iintro H; iapply smPtsCC_join p m m' $$ H

theorem bytesCC_split (ds : GoSlice) (o : Option (List w8)) :
    bytesCC (GF := GF) ds (DFrac.own 1) o ⊢ bytesCC ds dqh o ∗ bytesCC ds dqh o := by
  cases o with
  | none => simp only [bytesCC]; iintro %h; isplitl <;> ipureintro <;> exact h
  | some bs =>
    simp only [bytesCC]
    iintro ⟨%h, H⟩
    icases (slice_halves ds bs).1 $$ H with ⟨H1, H2⟩
    isplitl [H1]
    · iframe; ipureintro; exact h
    · iframe; ipureintro; exact h

theorem bytesCC_join (ds : GoSlice) (o o' : Option (List w8)) :
    bytesCC (GF := GF) ds dqh o ∗ bytesCC ds dqh o' ⊢ bytesCC ds (DFrac.own 1) o := by
  cases o with
  | none => simp only [bytesCC]; iintro ⟨%h1, -⟩; ipureintro; exact h1
  | some bs =>
    cases o' with
    | none =>
      simp only [bytesCC]
      iintro ⟨⟨%h1, -⟩, %h2⟩
      exact absurd h2 h1
    | some bs' =>
      simp only [bytesCC]
      iintro ⟨⟨%h1, H1⟩, ⟨-, H2⟩⟩
      ihave ⟨H, -⟩ := slice_join ds bs bs' $$ [$H1 $H2]
      iframe; ipureintro; exact h1

theorem ownSnapCC_split (p : Loc) (sn : SnapC) :
    ownSnapCC (GF := GF) p (DFrac.own 1) sn ⊢ ownSnapCC p dqh sn ∗ ownSnapCC p dqh sn := by
  unfold ownSnapCC
  iintro ⟨%ds, %pm, %Hnn, HD, Hd, HM, Hm, #Hpb⟩
  icases (tpt_halves _ ds).1 $$ HD with ⟨HD1, HD2⟩
  icases (tpt_halves _ pm).1 $$ HM with ⟨HM1, HM2⟩
  icases bytesCC_split ds _ $$ Hd with ⟨Hd1, Hd2⟩
  icases smOptCC_split pm _ $$ Hm with ⟨Hm1, Hm2⟩
  isplitl [HD1 HM1 Hd1 Hm1]
  · iexists ds, pm
    iframe; iframe #; ipureintro; exact Hnn
  · iexists ds, pm
    iframe; iframe #; ipureintro; exact Hnn

theorem ownSnapCC_join (p : Loc) (sn sn' : SnapC) :
    ownSnapCC (GF := GF) p dqh sn ∗ ownSnapCC p dqh sn' ⊢ ownSnapCC p (DFrac.own 1) sn := by
  unfold ownSnapCC
  iintro ⟨⟨%ds, %pm, %Hnn, HD, Hd, HM, Hm, #Hpb⟩, ⟨%ds', %pm', -, HD', Hd', HM', Hm', -⟩⟩
  ihave ⟨HD, %e1⟩ := tpt_join _ ds ds' $$ [$HD $HD']
  ihave ⟨HM, %e2⟩ := tpt_join _ pm pm' $$ [$HM $HM']
  subst e1 e2
  ihave Hd := bytesCC_join ds _ _ $$ [$Hd $Hd']
  ihave Hm := smOptCC_join pm _ _ $$ [$Hm $Hm']
  iexists ds, pm
  iframe; iframe #; ipureintro; exact Hnn

theorem snapOptCC_split (p : Loc) (o : Option SnapC) :
    snapOptCC (GF := GF) p (DFrac.own 1) o ⊢ snapOptCC p dqh o ∗ snapOptCC p dqh o := by
  cases o with
  | none => simp only [snapOptCC]; iintro %h; isplitl <;> ipureintro <;> exact h
  | some sn => simp only [snapOptCC]; iintro H; iapply ownSnapCC_split p sn $$ H

theorem snapOptCC_join (p : Loc) (o o' : Option SnapC) :
    snapOptCC (GF := GF) p dqh o ∗ snapOptCC p dqh o' ⊢ snapOptCC p (DFrac.own 1) o := by
  cases o with
  | none => simp only [snapOptCC]; iintro ⟨%h1, -⟩; ipureintro; exact h1
  | some sn =>
    cases o' with
    | none =>
      simp only [snapOptCC]
      unfold ownSnapCC
      iintro ⟨⟨%ds, %pm, %Hnn, -⟩, %h2⟩
      exact absurd h2 Hnn
    | some sn' => simp only [snapOptCC]; iintro H; iapply ownSnapCC_join p sn sn' $$ H

end snap

section msg
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

set_option maxHeartbeats 1000000 in
theorem msgPtsCC_splitE (l : Loc) (cap : Bool) (c : MsgC) (dqa dqb : DFrac) :
    msgPtsCC (GF := GF) l (DFrac.own 1) (dqa • dqb) cap c ⊢
      msgPtsCC l dqh dqa cap c ∗ msgPtsCC l dqh dqb false c := by
  unfold msgPtsCC
  iintro ⟨%pty, %pto, %pfr, %pte, %plt, %pix, %pco, %pvo, %prj, %prh, %es, %els, %ps, %cs, %rs,
    %Hnn, HTy, #cTy, HTo, #cTo, HFr, #cFr, HTe, #cTe, HLt, #cLt, HIx, #cIx, HCo, #cCo,
    HVo, #cVo, HRj, #cRj, HRh, #cRh, HEs, Hes, #Hents, Hcap, HSn, Hsn, HCx, #Hcx, HRs, Hrs, #Hpb⟩
  icases (tpt_halves _ pty).1 $$ HTy with ⟨HTy1, HTy2⟩
  icases (tpt_halves _ pto).1 $$ HTo with ⟨HTo1, HTo2⟩
  icases (tpt_halves _ pfr).1 $$ HFr with ⟨HFr1, HFr2⟩
  icases (tpt_halves _ pte).1 $$ HTe with ⟨HTe1, HTe2⟩
  icases (tpt_halves _ plt).1 $$ HLt with ⟨HLt1, HLt2⟩
  icases (tpt_halves _ pix).1 $$ HIx with ⟨HIx1, HIx2⟩
  icases (tpt_halves _ pco).1 $$ HCo with ⟨HCo1, HCo2⟩
  icases (tpt_halves _ pvo).1 $$ HVo with ⟨HVo1, HVo2⟩
  icases (tpt_halves _ prj).1 $$ HRj with ⟨HRj1, HRj2⟩
  icases (tpt_halves _ prh).1 $$ HRh with ⟨HRh1, HRh2⟩
  icases (tpt_halves _ es).1 $$ HEs with ⟨HEs1, HEs2⟩
  icases (tpt_halves _ ps).1 $$ HSn with ⟨HSn1, HSn2⟩
  icases (tpt_halves _ cs).1 $$ HCx with ⟨HCx1, HCx2⟩
  icases (tpt_halves _ rs).1 $$ HRs with ⟨HRs1, HRs2⟩
  icases ((ownSlice_dfractional (GF := GF) es els).dfractional dqa dqb).1 $$ Hes with ⟨Hes1, Hes2⟩
  icases (slice_halves rs _).1 $$ Hrs with ⟨Hrs1, Hrs2⟩
  icases snapOptCC_split ps _ $$ Hsn with ⟨Hsn1, Hsn2⟩
  isplitl [HTy1 HTo1 HFr1 HTe1 HLt1 HIx1 HCo1 HVo1 HRj1 HRh1 HEs1 HSn1 HCx1 HRs1 Hes1 Hrs1 Hsn1 Hcap]
  · iexists pty, pto, pfr, pte, plt, pix, pco, pvo, prj, prh, es, els, ps, cs, rs
    iframe; iframe #; ipureintro; exact Hnn
  · iexists pty, pto, pfr, pte, plt, pix, pco, pvo, prj, prh, es, els, ps, cs, rs
    simp only [Bool.false_eq_true, ↓reduceIte]
    iframe; iframe #; ipureintro; exact Hnn

set_option maxHeartbeats 1000000 in
theorem msgPtsCC_joinE (l : Loc) (cap : Bool) (c c' : MsgC) (dqa dqb : DFrac) :
    msgPtsCC (GF := GF) l dqh dqa cap c ∗ msgPtsCC l dqh dqb false c' ⊢
      msgPtsCC l (DFrac.own 1) (dqa • dqb) cap c := by
  unfold msgPtsCC
  iintro ⟨⟨%pty, %pto, %pfr, %pte, %plt, %pix, %pco, %pvo, %prj, %prh, %es, %els, %ps, %cs, %rs,
    %Hnn, HTy, #cTy, HTo, #cTo, HFr, #cFr, HTe, #cTe, HLt, #cLt, HIx, #cIx, HCo, #cCo,
    HVo, #cVo, HRj, #cRj, HRh, #cRh, HEs, Hes, #Hents, Hcap, HSn, Hsn, HCx, #Hcx, HRs, Hrs, #Hpb⟩,
    ⟨%pty', %pto', %pfr', %pte', %plt', %pix', %pco', %pvo', %prj', %prh', %es', %els', %ps', %cs',
    %rs', -, HTy', -, HTo', -, HFr', -, HTe', -, HLt', -, HIx', -, HCo', -,
    HVo', -, HRj', -, HRh', -, HEs', Hes', -, -, HSn', Hsn', HCx', -, HRs', Hrs', -⟩⟩
  ihave ⟨HTy, %e1⟩ := tpt_join _ pty pty' $$ [$HTy $HTy']
  ihave ⟨HTo, %e2⟩ := tpt_join _ pto pto' $$ [$HTo $HTo']
  ihave ⟨HFr, %e3⟩ := tpt_join _ pfr pfr' $$ [$HFr $HFr']
  ihave ⟨HTe, %e4⟩ := tpt_join _ pte pte' $$ [$HTe $HTe']
  ihave ⟨HLt, %e5⟩ := tpt_join _ plt plt' $$ [$HLt $HLt']
  ihave ⟨HIx, %e6⟩ := tpt_join _ pix pix' $$ [$HIx $HIx']
  ihave ⟨HCo, %e7⟩ := tpt_join _ pco pco' $$ [$HCo $HCo']
  ihave ⟨HVo, %e8⟩ := tpt_join _ pvo pvo' $$ [$HVo $HVo']
  ihave ⟨HRj, %e9⟩ := tpt_join _ prj prj' $$ [$HRj $HRj']
  ihave ⟨HRh, %e10⟩ := tpt_join _ prh prh' $$ [$HRh $HRh']
  ihave ⟨HEs, %e11⟩ := tpt_join _ es es' $$ [$HEs $HEs']
  ihave ⟨HSn, %e12⟩ := tpt_join _ ps ps' $$ [$HSn $HSn']
  ihave ⟨HCx, %e13⟩ := tpt_join _ cs cs' $$ [$HCx $HCx']
  ihave ⟨HRs, %e14⟩ := tpt_join _ rs rs' $$ [$HRs $HRs']
  subst e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14
  ihave ⟨⟨Hes, Hes'⟩, %f1⟩ := slice_agree_keep es dqa dqb els els' $$ [$Hes $Hes']
  subst f1
  ihave Hes := ((ownSlice_dfractional (GF := GF) es els).dfractional dqa dqb).2 $$ [$Hes $Hes']
  ihave ⟨Hrs, -⟩ := slice_join rs _ _ $$ [$Hrs $Hrs']
  ihave Hsn := snapOptCC_join ps _ _ $$ [$Hsn $Hsn']
  iexists pty, pto, pfr, pte, plt, pix, pco, pvo, prj, prh, es, els, ps, cs, rs
  iframe; iframe #; ipureintro; exact Hnn

theorem msgPtsCC_split (l : Loc) (cap : Bool) (c : MsgC) :
    msgPtsCC (GF := GF) l (DFrac.own 1) (DFrac.own 1) cap c ⊢
      msgPtsCC l dqh dqh cap c ∗ msgPtsCC l dqh dqh false c := by
  have h := msgPtsCC_splitE (GF := GF) l cap c dqh dqh
  rw [dqh_op] at h
  exact h

theorem msgPtsCC_join (l : Loc) (cap : Bool) (c c' : MsgC) :
    msgPtsCC (GF := GF) l dqh dqh cap c ∗ msgPtsCC l dqh dqh false c' ⊢
      msgPtsCC l (DFrac.own 1) (DFrac.own 1) cap c := by
  have h := msgPtsCC_joinE (GF := GF) l cap c c' dqh dqh
  rw [dqh_op] at h
  exact h

/-- **A message held at a content, read through today's form**, its entries' slice at `dqa • dqb`
(see the file header): half of it in today's form (the slice at `dqb`), and what rebuilds the whole
at the same content from that half given back. (out_size C3: over the slice's fraction, for raft's
messages, whose entries' slices are read-only.) -/
theorem msgPtsCC_readE (l : Loc) (cap : Bool) (c : MsgC) (hcs : c.csUfNil) (dqa dqb : DFrac) :
    msgPtsCC (GF := GF) l (DFrac.own 1) (dqa • dqb) cap c ⊢
      msgPtsC l dqh dqb false c.model ∗
        (msgPtsC l dqh dqb false c.model -∗ msgPtsCC l (DFrac.own 1) (dqa • dqb) cap c) := by
  iintro H
  icases msgPtsCC_splitE l cap c dqa dqb $$ H with ⟨H1, H2⟩
  ihave H2 := msgPtsCC_msgPtsC l dqh dqb false c hcs $$ H2
  iframe H2
  iintro H2
  icases msgPtsC_msgPtsCC l dqh dqb false c.model $$ H2 with ⟨%c', H2, -⟩
  iapply msgPtsCC_joinE l cap c c' dqa dqb
  isplitl [H1]
  · iexact H1
  · iexact H2

/-- **A message held at a content, read through today's form** (see the file header): half of it in
today's form, and what rebuilds the whole at the same content from that half given back. -/
theorem msgPtsCC_read (l : Loc) (cap : Bool) (c : MsgC) (hcs : c.csUfNil) :
    msgPtsCC (GF := GF) l (DFrac.own 1) (DFrac.own 1) cap c ⊢
      msgPtsC l dqh dqh false c.model ∗
        (msgPtsC l dqh dqh false c.model -∗ msgPtsCC l (DFrac.own 1) (DFrac.own 1) cap c) := by
  have h := msgPtsCC_readE (GF := GF) l cap c hcs dqh dqh
  rw [dqh_op] at h
  exact h

end msg

section lit
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- A fresh cell, frozen, is a set optional field. -/
theorem optCell_alloc {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] (p : Loc) (v : V) :
    (p ↦ v : IProp GF) ⊢ |==> optCell p (some v) := by
  iintro H
  imod (typedPointsto_dfractional (GF := GF) p v).dfractional_persist _ $$ H with #H
  imodintro
  simp only [optCell]
  iexact H

/-- **A freshly allocated `*pb.Message` at a content** (raft-entsize §4: `msgPtsC_of_struct_uf`'s
content form): its hidden fields zero, its pointer fields at the content's presences, its `Entries`
a slice of entries frozen at the content's (elements at `dqe`, the capacity when `cap`), its
`Snapshot` and `Context` at the content's, no responses, and no unknown fields. -/
theorem msgPtsCC_of_struct (l : Loc) (v : raftpb.Message) (dqe : DFrac) (cap : Bool)
    (els : List Loc) (f : MsgFC) (E : CoPset) (Hu : v.unknownFields' = slice.nil) (Hf : f.uf = []) :
    (l ↦ v ∗ optCell v.Type' f.type ∗ optCell v.To' f.to ∗ optCell v.From' f.frm ∗
      optCell v.Term' f.term ∗ optCell v.LogTerm' f.logTerm ∗ optCell v.Index' f.index ∗
      optCell v.Commit' f.commit ∗ optCell v.Vote' f.vote ∗ optCell v.Reject' f.reject ∗
      optCell v.RejectHint' f.rejectHint ∗
      v.Entries' ↦*{dqe} els ∗ ([∗list] p;e ∈ els;f.entries, entRoC p e) ∗
      (if cap then ownSliceCap Loc v.Entries' (DFrac.own 1) else emp) ∗
      snapOptCC v.Snapshot' (DFrac.own 1) f.snapshot ∗ bytesC v.Context' f.context ∗
      v.Responses' ↦* ([] : List Loc) : IProp GF) ⊢
      |={E}=> msgPtsCC l (DFrac.own 1) dqe cap (.mk f []) := by
  iintro ⟨Hl, #cTy, #cTo, #cFr, #cTe, #cLt, #cIx, #cCo, #cVo, #cRj, #cRh, Hes, #Hents, Hes_cap,
    Hsn, #Hcs, Hrs⟩
  ihave %Hnn := typedPointsto_not_null $$ Hl
  icases typedPointsto_split _ _ _ $$ Hl with Hl
  simp only [TypedPointsto.typedPointstoDef]
  icases Hl with ⟨state, Ty, To, From, Term, LogTerm, Index, Entries, Commit, Vote, Snapshot,
    Reject, RejectHint, Context, Responses, unknownFields, sizeCache, -⟩
  rw [Hu]
  ihave Hnil : (slice.nil ↦* ([] : List w8) : IProp GF) $$ []
  · iapply ownSlice_nil
  imod pbMsg_alloc raftpb.Message l v.state' v.sizeCache' slice.nil [] E (ufWire_nil _) $$
    [state sizeCache unknownFields Hnil] with #Hpb
  · iframe
  imodintro
  unfold msgPtsCC
  iexists v.Type', v.To', v.From', v.Term', v.LogTerm', v.Index', v.Commit', v.Vote', v.Reject',
    v.RejectHint', v.Entries', els, v.Snapshot', v.Context', v.Responses'
  simp only [MsgC.f, MsgC.resps, List.map_nil, Hf]
  isplitr
  · ipureintro; exact Hnn
  iframe
  iframe cTy cTo cFr cTe cLt cIx cCo cVo cRj cRh Hents Hcs Hpb

/-- A message's object's unknown fields (its `pbMsg`). -/
theorem msgPtsCC_pbMsg (l : Loc) (dq dqe : DFrac) (cap : Bool) (c : MsgC) :
    msgPtsCC (GF := GF) l dq dqe cap c ⊢ pbMsg raftpb.Message l c.f.uf := by
  iintro H
  iunfold msgPtsCC at H
  icases H with ⟨%pty, %pto, %pfr, %pte, %plt, %pix, %pco, %pvo, %prj, %prh, %es, %els, %ps, %cs,
    %rsl, %Hnn, HTy, #cTy, HTo, #cTo, HFr, #cFr, HTe, #cTe, HLt, #cLt, HIx, #cIx, HCo, #cCo,
    HVo, #cVo, HRj, #cRj, HRh, #cRh, HEs, Hes, #Hents, Hcap, HSn, Hsn, HCx, #Hcx, HRs, Hrs, #Hpb⟩
  iexact Hpb

/-- **A message at a content, frozen**: its entries slice frozen, its capacity dropped. -/
theorem msgPtsCC_freeze (l : Loc) (dq dqe : DFrac) (cap : Bool) (c : MsgC) :
    msgPtsCC (GF := GF) l dq dqe cap c ⊢ |==> msgPtsCC l dq DFrac.discard false c := by
  unfold msgPtsCC
  iintro ⟨%pty, %pto, %pfr, %pte, %plt, %pix, %pco, %pvo, %prj, %prh, %es, %els, %ps, %cs,
    %rsl, %Hnn, HTy, #cTy, HTo, #cTo, HFr, #cFr, HTe, #cTe, HLt, #cLt, HIx, #cIx, HCo, #cCo,
    HVo, #cVo, HRj, #cRj, HRh, #cRh, HEs, Hes, #Hents, -, HSn, Hsn, HCx, #Hcx, HRs, Hrs, #Hpb⟩
  imod (ownSlice_dfractional (GF := GF) _ _).dfractional_persist _ $$ Hes with #Hes
  imodintro
  iexists pty, pto, pfr, pte, plt, pix, pco, pvo, prj, prh, es, els, ps, cs, rsl
  simp only [Bool.false_eq_true, ↓reduceIte]
  isplitr
  · ipureintro; exact Hnn
  iframe
  iframe cTy cTo cFr cTe cLt cIx cCo cVo cRj cRh Hes Hents Hcx Hpb

end lit

end EtcdGrove
end Perennial
