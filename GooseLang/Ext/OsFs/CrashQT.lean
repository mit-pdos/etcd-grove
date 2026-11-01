/-
Crash adequacy for the Linux file extension under a premise `Q` on crashes (`CrashP1.lean`),
keeping the old generation's changes in flight (`CrashTok.lean`): the crash interpretation
`os_crash_interpQT` and `osFsQ_crash_adequacyT`.

The restart gets `crashRestQT Q`: the old generation's maps of bytes and files (`crashRest`), its
map of changes in flight with what they hold (`crashRestT`), and the crash's facts
(`crashRestQ`): the crashed state `st`, coherent with the old ghost maps (`OsCoh`), the state
`st'` the new generation starts from, and `Q st st'`. A file is taken with its bytes in runs and,
if a change in flight holds its `OsMeta`, with the change's token; what the crash did to it comes
back as `FileCrashedR` and as `CrashSeenR`, the crash's facts, from which a client's crash
invariant draws what `Q` says of the file (minibolt's P1, `Proof/.../bboltfs/BootP1.lean`). The
`_keep` lemmas give the old resources back, so that the crash part closes the invariant it opened.

Nothing here is trusted: the premise is a hypothesis of the client's theorem, visible in its
statement through the semantics (`osFsSemWith Q`).
-/
module

public import GooseLang.Ext.OsFs.CrashP1
public import GooseLang.Ext.OsFs.CrashTok

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode

/-- What the restarted boot program learns of the file at `p`, taken with the old generation's
`OsMeta` `mo`, the bytes of the runs `rs` and the changes in flight `ts` (tokens it holds): the new
file `fo` is the one at `p` in the state `st'` the new generation starts from, which a crash
(`OsCrash`, and `Q`) made of the crashed state `st`; `st` is coherent with the old ghost maps, in
which `p`'s `OsMeta` is `mo`, the runs' bytes are as `rs` says, and the changes `ts` are in
flight. -/
def CrashSeenR (Q : OsState → OsState → Prop) (p : GoString) (mo : Option OsMeta)
    (rs : List (Nat × DFrac × List (w8 × Bool))) (ts : List (Nat × TokInfo))
    (fo : Option OsFile) : Prop :=
  ∃ (st st' : OsState) (Γb : GMap (GoString × Nat) (w8 × Bool)) (Γm : GMap GoString (Option OsMeta))
    (Γf : GMap w64 OsFd) (Γt : GMap Nat TokInfo),
    OsCoh st Γb Γm Γf Γt ∧ OsCrash st st' ∧ Q st st' ∧ st'.files !! p = some fo ∧
    Γm !! p = some mo ∧
    (∀ r ∈ rs, ∀ k (hk : k < r.2.2.length), Γb !! (p, r.1 + k) = some r.2.2[k]) ∧
    ∀ x ∈ ts, Γt !! x.1 = some x.2

/-! ## The crash interpretation -/

section crash
variable {GF : BundledGFunctors}

/-- `crashRestQ` and the old generation's changes in flight with what they hold (those not yet
taken: `Γt'`, part of the crashed `Γt`). -/
def crashRestQT (Q : OsState → OsState → Prop) (hL hL' : OsGS GF) (D : List GoString) : IProp GF :=
  iprop(∃ (Γb : GMap (GoString × Nat) (w8 × Bool)) (Γm : GMap GoString (Option OsMeta))
      (F : GMap GoString (Option OsFile)) (st st' : OsState) (Γf : GMap w64 OsFd)
      (Γt Γt' : GMap Nat TokInfo),
    ⌜CrashRel Γb Γm F D ∧ OsCoh st Γb Γm Γf Γt ∧ OsCrash st st' ∧ Q st st' ∧
      (∀ p fo, F !! p = some fo → st'.files !! p = some fo) ∧
      (∀ t ti, Γt' !! t = some ti → Γt !! t = some ti)⌝ ∗
    gAuth hL hL.γb Γb ∗ gAuth hL hL.γm Γm ∗
    ([∗map] p ↦ fo ∈ F, fileStart hL' p fo) ∗
    gAuth hL hL.γt Γt' ∗ tokRes hL st Γt')

/-- The restart's resources. -/
def osCrashStartQT (Q : OsState → OsState → Prop) (hL hL' : OsGS GF) : IProp GF :=
  iprop(gVar hL' (1 : Qp).half ((∅ : GMap Loc (Option w8 × Bool)), 0) ∗ crashRestQT Q hL hL' [])

/-- Taking the file at `p` with a fragment of its `OsMeta` and its bytes in runs, giving them
back. -/
theorem crashRestQT_take_runs_keep (Q : OsState → OsState → Prop) (hL hL' : OsGS GF)
    (D : List GoString) (p : GoString) (hp : p ∉ D) (dq : DFrac) (mo : Option OsMeta)
    (rs : List (Nat × DFrac × List (w8 × Bool))) :
    ⊢ crashRestQT Q hL hL' D -∗ gElem hL hL.γm p dq mo -∗
      ([∗list] r ∈ rs, bytesG hL p r.1 r.2.1 r.2.2) -∗
      ∃ fo, ⌜FileCrashedR mo rs fo ∧ CrashSeenR Q p mo rs [] fo⌝ ∗ fileStart hL' p fo ∗
        crashRestQT Q hL hL' (p :: D) ∗
        gElem hL hL.γm p dq mo ∗ ([∗list] r ∈ rs, bytesG hL p r.1 r.2.1 r.2.2) := by
  unfold crashRestQT
  iintro ⟨%Γb, %Γm, %F, %st, %st', %Γf, %Γt, %Γt', %hrel, Hab, Ham, Hfs, HAt, Htok⟩ Hm Hbs
  obtain ⟨hrel, hcoh, hcr, hQ, hF, hsub⟩ := hrel
  icases gAuth_lookup hL _ _ _ _ _ $$ Ham Hm with %hmo
  icases bytesG_lookup_runs hL p Γb rs $$ Hab Hbs with %hxs
  obtain ⟨fo, hFp, hfc⟩ := hrel p mo hmo hp
  icases (BigSepM.bigSepM_delete (Φ := fun p fo => fileStart hL' p fo) hFp).1 $$ Hfs with ⟨Hf, Hfs⟩
  iexists fo
  iframe Hf Hm Hbs
  isplitr
  · ipureintro
    exact ⟨fileCrashedR_of_g hfc hxs, st, st', Γb, Γm, Γf, Γt, hcoh, hcr, hQ, hF p fo hFp, hmo,
      hxs, fun _ h => nomatch h⟩
  iexists Γb, Γm, GMap.delete p F, st, st', Γf, Γt, Γt'
  iframe Hab Ham Hfs HAt Htok
  ipureintro
  refine ⟨fun q mq hq hqD => ?_, hcoh, hcr, hQ, fun q fq hq => ?_, hsub⟩
  · have hqp : q ≠ p := fun h => hqD (h ▸ List.mem_cons_self)
    obtain ⟨fq, h1, h2⟩ := hrel q mq hq (fun h => hqD (List.mem_cons_of_mem _ h))
    exact ⟨fq, by rw [GMap.lookup_delete_ne _ (Ne.symm hqp)]; exact h1, h2⟩
  · by_cases hqp : q = p
    · subst hqp; simp at hq
    · rw [GMap.lookup_delete_ne _ (Ne.symm hqp)] at hq; exact hF q fq hq

/-- Taking the file a change in flight is on, with the fragment of `OsMeta` the change holds,
giving back the token. -/
theorem crashRestQT_take_tok_keep (Q : OsState → OsState → Prop) (hL hL' : OsGS GF)
    (D : List GoString) (t : Nat) (ti : TokInfo) (hp : ti.c.path ∉ D)
    (rs : List (Nat × DFrac × List (w8 × Bool))) :
    ⊢ crashRestQT Q hL hL' D -∗ gElem hL hL.γt t (DFrac.own 1) ti -∗
      ([∗list] r ∈ rs, bytesG hL ti.c.path r.1 r.2.1 r.2.2) -∗
      ∃ fo, ⌜FileCrashedR (some ti.om) rs fo ∧
          CrashSeenR Q ti.c.path (some ti.om) rs [(t, ti)] fo⌝ ∗
        fileStart hL' ti.c.path fo ∗ crashRestQT Q hL hL' (ti.c.path :: D) ∗
        gElem hL hL.γt t (DFrac.own 1) ti ∗
        ([∗list] r ∈ rs, bytesG hL ti.c.path r.1 r.2.1 r.2.2) := by
  iintro Hr Ht Hbs
  unfold crashRestQT
  icases Hr with ⟨%Γb, %Γm, %F, %st, %st', %Γf, %Γt, %Γt', %hrel, Hab, Ham, Hfs, HAt, Htok⟩
  obtain ⟨hrel, hcoh, hcr, hQ, hF, hsub⟩ := hrel
  icases gAuth_lookup hL _ _ _ _ _ $$ HAt Ht with %hti
  unfold tokRes
  icases (BigSepM.bigSepM_delete (Φ := fun _ (ti : TokInfo) => iprop(
      gElem hL hL.γm ti.c.path (DFrac.own ti.q) (some ti.om) ∗
      bytesG hL ti.c.path (affLo st ti.c) (DFrac.own 1) (ti.saved.map (·, false)))) hti).1
    $$ Htok with ⟨⟨Hm, Hb⟩, Htok⟩
  icases gAuth_lookup hL _ _ _ _ _ $$ Ham Hm with %hmo
  icases bytesG_lookup_runs hL ti.c.path Γb rs $$ Hab Hbs with %hxs
  obtain ⟨fo, hFp, hfc⟩ := hrel ti.c.path _ hmo hp
  icases (BigSepM.bigSepM_delete (Φ := fun p fo => fileStart hL' p fo) hFp).1 $$ Hfs with ⟨Hf, Hfs⟩
  iexists fo
  iframe Hf Ht Hbs
  isplitr
  · ipureintro
    refine ⟨fileCrashedR_of_g hfc hxs, st, st', Γb, Γm, Γf, Γt, hcoh, hcr, hQ, hF _ fo hFp, hmo,
      hxs, ?_⟩
    intro x hx
    simp only [List.mem_singleton] at hx
    subst hx
    exact hsub t ti hti
  iexists Γb, Γm, GMap.delete ti.c.path F, st, st', Γf, Γt, Γt'
  iframe Hab Ham Hfs HAt
  isplitr
  · ipureintro
    refine ⟨fun q mq hq hqD => ?_, hcoh, hcr, hQ, fun q fq hq => ?_, hsub⟩
    · have hqp : q ≠ ti.c.path := fun h => hqD (h ▸ List.mem_cons_self)
      obtain ⟨fq, h1, h2⟩ := hrel q mq hq (fun h => hqD (List.mem_cons_of_mem _ h))
      exact ⟨fq, by rw [GMap.lookup_delete_ne _ (Ne.symm hqp)]; exact h1, h2⟩
    · by_cases hqp : q = ti.c.path
      · subst hqp; simp at hq
      · rw [GMap.lookup_delete_ne _ (Ne.symm hqp)] at hq; exact hF q fq hq
  iapply (BigSepM.bigSepM_delete (Φ := fun _ (ti : TokInfo) => iprop(
      gElem hL hL.γm ti.c.path (DFrac.own ti.q) (some ti.om) ∗
      bytesG hL ti.c.path (affLo st ti.c) (DFrac.own 1) (ti.saved.map (·, false)))) hti).2
  iframe

/-- The crash of the extension's ghost state under the premise, keeping the changes in
flight. -/
theorem os_local_crashQT (Q : OsState → OsState → Prop) (hPre : OsGpreS GF) (hL : OsGS GF)
    (st st' : OsState) (hc : OsCrash st st') (hQ : Q st st') :
    ⊢@{IProp GF} osCtx hL st ==∗ ∃ hL' : OsGS GF, osCtx hL' st' ∗ osCrashStartQT Q hL hL' := by
  unfold osCtx
  iintro ⟨%Γb, %Γm, %Γf, %Γt, %hwc, Hab, Ham, -, HAt, Htok, -⟩
  obtain ⟨hinit, hrel⟩ := osCrash_rel hwc.2 hc
  imod os_local_init hPre st' hinit with ⟨%hL', Hctx, Hst⟩
  unfold osCtx
  icases osStart_files hL' st' $$ Hst with ⟨Hfs, Hv⟩
  imodintro
  iexists hL'
  iframe Hctx
  unfold osCrashStartQT crashRestQT
  iframe Hv
  iexists Γb, Γm, st'.files, st, st', Γf, Γt, Γt
  iframe Hab Ham Hfs HAt Htok
  ipureintro; exact ⟨hrel, hwc.2, hc, hQ, fun _ _ h => h, fun _ _ h => h⟩

/-- The crash interpretation of the Linux file extension under the premise `Q`, keeping the
changes in flight. -/
@[instance_reducible] def os_crash_interpQT (Q : OsState → OsState → Prop) :
    @ExtCrashInterp osFsExt (osFsSemWith Q) os_interp :=
  @ExtCrashInterp.mk osFsExt (osFsSemWith Q) os_interp (fun hL hL' => osCrashStartQT Q hL hL')
    (fun _ hPre hL st st' (hc : OsCrash st st' ∧ Q st st') =>
      os_local_crashQT Q hPre hL st st' hc.1 hc.2)

end crash

/-! ## In a generation's terms -/

section gen
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt osFsExt] [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF]

/-- `crashRestQT_take_runs_keep` from the old generation `L` to the new one `L'`. -/
theorem osCrashQT_take_runs_keep (Q : OsState → OsState → Prop) (L L' : GooseLocalGS GF)
    (D : List GoString) (p : GoString) (hp : p ∉ D) (dq : DFrac) (mo : Option OsMeta)
    (rs : List (Nat × DFrac × List (w8 × Bool))) :
    ⊢ crashRestQT Q (gooseOsGS (L := L)) (gooseOsGS (L := L')) D -∗ osMeta (L := L) p dq mo -∗
      ([∗list] r ∈ rs, osBytes (L := L) p r.1 r.2.1 r.2.2) -∗
      ∃ fo, ⌜FileCrashedR mo rs fo ∧ CrashSeenR Q p mo rs [] fo⌝ ∗ osFileStart (L := L') p fo ∗
        crashRestQT Q (gooseOsGS (L := L)) (gooseOsGS (L := L')) (p :: D) ∗
        osMeta (L := L) p dq mo ∗ ([∗list] r ∈ rs, osBytes (L := L) p r.1 r.2.1 r.2.2) := by
  unfold osMeta osBytes
  iintro Hr Hm Hb
  icases crashRestQT_take_runs_keep Q _ _ D p hp dq mo rs $$ Hr Hm Hb
    with ⟨%fo, %h, Hf, Hr, Hm, Hb⟩
  iexists fo
  iframe Hr Hm Hb
  isplitr
  · ipureintro; exact h
  iapply (fileStart_eq (L := L') p fo).1 $$ Hf

/-- `crashRestQT_take_tok_keep` from the old generation `L` to the new one `L'`. -/
theorem osCrashQT_take_tok_keep (Q : OsState → OsState → Prop) (L L' : GooseLocalGS GF)
    (D : List GoString) (t : Nat) (ti : TokInfo) (hp : ti.c.path ∉ D)
    (rs : List (Nat × DFrac × List (w8 × Bool))) :
    ⊢ crashRestQT Q (gooseOsGS (L := L)) (gooseOsGS (L := L')) D -∗ osTok (L := L) t ti -∗
      ([∗list] r ∈ rs, osBytes (L := L) ti.c.path r.1 r.2.1 r.2.2) -∗
      ∃ fo, ⌜FileCrashedR (some ti.om) rs fo ∧
          CrashSeenR Q ti.c.path (some ti.om) rs [(t, ti)] fo⌝ ∗
        osFileStart (L := L') ti.c.path fo ∗
        crashRestQT Q (gooseOsGS (L := L)) (gooseOsGS (L := L')) (ti.c.path :: D) ∗
        osTok (L := L) t ti ∗ ([∗list] r ∈ rs, osBytes (L := L) ti.c.path r.1 r.2.1 r.2.2) := by
  unfold osTok osBytes
  iintro Hr Ht Hb
  icases crashRestQT_take_tok_keep Q _ _ D t ti hp rs $$ Hr Ht Hb
    with ⟨%fo, %h, Hf, Hr, Ht, Hb⟩
  iexists fo
  iframe Hr Ht Hb
  isplitr
  · ipureintro; exact h
  iapply (fileStart_eq (L := L') _ fo).1 $$ Hf

end gen

/-! ## Adequacy -/

@[reducible] def osFsExtsCrashInterpQT (Q : OsState → OsState → Prop) :
    @GooseCrashInterp osFsExts (osFsExtsSemanticsWith Q) osFsExtsInterp :=
  @GooseCrashInterp.mk osFsExts (osFsExtsSemanticsWith Q) osFsExtsInterp (os_crash_interpQT Q, ⟨⟩)

section adequacy
attribute [local instance] osFsExts osFsExtsSemantics osFsExtsInterp osFsExts_hasOsFs
variable [GoGlobalContext] {GF : BundledGFunctors}

/-- **Crash adequacy for a program with Linux files, under a premise `Q` on crashes, keeping the
changes in flight**: as `osFsQ_crash_adequacy`, with the crash interpretation
`os_crash_interpQT`: after a crash, the proof of a generation gets `crashRestQT Q`, from which it
takes the files, with the tokens of the changes in flight, and the crash's facts. -/
theorem osFsQ_crash_adequacyT (Q : OsState → OsState → Prop) [hPre : GooseGpreS GF] (N T : Nat)
    (e : Expr) (σ : state) (g : GlobalState) (φ : val → Prop) (hφ : ∀ p, ¬ φ (PanicV p))
    (Hinit : OsInit (extLocal osFsExt σ.world))
    (P : ∀ [GooseGlobalGS .hasLC GF], GooseLocalGS GF → IProp GF)
    (Hstart : ∀ [hG : HeapGS .hasLC GF],
      receiptBound GF = N →
      threadBound GF = T →
      hG.goose_localGS.goose_go_local_context = σ.goState.goLctx →
      ⊢ osInv (L := hG.goose_localGS) -∗
        ([∗map] p ↦ fo ∈ (extLocal osFsExt σ.world).files,
          osFileStart (L := hG.goose_localGS) p fo) -∗
        ownGoState σ.goState.packageState ={⊤}=∗ P hG.goose_localGS)
    (Hwp : ∀ [hG : HeapGS .hasLC GF],
      receiptBound GF = N →
      threadBound GF = T →
      hG.goose_localGS.goose_go_local_context = σ.goState.goLctx →
      ⊢ P hG.goose_localGS -∗ threadTok ={⊤}=∗
        WP e @ Stuckness.NotStuck; ⊤ {{ v, ⌜φ v⌝ }} ∗
        ∀ L' : GooseLocalGS GF, crashed (hC := hG.goose_localGS.goose_crashGS) -∗
          osInv (L := L') -∗
          crashRestQT Q (gooseOsGS (L := hG.goose_localGS)) (gooseOsGS (L := L')) [] -∗
          ownGoState (hG := L'.goose_go_stateGS) ∅ ={⊤}=∗ P L')
    (n : Nat) (κs : List Observation) (t2 : List Expr) (σ2 : CfgState) (b : Bool)
    (Hsteps : @RealCrashNsteps osFsExts (osFsExtsSemanticsWith Q) _ e n
      ([e], ((σ, g) : CfgState)) κs (t2, σ2) b)
    (Hbound : n < N) (Hthreads : σ.threads = 1)
    (Hlive : @RealCrashThreadsBelow osFsExts (osFsExtsSemanticsWith Q) _ e T n
      ([e], ((σ, g) : CfgState))) :
    (∀ v t2', t2 = Val v :: t2' → φ v) ∧
      (∀ e2, e2 ∈ t2 → @RealNotStuck osFsExts (osFsExtsSemanticsWith Q) _ e2 σ2) ∧
      (∀ e2, e2 ∈ t2 → ¬ UnrecoveredPanic e2) := by
  refine @goose_crash_adequacy osFsExts osFsExtsInterp (osFsExtsSemanticsWith Q) _
    (osFsExtsCrashInterpQT Q) GF hPre N T e σ g φ hφ ⟨trivial, trivial⟩ ⟨Hinit, trivial⟩ P
    ?_ ?_ n κs t2 σ2 b Hsteps Hbound Hthreads Hlive
  · intro hG HN HT Hlctx
    iintro _ Hs Hgs
    imod osFs_start σ $$ Hs with ⟨#Hinv, Hfs⟩
    iapply Hstart HN HT Hlctx $$ Hinv Hfs Hgs
  · intro hG HN HT Hlctx
    have hw := wp_sem_congr (hlc := .hasLC) (GF := GF) (Sa := osFsExtsSemantics) (Sb := osFsExtsSemanticsWith Q)
      (osFsWith_extStep_iff Q) Stuckness.NotStuck ⊤ e (fun v => iprop(⌜φ v⌝))
    iintro HP Htok
    imod Hwp HN HT Hlctx $$ HP Htok with ⟨Hwp, Hcrash⟩
    imodintro
    isplitl [Hwp]
    · rw [← hw]; iexact Hwp
    iintro %L' Hcr Hcs Hgs
    have Hc : @extsCrashStart osFsExts (osFsExtsSemanticsWith Q) osFsExtsInterp
        (osFsExtsCrashInterpQT Q) GF hG.goose_localGS L' ⊢
        osCrashStartQT Q (gooseOsGS (L := hG.goose_localGS)) (gooseOsGS (L := L')) := by
      unfold extsCrashStart Exts.crashStart; exact sep_elim_left
    icases Hc $$ Hcs with Hcs
    unfold osCrashStartQT
    icases Hcs with ⟨Hv, Hr⟩
    imod osInv_alloc (L := L') ⊤ $$ Hv with #Hinv
    iapply Hcrash $$ %L' Hcr Hinv Hr Hgs

end adequacy

end Perennial
