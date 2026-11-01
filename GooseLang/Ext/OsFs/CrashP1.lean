/-
Crash adequacy for the Linux file extension under a premise `Q` on crashes: the extension's
semantics with the same step (`OsStep`) and the crash relation `OsCrash st st' ∧ Q st st'`
(`osFsSemWith Q`). A client's end-to-end theorem closes its program with this semantics, so that
its statement shows the premise (minibolt's P1, `Proof/.../bboltfs/BootP1.lean`).

* The specs are proved for `osFs_semantics`, and need not be redone: the WP and the ghost state
  depend on the semantics only through its step, which is the same. `osFsQ_crash_adequacy` takes
  the client's proof of each generation in `osFs_semantics`'s terms (as `osFs_crash_adequacy`
  does) and turns it into one for `osFsSemWith Q` by conversion (the two are definitionally
  equal: `ExtSemantics.step (osFsSemWith Q)` is `OsStep`).
* The crash interpretation (`os_crash_interpQ`) is `os_crash_interp`'s, with the premise added to
  what the restarted boot program gets (`crashRestQ`): besides `CrashRel`, the crashed state `st`,
  its coherence with the old generation's ghost maps (`OsCoh`), and `Q st st'` of the state `st'`
  the new generation starts from. `osCrashQ_take` takes a file as `osCrash_take` does, and
  returns those facts too (`CrashSeen`).

Nothing here is trusted: the premise is a hypothesis of the client's theorem, visible in its
statement through the semantics.
-/
module

public import GooseLang.Ext.OsFs.Adequacy
public import GooseLang.Ext.OsFs.SemCongr

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode

/-- The Linux file extension's semantics with crashes restricted by the premise `Q`. -/
@[instance_reducible] def osFsSemWith (Q : OsState → OsState → Prop) : ExtSemantics osFsExt where
  step := OsStep
  crash st st' := OsCrash st st' ∧ Q st st'

/-! ## The crash interpretation -/

/-- What the restarted boot program learns of the file at `p`, taken from the new files with the
old generation's `OsMeta` `mo` and bytes `xs` from `off` on: the new file `fo` is the one at `p`
in the state `st'` the new generation starts from, which a crash (`OsCrash`, and `Q`) made of the
crashed state `st`; `st` is coherent with the old ghost maps, in which `p`'s `OsMeta` is `mo` and
its bytes from `off` on are `xs`. -/
def CrashSeen (Q : OsState → OsState → Prop) (p : GoString) (mo : Option OsMeta) (off : Nat)
    (xs : List (w8 × Bool)) (fo : Option OsFile) : Prop :=
  ∃ (st st' : OsState) (Γb : GMap (GoString × Nat) (w8 × Bool)) (Γm : GMap GoString (Option OsMeta))
    (Γf : GMap w64 OsFd) (Γt : GMap Nat TokInfo),
    OsCoh st Γb Γm Γf Γt ∧ OsCrash st st' ∧ Q st st' ∧ st'.files !! p = some fo ∧
    Γm !! p = some mo ∧ ∀ k (hk : k < xs.length), Γb !! (p, off + k) = some xs[k]

section crash
variable {GF : BundledGFunctors}

/-- `crashRest` with the crash's facts: the crashed state `st`, coherent with the old maps, and
the state `st'` after the crash, which `Q` relates to it and whose files include the files left. -/
def crashRestQ (Q : OsState → OsState → Prop) (hL hL' : OsGS GF) (D : List GoString) : IProp GF :=
  iprop(∃ (Γb : GMap (GoString × Nat) (w8 × Bool)) (Γm : GMap GoString (Option OsMeta))
      (F : GMap GoString (Option OsFile)) (st st' : OsState) (Γf : GMap w64 OsFd)
      (Γt : GMap Nat TokInfo),
    ⌜CrashRel Γb Γm F D ∧ OsCoh st Γb Γm Γf Γt ∧ OsCrash st st' ∧ Q st st' ∧
      ∀ p fo, F !! p = some fo → st'.files !! p = some fo⌝ ∗
    gAuth hL hL.γb Γb ∗ gAuth hL hL.γm Γm ∗
    [∗map] p ↦ fo ∈ F, fileStart hL' p fo)

/-- `osCrashStart` with the crash's facts. -/
def osCrashStartQ (Q : OsState → OsState → Prop) (hL hL' : OsGS GF) : IProp GF :=
  iprop(gVar hL' (1 : Qp).half ((∅ : GMap Loc (Option w8 × Bool)), 0) ∗ crashRestQ Q hL hL' [])

/-- `crashRest_take`, with the crash's facts (`CrashSeen`). -/
theorem crashRestQ_take (Q : OsState → OsState → Prop) (hL hL' : OsGS GF) (D : List GoString)
    (p : GoString) (hp : p ∉ D) (dq dq' : DFrac) (mo : Option OsMeta) (off : Nat)
    (xs : List (w8 × Bool)) :
    ⊢ crashRestQ Q hL hL' D -∗ gElem hL hL.γm p dq mo -∗ bytesG hL p off dq' xs -∗
      ∃ fo, ⌜FileCrashed mo off xs fo ∧ CrashSeen Q p mo off xs fo⌝ ∗ fileStart hL' p fo ∗
        crashRestQ Q hL hL' (p :: D) := by
  unfold crashRestQ
  iintro ⟨%Γb, %Γm, %F, %st, %st', %Γf, %Γt, %hrel, Hab, Ham, Hfs⟩ Hm Hbs
  obtain ⟨hrel, hcoh, hcr, hQ, hF⟩ := hrel
  icases gAuth_lookup hL _ _ _ _ _ $$ Ham Hm with %hmo
  icases bytesG_lookup hL _ _ _ _ _ $$ Hab Hbs with %hxs
  obtain ⟨fo, hFp, hfc⟩ := hrel p mo hmo hp
  icases (BigSepM.bigSepM_delete (Φ := fun p fo => fileStart hL' p fo) hFp).1 $$ Hfs with ⟨Hf, Hfs⟩
  iexists fo
  iframe Hf
  isplitr
  · ipureintro
    exact ⟨fileCrashed_of_g hfc hxs, st, st', Γb, Γm, Γf, Γt, hcoh, hcr, hQ, hF p fo hFp, hmo, hxs⟩
  iexists Γb, Γm, GMap.delete p F, st, st', Γf, Γt
  iframe Hab Ham Hfs
  ipureintro
  refine ⟨fun q mq hq hqD => ?_, hcoh, hcr, hQ, fun q fq hq => ?_⟩
  · have hqp : q ≠ p := fun h => hqD (h ▸ List.mem_cons_self)
    obtain ⟨fq, h1, h2⟩ := hrel q mq hq (fun h => hqD (List.mem_cons_of_mem _ h))
    exact ⟨fq, by rw [GMap.lookup_delete_ne _ (Ne.symm hqp)]; exact h1, h2⟩
  · by_cases hqp : q = p
    · subst hqp; simp at hq
    · rw [GMap.lookup_delete_ne _ (Ne.symm hqp)] at hq; exact hF q fq hq

/-- The crash of the extension's ghost state under the premise: as `os_local_crash`, keeping the
crashed state and the premise. -/
theorem os_local_crashQ (Q : OsState → OsState → Prop) (hPre : OsGpreS GF) (hL : OsGS GF)
    (st st' : OsState) (hc : OsCrash st st') (hQ : Q st st') :
    ⊢@{IProp GF} osCtx hL st ==∗ ∃ hL' : OsGS GF, osCtx hL' st' ∗ osCrashStartQ Q hL hL' := by
  unfold osCtx
  iintro ⟨%Γb, %Γm, %Γf, %Γt, %hwc, Hab, Ham, -, -, -, -⟩
  obtain ⟨hinit, hrel⟩ := osCrash_rel hwc.2 hc
  imod os_local_init hPre st' hinit with ⟨%hL', Hctx, Hst⟩
  unfold osCtx
  icases osStart_files hL' st' $$ Hst with ⟨Hfs, Hv⟩
  imodintro
  iexists hL'
  iframe Hctx
  unfold osCrashStartQ crashRestQ
  iframe Hv
  iexists Γb, Γm, st'.files, st, st', Γf, Γt
  iframe Hab Ham Hfs
  ipureintro; exact ⟨hrel, hwc.2, hc, hQ, fun _ _ h => h⟩

/-- The crash interpretation of the Linux file extension under the premise `Q`. -/
@[instance_reducible] def os_crash_interpQ (Q : OsState → OsState → Prop) :
    @ExtCrashInterp osFsExt (osFsSemWith Q) os_interp :=
  @ExtCrashInterp.mk osFsExt (osFsSemWith Q) os_interp (fun hL hL' => osCrashStartQ Q hL hL')
    (fun _ hPre hL st st' (hc : OsCrash st st' ∧ Q st st') =>
      os_local_crashQ Q hPre hL st st' hc.1 hc.2)

end crash

/-! ## In a generation's terms -/

section gen
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt osFsExt] [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF]

/-- `crashRestQ_take` from the old generation `L` to the new one `L'` (`osCrash_take` with the
crash's facts). -/
theorem osCrashQ_take (Q : OsState → OsState → Prop) (L L' : GooseLocalGS GF) (D : List GoString)
    (p : GoString) (hp : p ∉ D) (dq dq' : DFrac) (mo : Option OsMeta) (off : Nat)
    (xs : List (w8 × Bool)) :
    ⊢ crashRestQ Q (gooseOsGS (L := L)) (gooseOsGS (L := L')) D -∗ osMeta (L := L) p dq mo -∗
      osBytes (L := L) p off dq' xs -∗
      ∃ fo, ⌜FileCrashed mo off xs fo ∧ CrashSeen Q p mo off xs fo⌝ ∗
        osFileStart (L := L') p fo ∗
        crashRestQ Q (gooseOsGS (L := L)) (gooseOsGS (L := L')) (p :: D) := by
  unfold osMeta osBytes
  iintro Hr Hm Hb
  icases crashRestQ_take Q _ _ D p hp dq dq' mo off xs $$ Hr Hm Hb with ⟨%fo, %h, Hf, Hr⟩
  iexists fo
  iframe Hr
  isplitr
  · ipureintro; exact h
  iapply (fileStart_eq (L := L') p fo).1 $$ Hf

end gen

/-! ## Adequacy -/

/-- The semantics of a program whose only extension is the Linux file extension, with crashes
restricted by `Q`. -/
@[reducible] def osFsExtsSemanticsWith (Q : OsState → OsState → Prop) :
    @GooseSemantics osFsExts := @GooseSemantics.mk osFsExts (osFsSemWith Q, ⟨⟩)

@[reducible] def osFsExtsCrashInterpWith (Q : OsState → OsState → Prop) :
    @GooseCrashInterp osFsExts (osFsExtsSemanticsWith Q) osFsExtsInterp :=
  @GooseCrashInterp.mk osFsExts (osFsExtsSemanticsWith Q) osFsExtsInterp (os_crash_interpQ Q, ⟨⟩)

section adequacy
attribute [local instance] osFsExts osFsExtsSemantics osFsExtsInterp osFsExts_hasOsFs
variable [GoGlobalContext] {GF : BundledGFunctors}

/-- The extension's steps are the same in both semantics. -/
theorem osFsWith_extStep_iff (Q : OsState → OsState → Prop) (ext op : String) (v : val)
    (σg : CfgState) (e' : Expr) (σg' : CfgState) :
    @extStep osFsExts osFsExtsSemantics _ ext op v σg e' σg' ↔
      @extStep osFsExts (osFsExtsSemanticsWith Q) _ ext op v σg e' σg' := by
  unfold extStep
  refine exists_congr fun E => exists_congr fun h => ?_
  generalize ExtIn.ofNamed h = m
  change ExtIn E [osFsExt] at m
  cases m with
  | here => exact Iff.rfl
  | there m => cases m

/-- **Crash adequacy for a program with Linux files, under a premise `Q` on crashes**: as
`osFs_crash_adequacy`, for executions of the semantics whose crash relation is
`OsCrash ∧ Q` (`osFsExtsSemanticsWith Q`). The proof of each generation is in the terms of the
extension's own semantics (`osFsExtsSemantics`, which its specs are for), and after a crash gets
`crashRestQ Q`: the files, with the crashed state and the premise (`osCrashQ_take`). -/
theorem osFsQ_crash_adequacy (Q : OsState → OsState → Prop) [hPre : GooseGpreS GF] (N T : Nat)
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
          crashRestQ Q (gooseOsGS (L := hG.goose_localGS)) (gooseOsGS (L := L')) [] -∗
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
    (osFsExtsCrashInterpWith Q) GF hPre N T e σ g φ hφ ⟨trivial, trivial⟩ ⟨Hinit, trivial⟩ P
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
        (osFsExtsCrashInterpWith Q) GF hG.goose_localGS L' ⊢
        osCrashStartQ Q (gooseOsGS (L := hG.goose_localGS)) (gooseOsGS (L := L')) := by
      unfold extsCrashStart Exts.crashStart; exact sep_elim_left
    icases Hc $$ Hcs with Hcs
    unfold osCrashStartQ
    icases Hcs with ⟨Hv, Hr⟩
    imod osInv_alloc (L := L') ⊤ $$ Hv with #Hinv
    iapply Hcrash $$ %L' Hcr Hinv Hr Hgs

end adequacy

end Perennial
