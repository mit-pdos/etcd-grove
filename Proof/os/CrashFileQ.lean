/-
Crash-aware specs of `os` under a premise `Q` on crashes: the crash invariant of a file whose
`Good` predicate needs the crash's facts (`CrashSeenR`, `GooseLang/Ext/OsFs/CrashQT.lean`), not
only what the old generation's resources say of the crash (`FileCrashedR`).

`CrashOk Good s` (`CrashFile.lean`) asks that every file a crash may leave of the state `s`, as
the file's resources describe it, be `Good`. minibolt's `Good` needs more: P1
(`Proof/.../bboltfs/BootP1.lean`) speaks of the crashed state itself (a meta slot of the image
that validates is the durable one, the page cache's or a write in flight's), which `CrashSeenR`
gives, coherent with the resources (`OsCoh`). `CrashOkQ Q p Good s` is `CrashOk` with those facts
as a further hypothesis, so `CrashOk` implies it (`crashOk_Q`). `cfInvQ` is `cfInv` with
`CrashOkQ`, and `cfInvQ_crash_keep` takes the file after a crash from it through `crashRestQT`.
-/
module

public import Proof.os.CrashFile
public import GooseLang.Ext.OsFs.CrashQT

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

/-- The change in flight of the state `s` of the file at `p`, as its token records it (`pwTok`
with the whole `OsMeta`). -/
def cToks (p : GoString) : CFile → List (Nat × TokInfo)
  | some (m, bs, some (t, off, data)) =>
      [(t, ⟨⟨p, .write off data⟩, 1, (cfRange m bs off data.length).map Prod.fst,
        pwMeta m off data.length⟩)]
  | _ => []

/-- Every file a crash under the premise `Q` may leave of the state `s` of the file at `p` is
`Good`, given the crash's facts. -/
def CrashOkQ (Q : OsState → OsState → Prop) (p : GoString) (Good : Option OsFile → Prop)
    (s : CFile) : Prop :=
  ∀ fo, FileCrashedR (cMeta s) (cRuns s) fo → CrashSeenR Q p (cMeta s) (cRuns s) (cToks p s) fo →
    Good fo

theorem crashOk_Q {Q : OsState → OsState → Prop} {p : GoString} {Good : Option OsFile → Prop}
    {s : CFile} (h : CrashOk Good s) : CrashOkQ Q p Good s :=
  fun fo hc _ => h fo hc

section res
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt osFsExt] [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]

/-- `cfInv` under the premise `Q`: the invariant holds `CrashOkQ` of the state. -/
def cfInvQ (N : Namespace) (p : GoString) (γ : GName) (Q : OsState → OsState → Prop)
    (Good : Option OsFile → Prop) : IProp GF :=
  inv N iprop(∃ s : CFile, ghostVar γ (1 : Qp).half s ∗ invRes (L := L) p s ∗
    ⌜CrashOkQ Q p Good s⌝)

instance cfInvQ_persistent (N : Namespace) (p : GoString) (γ : GName)
    (Q : OsState → OsState → Prop) (Good : Option OsFile → Prop) :
    Persistent (cfInvQ (L := L) N p γ Q Good) := by unfold cfInvQ; infer_instance

/-- A file a generation starts with, in an invariant, if a crash of it is `Good`. -/
theorem cfInvQ_alloc (N : Namespace) (p : GoString) (Q : OsState → OsState → Prop)
    (Good : Option OsFile → Prop) (fo : Option OsFile) (hok : CrashOkQ Q p Good (startState fo)) :
    ⊢ osFileStart (L := L) p fo ={⊤}=∗ ∃ γ, cfInvQ (L := L) N p γ Q Good ∗
      cfOwn (L := L) p γ (startState fo) := by
  iintro Hf
  imod ghostVar_alloc (GF := GF) (startState fo) with ⟨%γ, Hv⟩
  icases (ghostVar_split_half (A := CFile) γ 1 _).1 $$ Hv with ⟨Hv1, Hv2⟩
  ihave ⟨Hi, Ht⟩ := (show osFileStart (L := L) p fo ⊢
      invRes (L := L) p (startState fo) ∗ thrRes (L := L) p (startState fo) by
    cases fo with
    | none => exact (osMeta_halves p none).1
    | some f =>
      dsimp only [osFileStart, startState, invRes, thrRes]
      iintro ⟨Hm, Hb⟩
      icases (osMeta_halves p _).1 $$ Hm with ⟨Hm1, Hm2⟩
      icases (osBytes_halves p 0 _).1 $$ Hb with ⟨Hb1, Hb2⟩
      iframe) $$ Hf
  imod inv_alloc N ⊤ (iprop(∃ s : CFile, ghostVar γ (1 : Qp).half s ∗ invRes (L := L) p s ∗
      ⌜CrashOkQ Q p Good s⌝)) $$ [Hv1 Hi] with #Hinv
  · inext; iexists (startState fo); iframe; ipureintro; exact hok
  imodintro
  iexists γ
  unfold cfInvQ cfOwn
  iframe Hinv Hv2 Ht
  ipureintro; exact startState_wf fo

end res

section crash
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt osFsExt] [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF]

/-- **The file after a crash under the premise `Q`**, from the invariant's half of the old
generation's state `s`: the new generation's file, which is `Good` if `CrashOkQ` holds of `s`;
the invariant's half comes back, so that the invariant can be closed again. -/
theorem cfInvQ_crash_keep (Q : OsState → OsState → Prop) (L L' : GooseLocalGS GF)
    (D : List GoString) (p : GoString) (hp : p ∉ D) (Good : Option OsFile → Prop) (s : CFile)
    (hok : CrashOkQ Q p Good s) :
    ⊢ crashRestQT Q (gooseOsGS (L := L)) (gooseOsGS (L := L')) D -∗ invRes (L := L) p s -∗
      ∃ fo, ⌜Good fo⌝ ∗ osFileStart (L := L') p fo ∗
        crashRestQT Q (gooseOsGS (L := L)) (gooseOsGS (L := L')) (p :: D) ∗
        invRes (L := L) p s := by
  iintro Hr Hs
  rcases s with _ | ⟨m, bs, _ | ⟨t, off, data⟩⟩
  · dsimp only [invRes]
    icases osCrashQT_take_runs_keep Q L L' D p hp _ none [] $$ Hr Hs []
      with ⟨%fo, %h, Hf, Hr, Hs, -⟩
    · iapply BigSepL.bigSepL_nil.2; iempintro
    iexists fo; iframe; ipureintro; exact hok fo h.1 h.2
  · dsimp only [invRes]
    icases Hs with ⟨Hm, Hb⟩
    icases osCrashQT_take_runs_keep Q L L' D p hp _ (some m) [(0, DFrac.own (1 : Qp).half, bs)]
      $$ Hr Hm [Hb] with ⟨%fo, %h, Hf, Hr, Hm, Hb⟩
    · iapply BigSepL.bigSepL_singleton.2; iexact Hb
    icases BigSepL.bigSepL_singleton.1 $$ Hb with Hb
    iexists fo; iframe; ipureintro; exact hok fo h.1 h.2
  · dsimp only [invRes]
    icases Hs with ⟨Ht, Hb1, Hb2⟩
    dsimp only [pwTok]
    icases osCrashQT_take_tok_keep Q L L' D t _ hp (cRuns (some (m, bs, some (t, off, data))))
      $$ Hr Ht [Hb1 Hb2] with ⟨%fo, %h, Hf, Hr, Ht, Hbs⟩
    · unfold cRuns
      iapply BigSepL.bigSepL_cons.2; iframe Hb1
      iapply BigSepL.bigSepL_singleton.2; iexact Hb2
    unfold cRuns
    icases BigSepL.bigSepL_cons.1 $$ Hbs with ⟨Hb1, Hbs⟩
    icases BigSepL.bigSepL_singleton.1 $$ Hbs with Hb2
    iexists fo; iframe; ipureintro; exact hok fo h.1 h.2

end crash

end Perennial
