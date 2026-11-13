/-
Crash-aware specs of `os` under a premise `Q` on crashes: the crash invariant of a file whose
`Good` predicate needs the crash's facts (`CrashSeenR`, `GooseLang/Ext/Fs/CrashTok.lean`), not
only what the old generation's resources say of the crash (`FileCrashedR`).

`FileOk Good x` (`CrashFile.lean`) asks that every file a crash may leave of the file `x`, as its
resources describe it, be `Good`. minibolt's `Good` needs more: P1
(`Proof/.../bboltfs/BootP1.lean`) speaks of the crashed state itself (a meta slot of the image
that validates is the durable one, the page cache's or a write in flight's), which `CrashSeenR`
gives, coherent with the resources (`OsCoh`). `FileOkQ Q Good i x` is `FileOk` of the file of
inode `i` with those facts as a further hypothesis, so `FileOk` implies it (`fileOk_Q`), and
`CrashOkQ` is `CrashOk` with it (the tree's part, `TreeOk`, is the same). `cfInvQ` is `cfInv` with
`CrashOkQ`, and `cfInvQ_crash_keep` takes the tree and the file after a crash from it.
-/
module

public import Proof.os.CrashFile

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open Fs

/-- The change in flight of the file `x` of inode `i`, as its token records it (`pwTok`). -/
def cToks (i : Ino) : CX → List (Nat × TokInfo)
  | (m, bs, some (t, off, data, n)) =>
      [(t, ⟨i, .write off data, n, m, pwAnn data n (cfRange m bs off data.length)⟩)]
  | _ => []

/-- Every file a crash under the premise `Q` may leave of the file `x` of inode `i` is `Good`,
given the crash's facts. -/
def FileOkQ (Q : OsState → OsState → Prop) (Good : Option OsFile → Prop) (i : Ino) (x : CX) : Prop :=
  ∀ f, FileCrashedR (fMeta x) (fRuns x) (some f) →
    CrashSeenR Q i (fMeta x) (fRuns x) (cToks i x) (some f) → Good (some f)

/-- What a crash under the premise `Q` may leave of the state `s` and the history `V` is `Good`
at `p`. -/
def CrashOkQ (Q : OsState → OsState → Prop) (Good : Option OsFile → Prop) (p : GoString)
    (R : Roots) (s : CFile) (V : Hist) : Prop :=
  TreeOk Good p R s V ∧ ∀ i x, s = some (i, x) → FileOkQ Q Good i x

theorem fileOk_Q {Q : OsState → OsState → Prop} {Good : Option OsFile → Prop} {i : Ino} {x : CX}
    (h : FileOk Good x) : FileOkQ Q Good i x :=
  fun f hc _ => h f hc

theorem crashOk_Q {Q : OsState → OsState → Prop} {Good : Option OsFile → Prop} {p : GoString}
    {R : Roots} {s : CFile} {V : Hist} (h : CrashOk Good p R s V) : CrashOkQ Q Good p R s V :=
  ⟨h.1, fun i x hs => fileOk_Q (h.2 i x hs)⟩

section res
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt] [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]

/-- `cfInv` under the premise `Q`: the invariant holds `CrashOkQ` of the state. -/
def cfInvQ (N : Namespace) (p : GoString) (R : Roots) (γ : GName) (Q : OsState → OsState → Prop)
    (Good : Option OsFile → Prop) : IProp GF :=
  inv N iprop(∃ (s : CFile) (V : Hist), ghostVar γ (1 : Qp).half s ∗ invRes (L := L) s ∗
    osTree (L := L) (DFrac.own (1 : Qp).half) R V ∗ ⌜CrashOkQ Q Good p R s V⌝)

instance cfInvQ_persistent (N : Namespace) (p : GoString) (R : Roots) (γ : GName)
    (Q : OsState → OsState → Prop) (Good : Option OsFile → Prop) :
    Persistent (cfInvQ (L := L) N p R γ Q Good) := by unfold cfInvQ; infer_instance

/-- **The file at `p` and the history, in an invariant**, if a crash of them is `Good`. -/
theorem cfInvQ_alloc (N : Namespace) (p : GoString) (R : Roots) (V : Hist)
    (Q : OsState → OsState → Prop) (Good : Option OsFile → Prop) (s : CFile)
    (hs : ∀ i m bs x, s ≠ some (i, m, bs, some x))
    (hok : CrashOkQ Q Good p R s V) (hwf : CfWf s) (hp : PathOk p R s V) :
    ⊢ osTree (L := L) (DFrac.own 1) R V -∗ startRes (L := L) s ={⊤}=∗ ∃ γ,
      cfInvQ (L := L) N p R γ Q Good ∗ cfOwn (L := L) p R γ s V := by
  iintro Ht Hf
  imod ghostVar_alloc (GF := GF) s with ⟨%γ, Hv⟩
  icases (ghostVar_split_half (A := CFile) γ 1 _).1 $$ Hv with ⟨Hv1, Hv2⟩
  icases (osTree_halves R V).1 $$ Ht with ⟨Ht1, Ht2⟩
  ihave ⟨Hi, Hth⟩ := (show startRes (L := L) s ⊢ invRes (L := L) s ∗ thrRes (L := L) s by
    rcases s with _ | ⟨i, m, bs, _ | x⟩
    · iintro -; isplitl [] <;> iempintro
    · dsimp only [startRes, invRes, thrRes]
      iintro ⟨Hm, Hb⟩
      icases (osMeta_halves i m).1 $$ Hm with ⟨Hm1, Hm2⟩
      icases (osBytes_halves i 0 bs).1 $$ Hb with ⟨Hb1, Hb2⟩
      iframe
    · exact absurd rfl (hs i m bs x)) $$ Hf
  imod inv_alloc N ⊤ (iprop(∃ (s : CFile) (V : Hist), ghostVar γ (1 : Qp).half s ∗
      invRes (L := L) s ∗ osTree (L := L) (DFrac.own (1 : Qp).half) R V ∗
      ⌜CrashOkQ Q Good p R s V⌝)) $$ [Hv1 Hi Ht1] with #Hinv
  · inext; iexists s, V; iframe; ipureintro; exact hok
  imodintro
  iexists γ
  unfold cfInvQ cfOwn
  iframe Hinv Hv2 Hth Ht2
  ipureintro; exact ⟨hwf, hp⟩

end res

section crash
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt] [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF]

/-- **The tree and the file after a crash under the premise `Q`**, from the invariant's halves of
the old generation's state `s` and history `V`: the new generation's history, whole, and the file
at `p` in it, `Good` if `CrashOkQ` holds of `s` and `V`; the old halves come back, so that the
invariant can be closed again. -/
theorem cfInvQ_crash_keep (Q : OsState → OsState → Prop) (L L' : GooseLocalGS GF) (D : List Ino)
    (V' : Hist) (p : GoString) (R : Roots) (Good : Option OsFile → Prop) (s : CFile) (V : Hist)
    (hD : ∀ i, cIno s = some i → i ∉ D) (hok : CrashOkQ Q Good p R s V) :
    ⊢ crashRest Q (gooseOsGS (L := L)) (gooseOsGS (L := L')) D false V' -∗ invRes (L := L) s -∗
      osTree (L := L) (DFrac.own (1 : Qp).half) R V -∗
      ∃ fo, ⌜Good fo⌝ ∗ osTree (L := L') (DFrac.own 1) R V' ∗ startAt L' p R V' fo ∗
        (∃ D', crashRest Q (gooseOsGS (L := L)) (gooseOsGS (L := L')) D' true V') ∗
        invRes (L := L) s ∗ osTree (L := L) (DFrac.own (1 : Qp).half) R V := by
  iintro Hr Hs Ht
  icases osTreeCrash_take Q L L' D V' _ R V $$ Hr Ht with ⟨%htc, Ht', Hr, Ht⟩
  have hto := hok.1 V' htc
  rcases s with _ | ⟨i, m, bs, _ | ⟨t, off, data, n⟩⟩
  · -- no file at `p`: `p` names nothing after the crash
    rcases hto with ⟨hn, hg⟩ | ⟨i, hi, -⟩
    · iexists none
      iframe Ht' Hs Ht
      isplitr
      · ipureintro; exact hg
      isplitr
      · unfold startAt; rw [hn]; ipureintro; rfl
      iexists D; iexact Hr
    · cases hi
  · -- idle
    dsimp only [invRes]
    icases Hs with ⟨Hm, Hb⟩
    icases osCrash_take_runs_keep Q L L' D true V' i (hD i rfl) _ m [(0, DFrac.own (1 : Qp).half, bs)]
      $$ Hr Hm [Hb] with ⟨%fo, %hfo, Hf, Hr, Hm, Hb⟩
    · iapply BigSepL.bigSepL_singleton.2; iexact Hb
    icases BigSepL.bigSepL_singleton.1 $$ Hb with Hb
    obtain ⟨hfc, hnm, hseen⟩ := hfo
    rcases hto with ⟨hn, hg⟩ | ⟨i', hi, hl⟩
    · iexists none
      iframe Ht' Hm Hb Ht
      isplitr
      · ipureintro; exact hg
      isplitr
      · unfold startAt; rw [hn]; ipureintro; rfl
      iexists (i :: D); iexact Hr
    · cases hi
      obtain ⟨f, rfl⟩ := Option.isSome_iff_exists.1 (hnm (named_of_lookup hl))
      iexists (some f)
      iframe Ht' Hm Hb Ht
      isplitr
      · ipureintro; exact hok.2 i _ rfl f hfc hseen
      isplitl [Hf]
      · unfold startAt; rw [hl]; iexists f; isplitr
        · ipureintro; rfl
        unfold osFileStartO; iexact Hf
      iexists (i :: D); iexact Hr
  · -- a write in flight
    dsimp only [invRes]
    icases Hs with ⟨Ht0, Hb1, Hb2⟩
    dsimp only [pwTok]
    icases Ht0 with ⟨Ht0, %hgap⟩
    icases osCrash_take_tok_keep Q L L' D true V' t _ (hD i rfl)
      [(0, DFrac.own (1 : Qp).half, bs.take (cfLo m off)),
       (cfHi m off data.length, DFrac.own (1 : Qp).half, bs.drop (cfHi m off data.length))]
      $$ Hr Ht0 [Hb1 Hb2] with ⟨%fo, %hfo, Hf, Hr, Ht0, Hbs⟩
    · iapply BigSepL.bigSepL_cons.2; iframe Hb1
      iapply BigSepL.bigSepL_singleton.2; iexact Hb2
    icases BigSepL.bigSepL_cons.1 $$ Hbs with ⟨Hb1, Hbs⟩
    icases BigSepL.bigSepL_singleton.1 $$ Hbs with Hb2
    obtain ⟨hfc, hnm, hseen⟩ := hfo
    rcases hto with ⟨hn, hg⟩ | ⟨i', hi, hl⟩
    · iexists none
      iframe Ht' Ht
      isplitr
      · ipureintro; exact hg
      isplitr
      · unfold startAt; rw [hn]; ipureintro; rfl
      isplitl [Hr]
      · iexists _; iexact Hr
      iframe; ipureintro; exact hgap
    · cases hi
      obtain ⟨f, rfl⟩ := Option.isSome_iff_exists.1 (hnm (named_of_lookup hl))
      iexists (some f)
      iframe Ht' Ht
      isplitr
      · ipureintro; exact hok.2 i _ rfl f hfc hseen
      isplitl [Hf]
      · unfold startAt; rw [hl]; iexists f; isplitr
        · ipureintro; rfl
        unfold osFileStartO; iexact Hf
      isplitl [Hr]
      · iexists _; iexact Hr
      iframe; ipureintro; exact hgap

end crash

end Perennial
