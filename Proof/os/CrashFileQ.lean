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

/-- The change in flight of the file `x` of inode `i`, as its token records it (`pwTok` with the
whole `OsMeta`). -/
def cToks (i : Ino) : OsMeta × List (w8 × Bool) × Option (Nat × Nat × List w8) →
    List (Nat × TokInfo)
  | (m, bs, some (t, off, data)) =>
      [(t, ⟨⟨i, .write off data⟩, 1, (cfRange m bs off data.length).map Prod.fst,
        pwMeta m off data.length, (cfRange m bs off data.length).map Prod.snd⟩)]
  | _ => []

/-- Every file a crash under the premise `Q` may leave of the file `x` of inode `i` is `Good`,
given the crash's facts. -/
def FileOkQ (Q : OsState → OsState → Prop) (Good : Option OsFile → Prop) (i : Ino)
    (x : OsMeta × List (w8 × Bool) × Option (Nat × Nat × List w8)) : Prop :=
  ∀ f, FileCrashedR (fMeta x) (fRuns x) (some f) →
    CrashSeenR Q i (fMeta x) (fRuns x) (cToks i x) (some f) → Good (some f)

/-- What a crash under the premise `Q` may leave of the state `s` and the history `V` is `Good`
at `p`. -/
def CrashOkQ (Q : OsState → OsState → Prop) (Good : Option OsFile → Prop) (p : GoString)
    (R : Roots) (s : CFile) (V : Hist) : Prop :=
  TreeOk Good p R s V ∧ ∀ i x, s = some (i, x) → FileOkQ Q Good i x

/-- A write in flight starts inside the file (`pwTok`'s `off ≤ m.size`). -/
def OffOk : OsMeta × List (w8 × Bool) × Option (Nat × Nat × List w8) → Prop
  | (m, _, some (_, off, _)) => off ≤ m.size
  | _ => True

theorem fileOk_Q {Q : OsState → OsState → Prop} {Good : Option OsFile → Prop} {i : Ino}
    {x : OsMeta × List (w8 × Bool) × Option (Nat × Nat × List w8)} (hoff : OffOk x)
    (h : FileOk Good x) : FileOkQ Q Good i x := by
  intro f hc hs
  rcases x with ⟨m, bs, _ | ⟨t, off, data⟩⟩
  · exact h f hc (crashSeen_runsKept hs (fun x hx => by cases hx))
      (fun b h1 h2 => crashSeen_tailKept hs (fun x hx => by cases hx) f rfl b h1 h2) trivial
  · have hgap : off ≤ m.size := hoff
    have hrk : RunsKept (fRuns (m, bs, some (t, off, data))) (some f) := by
      refine crashSeen_runsKept hs (fun x hx => ⟨off, data, ?_, fun r hr k hk hkm => ?_⟩)
      · rw [cToks, List.mem_singleton] at hx; rw [hx]
      · simp only [fRuns, List.mem_cons, List.not_mem_nil, or_false] at hr
        have hsz : (fMeta (m, bs, some (t, off, data))).size = m.size := rfl
        rw [hsz] at hkm
        rcases hr with rfl | rfl
        · left; simp only [List.length_take] at hk; unfold cfLo at hk; dsimp only; omega
        · right; dsimp only; unfold cfHi at hkm ⊢; omega
    have htk := crashSeen_tailKept hs (fun x hx => ⟨off, data, by
      rw [cToks, List.mem_singleton] at hx; rw [hx], hgap⟩)
    refine h f hc hrk (fun b h1 h2 => .inl (htk f rfl b h1 h2)) (fun j x hx hj => ?_)
    exact .inr (.inr (crashSeen_tokKept hs List.mem_cons_self rfl rfl hgap f rfl j x.1
      (by simp [List.getElem?_map, hx]) hj))

theorem crashOk_Q {Q : OsState → OsState → Prop} {Good : Option OsFile → Prop} {p : GoString}
    {R : Roots} {s : CFile} {V : Hist} (hoff : ∀ i x, s = some (i, x) → OffOk x)
    (h : CrashOk Good p R s V) : CrashOkQ Q Good p R s V :=
  ⟨h.1, fun i x hs => fileOk_Q (hoff i x hs) (h.2 i x hs)⟩

section res
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt fsExt] [GoGlobalContext]
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
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt fsExt] [GoGlobalContext]
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
  rcases s with _ | ⟨i, m, bs, _ | ⟨t, off, data⟩⟩
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
        obtain ⟨vs, sz, rfl⟩ := crashSeen_ofDisk hseen
        iapply (osFileStartG_ofDisk (L := L') _ vs sz).1
        iapply (show osFileStartO (L := L') _ (some (OsFile.ofDisk vs sz)) ⊢
            osFileStartG (L := L') _ (OsFile.ofDisk vs sz) from BIBase.Entails.rfl) $$ Hf
      iexists (i :: D); iexact Hr
  · -- a write in flight
    dsimp only [invRes]
    icases Hs with ⟨Ht0, Hb1, Hb2⟩
    dsimp only [pwTok]
    icases Ht0 with ⟨Ht0, %hgap⟩
    icases osCrash_take_tok_keep Q L L' D true V' t _ (hD i rfl)
      (fRuns (m, bs, some (t, off, data))) $$ Hr Ht0 [Hb1 Hb2] with ⟨%fo, %hfo, Hf, Hr, Ht0, Hbs⟩
    · unfold fRuns
      iapply BigSepL.bigSepL_cons.2; iframe Hb1
      iapply BigSepL.bigSepL_singleton.2; iexact Hb2
    unfold fRuns
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
        obtain ⟨vs, sz, rfl⟩ := crashSeen_ofDisk hseen
        iapply (osFileStartG_ofDisk (L := L') _ vs sz).1
        iapply (show osFileStartO (L := L') _ (some (OsFile.ofDisk vs sz)) ⊢
            osFileStartG (L := L') _ (OsFile.ofDisk vs sz) from BIBase.Entails.rfl) $$ Hf
      isplitl [Hr]
      · iexists _; iexact Hr
      iframe; ipureintro; exact hgap

end crash

end Perennial
