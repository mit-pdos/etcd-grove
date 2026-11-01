/-
Crash-aware specs of `os` (this repository's, project `bboltfs`): the shared definitions.

A crash proof takes the old generation's files after a crash from what an invariant holds
(`osCrash_take`, `CrashTok.lean`'s `osCrashT_take_runs`), so a file's ghost resources (`osMeta`,
`osBytes`) must be in an invariant at every step, including the steps inside an `os` call. The
specs of `Spec/os/*.lean` are Hoare triples that take the resources whole from the caller; the
crash-aware ones (`Spec/os/Crash.lean`) instead keep the file in an invariant `cfInv N p γ Good`
and open it around each of the extension's steps:

* The file's state is `CFile`: absent (`none`), idle (`some (m, bs, none)`: the `OsMeta` `m` and all
  the bytes `bs`), or with a `pwrite` in flight (`some (m, bs, some (t, off, data))`: the token `t`
  holds `m` and the bytes it changes).
* The invariant holds a ghost variable `γ` naming the state, half of the resources (all of what a
  change in flight holds, its token), and `CrashOk Good s`: every file a crash may leave of the
  state is `Good`. The caller holds the other halves (`cfOwn`), so it knows the state exactly and
  can read the bytes with the existing Hoare specs (`File.ReadAt.specRacy`, which takes any
  fraction of the bytes and no `OsMeta`).
* A crash-aware spec moves the state, and asks the caller to show `CrashOk Good` of the states
  the call passes through: for a write, of one state in flight (`cfWriting`), of which every
  later state of the call, retries included, is a narrowing (`fileCrashedR_mono`).
* After a crash, `cfInv_crash` takes the file from the invariant's half: a `Good` file of the new
  generation.

`Good` is a predicate of what a crash leaves, so the specs are the same for any crash invariant
of a single file; mappings are not covered (`CfWf` asks for none).
-/
module

public import Proof.os.Base
public import GooseLang.Ext.OsFs.CrashTok

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

/-! ## The extension's operations are atomic -/

section atomic
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt osFsExt] [GoGlobalContext]

/-- Every step of an operation of the extension ends in a value. -/
theorem osStep_val {o : String} {v : val} {h : GMap Loc (NonAtomic val)} {st : OsState}
    {e' : Expr} {h' : GMap Loc (NonAtomic val)} {st' : OsState}
    (hs : OsStep o v h st () e' h' st' ()) : (toVal e').isSome := by
  obtain ⟨hs, -, -⟩ := hs
  unfold IsOsStep at hs
  split at hs
  · obtain ⟨_, _, -, -, -, hs⟩ := hs
    rcases hs with ⟨_, _, -, -, -, -, rfl⟩ | ⟨_, -, rfl, -⟩ <;> rfl
  · obtain ⟨_, _, _, _, _, -, -, -, -, -, -, hs⟩ := hs
    rcases hs with rfl | ⟨_, _, -, -, rfl⟩ <;> rfl
  · obtain ⟨_, _, _, _, _, -, -, -, -, -, rfl⟩ := hs; rfl
  · obtain ⟨_, _, _, _, _, _, _, -, -, -, -, -, -, rfl⟩ := hs; rfl
  · obtain ⟨_, _, _, -, -, -, -, hs⟩ := hs
    rcases hs with rfl | ⟨_, -, rfl⟩ <;> rfl
  · obtain ⟨_, _, _, _, -, -, -, -, -, -, -, rfl⟩ := hs; rfl
  · obtain ⟨_, _, _, _, -, -, -, hs⟩ := hs
    rcases hs with ⟨-, rfl⟩ | ⟨_, -, rfl, -⟩ <;> rfl
  · obtain ⟨_, _, _, -, -, -, hs⟩ := hs
    rcases hs with ⟨-, rfl⟩ | ⟨_, -, -, rfl, -⟩ <;> rfl
  · obtain ⟨_, _, _, _, -, -, -, rfl⟩ := hs; rfl
  · obtain ⟨_, _, _, -, -, -, rfl⟩ := hs; rfl
  · obtain ⟨_, _, _, _, _, _, -, -, -, -, -, -, -, -, hs⟩ := hs
    rcases hs with ⟨_, -, -, -, -, rfl⟩ | ⟨_, -, -, rfl⟩ <;> rfl
  · obtain ⟨_, _, _, _, -, -, -, -, hs⟩ := hs
    rcases hs with ⟨-, rfl⟩ | ⟨_, -, rfl, -⟩ <;> rfl
  · exact hs.elim

/-- An operation of the extension is atomic: it takes one step, to a value. -/
instance osOp_atomic (a : Language.Atomicity) (o : String) (v : val) :
    Language.Atomic a (ExternalOp osFsExt.name o (Val v)) :=
  goose_atomic a (fun _ _ e' _ _ hb => by
      cases hb with
      | ExternalOpS _ _ _ _ _ _ hst =>
        obtain ⟨_, _, _, hst', rfl⟩ := (extStep_named _ _ _ _ _).1 hst
        exact osStep_val ((HasExt.step_iff ..).1 hst'))
    (by intro Ki e' h; cases Ki <;> simp only [fillItem] at h <;> cases h <;> rfl)

end atomic

/-! ## The file's state and what a crash leaves of it -/

/-- A file as the crash-aware specs track it: absent (`none`); its `OsMeta` and all its bytes
(`some (m, bs, none)`); or with a `pwrite` of `data` at `off` in flight, whose token `t` holds
`m` and the bytes it changes (`some (m, bs, some (t, off, data))`, `bs` the bytes before it). -/
abbrev CFile := Option (OsMeta × List (w8 × Bool) × Option (Nat × Nat × List w8))

/-- The first byte a write at `off` takes of a file of size `m.size`. -/
def cfLo (m : OsMeta) (off : Nat) : Nat := min off m.size

/-- The end of the bytes a write of `n` bytes at `off` takes of a file of size `m.size`. -/
def cfHi (m : OsMeta) (off n : Nat) : Nat := min (off + n) m.size

/-- The bytes such a write takes. -/
def cfRange (m : OsMeta) (bs : List (w8 × Bool)) (off n : Nat) : List (w8 × Bool) :=
  (bs.drop (cfLo m off)).take (cfHi m off n - cfLo m off)

/-- What the old generation knows of the file for a crash: its `OsMeta` (the token's, with the
size bound of the write, while a write is in flight)... -/
def cMeta : CFile → Option OsMeta
  | none => none
  | some (m, _, none) => some m
  | some (m, _, some (_, off, data)) => some (pwMeta m off data.length)

/-- ... and the runs of bytes it holds. -/
def cRuns : CFile → List (Nat × DFrac × List (w8 × Bool))
  | none => []
  | some (_, bs, none) => [(0, DFrac.own (1 : Qp).half, bs)]
  | some (m, bs, some (_, off, data)) =>
      [(0, DFrac.own (1 : Qp).half, bs.take (cfLo m off)),
       (cfHi m off data.length, DFrac.own (1 : Qp).half, bs.drop (cfHi m off data.length))]

/-- Every file a crash may leave of the state `s` is `Good`. -/
def CrashOk (Good : Option OsFile → Prop) (s : CFile) : Prop :=
  ∀ fo, FileCrashedR (cMeta s) (cRuns s) fo → Good fo

/-- The state of a write of `data` at `off` in flight, from the file `m`, `bs` (the token's
number does not matter to a crash). -/
abbrev cfWriting (m : OsMeta) (bs : List (w8 × Bool)) (off : Nat) (data : List w8) : CFile :=
  some (m, bs, some (0, off, data))

/-- What the specs keep of a state: all of the file's bytes, and no mapping. -/
def CfWf : CFile → Prop
  | none => True
  | some (m, bs, _) => bs.length = m.size ∧ m.maps = ∅

/-- A crash view is narrower than another: a crash may leave fewer files of it. -/
theorem fileCrashedR_mono {m0 m1 : OsMeta} {rs0 rs1 : List (Nat × DFrac × List (w8 × Bool))}
    {fo : Option OsFile} (hlo : m0.lo ≤ m1.lo) (hhi : m1.hi ≤ m0.hi)
    (hnm : m1.named = false → m0.named = false)
    (hcov : ∀ r ∈ rs0, ∀ k x, r.2.2[k]? = some x → x.2 = true →
      ∃ r' ∈ rs1, ∃ k', r'.2.2[k']? = some x ∧ r'.1 + k' = r.1 + k)
    (h : FileCrashedR (some m1) rs1 fo) : FileCrashedR (some m0) rs0 fo := by
  rcases h with ⟨h1, h2⟩ | ⟨img, h1, h2, h3, h4⟩
  · exact Or.inl ⟨h1, hnm h2⟩
  · refine Or.inr ⟨img, h1, by omega, by omega, fun r hr k x hk hc => ?_⟩
    obtain ⟨r', hr', k', hk', he⟩ := hcov r hr k x hk hc
    rw [← he]; exact h4 r' hr' k' x hk' hc

/-! ## The invariant -/

section res
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt osFsExt] [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]

/-- What the invariant holds of the state: half of the `OsMeta` and of the bytes, or, while a
write is in flight, its token and half of the bytes around it. -/
def invRes (p : GoString) : CFile → IProp GF
  | none => osMeta (L := L) p (DFrac.own (1 : Qp).half) none
  | some (m, bs, none) => iprop(osMeta (L := L) p (DFrac.own (1 : Qp).half) (some m) ∗
      osBytes (L := L) p 0 (DFrac.own (1 : Qp).half) bs)
  | some (m, bs, some (t, off, data)) => iprop(
      pwTok (L := L) t p off data 1 m (cfRange m bs off data.length) ∗
      osBytes (L := L) p 0 (DFrac.own (1 : Qp).half) (bs.take (cfLo m off)) ∗
      osBytes (L := L) p (cfHi m off data.length) (DFrac.own (1 : Qp).half)
        (bs.drop (cfHi m off data.length)))

/-- What the caller holds of the state: the other halves. -/
def thrRes (p : GoString) : CFile → IProp GF
  | none => osMeta (L := L) p (DFrac.own (1 : Qp).half) none
  | some (m, bs, none) => iprop(osMeta (L := L) p (DFrac.own (1 : Qp).half) (some m) ∗
      osBytes (L := L) p 0 (DFrac.own (1 : Qp).half) bs)
  | some (m, bs, some (_, off, data)) => iprop(
      osBytes (L := L) p 0 (DFrac.own (1 : Qp).half) (bs.take (cfLo m off)) ∗
      osBytes (L := L) p (cfHi m off data.length) (DFrac.own (1 : Qp).half)
        (bs.drop (cfHi m off data.length)))

/-- The invariant of the file at `p`: its state `s` (named by `γ`), the invariant's half of it,
and every file a crash may leave of it is `Good`. -/
def cfInv (N : Namespace) (p : GoString) (γ : GName) (Good : Option OsFile → Prop) : IProp GF :=
  inv N iprop(∃ s : CFile, ghostVar γ (1 : Qp).half s ∗ invRes (L := L) p s ∗ ⌜CrashOk Good s⌝)

instance cfInv_persistent (N : Namespace) (p : GoString) (γ : GName) (Good : Option OsFile → Prop) :
    Persistent (cfInv (L := L) N p γ Good) := by unfold cfInv; infer_instance

/-- The caller's part of the file at `p` in the state `s`. -/
def cfOwn (p : GoString) (γ : GName) (s : CFile) : IProp GF :=
  iprop(ghostVar γ (1 : Qp).half s ∗ thrRes (L := L) p s ∗ ⌜CfWf s⌝)

theorem osMeta_halves (p : GoString) (mo : Option OsMeta) :
    osMeta (L := L) p (DFrac.own 1) mo ⊣⊢
      osMeta (L := L) p (DFrac.own (1 : Qp).half) mo ∗ osMeta (L := L) p (DFrac.own (1 : Qp).half) mo := by
  have h := gElem_split (gooseOsGS (L := L)) (gooseOsGS (L := L)).γm p (1 : Qp).half (1 : Qp).half mo
  rw [Qp.half_add_half] at h
  exact h

theorem osBytes_halves (p : GoString) (off : Nat) (xs : List (w8 × Bool)) :
    osBytes (L := L) p off (DFrac.own 1) xs ⊣⊢
      osBytes (L := L) p off (DFrac.own (1 : Qp).half) xs ∗
        osBytes (L := L) p off (DFrac.own (1 : Qp).half) xs := by
  unfold osBytes bytesG
  refine BiEntails.trans ?_ BigSepL.bigSepL_sep_eqv
  constructor
  · apply BigSepL.bigSepL_mono_of_forall; intro k x
    have h := gElem_split (gooseOsGS (L := L)) (gooseOsGS (L := L)).γb (p, off + k)
      (1 : Qp).half (1 : Qp).half x
    rw [Qp.half_add_half] at h
    exact h.1
  · apply BigSepL.bigSepL_mono_of_forall; intro k x
    have h := gElem_split (gooseOsGS (L := L)) (gooseOsGS (L := L)).γb (p, off + k)
      (1 : Qp).half (1 : Qp).half x
    rw [Qp.half_add_half] at h
    exact h.2

/-- The file as a generation starts with it (`osFileStart`), as a state. -/
def startState : Option OsFile → CFile
  | none => none
  | some f => some (initMeta f, f.cur.map (·, true), none)

theorem startState_wf (fo : Option OsFile) : CfWf (startState fo) := by
  cases fo with
  | none => trivial
  | some f => exact ⟨by simp [initMeta], rfl⟩

/-- A file a generation starts with, in an invariant, if a crash of it is `Good`. -/
theorem cfInv_alloc (N : Namespace) (p : GoString) (Good : Option OsFile → Prop)
    (fo : Option OsFile) (hok : CrashOk Good (startState fo)) :
    ⊢ osFileStart (L := L) p fo ={⊤}=∗ ∃ γ, cfInv (L := L) N p γ Good ∗
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
      ⌜CrashOk Good s⌝)) $$ [Hv1 Hi] with #Hinv
  · inext; iexists (startState fo); iframe; ipureintro; exact hok
  imodintro
  iexists γ
  unfold cfInv cfOwn
  iframe Hinv Hv2 Ht
  ipureintro; exact startState_wf fo

end res

/-! ## After a crash -/

section crash
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt osFsExt] [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF]

/-- **The file after a crash**, from the invariant's half of the old generation's state `s`: the
new generation's file, which is `Good` if every crash of `s` is. -/
theorem cfInv_crash (L L' : GooseLocalGS GF) (D : List GoString) (p : GoString) (hp : p ∉ D)
    (Good : Option OsFile → Prop) (s : CFile) (hok : CrashOk Good s) :
    ⊢ crashRestT (gooseOsGS (L := L)) (gooseOsGS (L := L')) D -∗ invRes (L := L) p s ==∗
      ∃ fo, ⌜Good fo⌝ ∗ osFileStart (L := L') p fo ∗
        crashRestT (gooseOsGS (L := L)) (gooseOsGS (L := L')) (p :: D) := by
  iintro Hr Hs
  rcases s with _ | ⟨m, bs, _ | ⟨t, off, data⟩⟩
  · unfold invRes
    icases osCrashT_take_runs L L' D p hp _ none [] $$ Hr Hs [] with ⟨%fo, %h, Hf, Hr⟩
    · iapply BigSepL.bigSepL_nil.2; iempintro
    imodintro; iexists fo; iframe; ipureintro; exact hok fo h
  · unfold invRes
    icases Hs with ⟨Hm, Hb⟩
    icases osCrashT_take_runs L L' D p hp _ (some m) [(0, DFrac.own (1 : Qp).half, bs)]
      $$ Hr Hm [Hb] with ⟨%fo, %h, Hf, Hr⟩
    · iapply BigSepL.bigSepL_singleton.2; iexact Hb
    imodintro; iexists fo; iframe; ipureintro; exact hok fo h
  · unfold invRes
    icases Hs with ⟨Ht, Hb1, Hb2⟩
    unfold pwTok
    imod osCrashT_tok L L' D t _ $$ Hr Ht with ⟨Hm, Hr⟩
    icases osCrashT_take_runs L L' D p hp _ (some (pwMeta m off data.length))
      (cRuns (some (m, bs, some (t, off, data)))) $$ Hr Hm [Hb1 Hb2] with ⟨%fo, %h, Hf, Hr⟩
    · unfold cRuns
      iapply BigSepL.bigSepL_cons.2; iframe Hb1
      iapply BigSepL.bigSepL_singleton.2; iexact Hb2
    imodintro; iexists fo; iframe; ipureintro; exact hok fo h

/-- `cfInv_crash`, giving back the invariant's half, so that the invariant can be closed again. -/
theorem cfInv_crash_keep (L L' : GooseLocalGS GF) (D : List GoString) (p : GoString) (hp : p ∉ D)
    (Good : Option OsFile → Prop) (s : CFile) (hok : CrashOk Good s) :
    ⊢ crashRestT (gooseOsGS (L := L)) (gooseOsGS (L := L')) D -∗ invRes (L := L) p s -∗
      ∃ fo, ⌜Good fo⌝ ∗ osFileStart (L := L') p fo ∗
        crashRestT (gooseOsGS (L := L)) (gooseOsGS (L := L')) (p :: D) ∗ invRes (L := L) p s := by
  iintro Hr Hs
  rcases s with _ | ⟨m, bs, _ | ⟨t, off, data⟩⟩
  · dsimp only [invRes]
    icases osCrashT_take_runs_keep L L' D p hp _ none [] $$ Hr Hs [] with ⟨%fo, %h, Hf, Hr, Hs, -⟩
    · iapply BigSepL.bigSepL_nil.2; iempintro
    iexists fo; iframe; ipureintro; exact hok fo h
  · dsimp only [invRes]
    icases Hs with ⟨Hm, Hb⟩
    icases osCrashT_take_runs_keep L L' D p hp _ (some m) [(0, DFrac.own (1 : Qp).half, bs)]
      $$ Hr Hm [Hb] with ⟨%fo, %h, Hf, Hr, Hm, Hb⟩
    · iapply BigSepL.bigSepL_singleton.2; iexact Hb
    icases BigSepL.bigSepL_singleton.1 $$ Hb with Hb
    iexists fo; iframe; ipureintro; exact hok fo h
  · dsimp only [invRes]
    icases Hs with ⟨Ht, Hb1, Hb2⟩
    dsimp only [pwTok]
    icases osCrashT_take_tok_keep L L' D t _ hp (cRuns (some (m, bs, some (t, off, data))))
      $$ Hr Ht [Hb1 Hb2] with ⟨%fo, %h, Hf, Hr, Ht, Hbs⟩
    · unfold cRuns
      iapply BigSepL.bigSepL_cons.2; iframe Hb1
      iapply BigSepL.bigSepL_singleton.2; iexact Hb2
    unfold cRuns
    icases BigSepL.bigSepL_cons.1 $$ Hbs with ⟨Hb1, Hbs⟩
    icases BigSepL.bigSepL_singleton.1 $$ Hbs with Hb2
    iexists fo; iframe; ipureintro; exact hok fo h

end crash

end Perennial
