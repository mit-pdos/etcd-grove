/- Lean-first (no Rocq counterpart).

# Taking the WAL's segments after a crash, writes in flight included (W6)

`walInv_crash` takes every named segment from the restart's resources at one crash
(`crashRestAt`, `GooseLang/Ext/Fs/CrashTakeFiles.lean`). A segment with a write in flight
(`segResF`, `Inv.lean`) holds the write's token and the halves of the bytes around it, not the
segment's halves:

* `crashRestAt_take_tok`: `crashRestAt_take` for a file a change in flight is on, taking its token
  (the fixed-crash form of `crashRest_take_tok_keep`, `GooseLang/Ext/Fs/CrashTok.lean`; belongs in
  `CrashTakeFiles.lean`, kept here so that `GooseLang/Ext/Fs` does not rebuild), and what the crash
  kept of the bytes the change announced past the size (`TokPast`, from the state's `tok_cand`: their
  candidates before it, then its own), which the token's `OsMeta` forgot;
* `fileCrashedR_rzMeta`, `fileCrashedR_rsPostK_rz`: a resize's crash, in flight or after a truncate
  landed (keeping the candidates it cut off), is one the layout's `OsMeta` (`rzMeta`) allows;
* `RunsCover`, `fileCrashedR_cover`: runs covering the segment's bytes as the layout holds them
  (the write's announced bytes between the halves around them, `SegFl.Ok`) give its crash as one run;
* `crashRestAt_take_seg`, `crashRest_take_segs`: every segment, idle or with a write in flight, at
  one crash: each as `FileCrashedR` of its layout's `OsMeta` and bytes, its candidates the state's.
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.Inv
public import GooseLang.Ext.Fs.CrashTakeFiles
public import LinuxFs.Proof.os.CrashResize

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Fs

/-! ## Runs covering a segment's bytes (pure) -/

/-- Every byte of `G` is the byte of one of the runs `rs` at the same offset. -/
def RunsCover (rs : List (Nat × DFrac × List ByteG)) (G : List ByteG) : Prop :=
  ∀ b (hb : b < G.length), ∃ r ∈ rs, ∃ k, ∃ hk : k < r.2.2.length, r.1 + k = b ∧ r.2.2[k] = G[b]

theorem fileCrashedR_cover {m : OsMeta} {rs : List (Nat × DFrac × List ByteG)} {G : List ByteG}
    {fo : Option OsFile} (q : DFrac) (hc : RunsCover rs G) (h : FileCrashedR m rs fo) :
    FileCrashedR m [(0, q, G)] fo := by
  intro f' hf
  obtain ⟨h1, h2, h3, h4, h5⟩ := h f' hf
  refine ⟨h1, h2, h3, ?_, h5⟩
  intro r hr k hk hks
  rw [List.mem_singleton] at hr; subst hr
  obtain ⟨r', hr', k', hk', he, hg⟩ := hc k hk
  have := h4 r' hr' k' hk' (by simp at hks; omega)
  simp only [Nat.zero_add] at hks ⊢
  rw [he, hg] at this
  exact this

theorem cands_cover {f : OsFile} {rs : List (Nat × DFrac × List ByteG)} {G : List ByteG}
    (hc : RunsCover rs G) (h : ∀ r ∈ rs, ∀ k (hk : k < r.2.2.length), f.cand (r.1 + k) = (r.2.2[k]).2) :
    ∀ b (y : ByteG), G[b]? = some y → f.cand b = y.2 := by
  intro b y hb
  obtain ⟨hbl, rfl⟩ := List.getElem?_eq_some_iff.1 hb
  obtain ⟨r, hr, k, hk, he, hg⟩ := hc b hbl
  rw [← hg, ← he]; exact h r hr k hk

theorem runsCover_one (q : DFrac) (G : List ByteG) : RunsCover [(0, q, G)] G :=
  fun b hb => ⟨_, List.mem_singleton_self _, b, hb, Nat.zero_add b, rfl⟩

/-- A write in flight's runs (its token's announced bytes, the halves around them) cover the
segment as the layout holds it. -/
theorem runsCover_fl {fl : SegFl} {g : SegG} (h : fl.Ok g) :
    RunsCover [(cfLo fl.m fl.off, DFrac.own 1, pwAnn fl.data fl.n (cfRange fl.m fl.bs fl.off fl.data.length)),
      (0, DFrac.own (1 : Qp).half, fl.bs.take (cfLo fl.m fl.off)),
      (cfHi fl.m fl.off fl.data.length, DFrac.own (1 : Qp).half,
        fl.bs.drop (cfHi fl.m fl.off fl.data.length))] g.bs := by
  obtain ⟨hin, -, hlen, -, -, hbs, -⟩ := h
  have hlo : cfLo fl.m fl.off = fl.off := by unfold cfLo; omega
  have hhi : cfHi fl.m fl.off fl.data.length = fl.off + fl.data.length := by unfold cfHi; omega
  have hA : (pwAnn fl.data fl.n (cfRange fl.m fl.bs fl.off fl.data.length)).length = fl.data.length := by
    simp only [pwAnn_length, cfRange, List.length_take, List.length_drop]; rw [hlo, hhi]; omega
  have hT : (fl.bs.take (cfLo fl.m fl.off)).length = fl.off := by
    simp only [List.length_take]; rw [hlo]; omega
  rw [hbs]
  intro b hb
  by_cases h1 : b < fl.off
  · refine ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), b, by simp at hT ⊢; omega, by simp, ?_⟩
    simp only
    rw [List.getElem_append_left (by simp only [List.length_append]; omega),
      List.getElem_append_left (by omega)]
  · by_cases h2 : b < fl.off + fl.data.length
    · refine ⟨_, List.mem_cons_self .., b - fl.off, by rw [hA]; omega, by rw [hlo]; omega, ?_⟩
      simp only
      rw [List.getElem_append_left (by simp only [List.length_append]; omega),
        List.getElem_append_right (by omega)]
      congr 1; omega
    · refine ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)),
        b - (fl.off + fl.data.length), ?_, by rw [hhi]; omega, ?_⟩
      · simp only [List.length_append, hT, hA, List.length_drop] at hb ⊢; rw [hhi]; omega
      · simp only
        rw [List.getElem_append_right (by simp only [List.length_append]; omega)]
        simp only [List.length_append, hT, hA, List.getElem_drop]

/-- A resize in flight's runs (its token's bytes cut off, the halves below them) cover the segment
as the layout holds it (I3b). -/
theorem runsCover_rz {fl : SegFl} {tr : Bool} {tg : Nat} {g : SegG} (h : fl.OkR tr tg g) :
    RunsCover [(min fl.m.size tg, DFrac.own 1, rsAnn fl.n (fl.bs.drop (min fl.m.size tg))),
      (0, DFrac.own (1 : Qp).half, fl.bs.take (min fl.m.size tg))] g.bs := by
  obtain ⟨hlen, -, -, hbs, -⟩ := h
  rw [hbs]
  intro b hb
  have hT : (fl.bs.take (min fl.m.size tg)).length = min fl.m.size tg := by
    simp only [List.length_take]; omega
  by_cases h1 : b < min fl.m.size tg
  · refine ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), b, by rw [hT]; exact h1, by simp, ?_⟩
    simp only
    rw [List.getElem_append_left (by rw [hT]; exact h1)]
  · refine ⟨_, List.mem_cons_self .., b - min fl.m.size tg, ?_, by omega, ?_⟩
    · simp only [List.length_append, hT, rsAnn_length, List.length_drop] at hb ⊢; omega
    · simp only
      rw [List.getElem_append_right (by rw [hT]; omega)]
      simp only [hT]

/-! ## The bytes a change announced past the size -/

/-- **What a crash keeps of a byte a change in flight announced past the size its first step saw**:
one of the candidates the byte had then (`OsMeta.pc`, known by the `OsMeta` before the change) or
the change's own, or, at or past the crash bound, zero. -/
def TokPast (ti : TokInfo) (fo : Option OsFile) : Prop :=
  ∀ f', fo = some f' → ∀ b c, ti.m0.size ≤ b → inRange ti.lo ti.hi b = true → ti.m0.pc b = some c →
    b < f'.size → (∃ s, (f'.cache b, s) ∈ c ++ [(ti.val b, ti.n)]) ∨ (ti.meta.lo ≤ b ∧ f'.cache b = 0)

/-- **A crash keeps the bytes a change in flight announced past the size** (`TokPast`, from
`OsCoh.tok_cand`). -/
theorem tok_crash_past {st st' : OsState} {Γb : GMap (Ino × Nat) ByteG} {Γm : GMap Ino OsMeta}
    {Γf : GMap w64 OsFd} {Γt : GMap Nat TokInfo} {t : Nat} {ti : TokInfo}
    (hcoh : OsCoh st Γb Γm Γf Γt) (hc : OsCrash st st') (hti : Γt !! t = some ti) :
    TokPast ti (st'.fs.files !! ti.ino) := by
  intro f' hf' b c hb hin hpc hbs
  have hm := hcoh.tok_meta t ti hti
  obtain ⟨f, hf, hok⟩ := hcoh.meta_some ti.ino ti.meta hm
  have hn : Named st'.fs.treeDur ti.ino := by
    apply Classical.byContradiction; intro hn
    rw [(hc.2.2.2.2.2.2.2 ti.ino).2 hn] at hf'; cases hf'
  obtain ⟨f0, f1, hf0, ⟨sz, img, -, -, hcand, rfl⟩, hf1⟩ := (hc.2.2.2.2.2.2.2 ti.ino).1 hn
  rw [hf] at hf0; cases hf0
  rw [hf'] at hf1; cases hf1
  obtain ⟨f2, hf2, hc2⟩ := hcoh.tok_cand t ti hti
  simp only [OsState.file, hf, Option.some.injEq] at hf2; subst hf2
  obtain ⟨c0, hc0, hz, htc⟩ := hc2 b hin
  have hc0c : c0 = c := by
    rcases OsMeta.pc_some hpc with h | ⟨z, hz', hzb, rfl⟩
    · exact htc c hb h
    · exact hz z hz' hzb
  subst hc0c
  simp only [OsFile.ofDisk] at hbs
  have hcache : (OsFile.ofDisk img sz).cache b = img b := by
    simp only [OsFile.ofDisk, diskByte]
    rw [if_pos (by simp only [pageIn, decide_eq_true_eq]; have := Nat.mul_div_le b 4096; omega)]
  rw [hcache]
  rcases hcand b with ⟨s, hs⟩ | ⟨hl, h0⟩
  · rw [hc0] at hs; exact .inl ⟨s, hs⟩
  · exact .inr ⟨Nat.le_trans hok.lo hl, h0⟩

/-- **A resize in flight's crash is one the layout's `OsMeta` allows** (`rzMeta`: the token's, and the
candidates of the bytes announced past the size, `TokPast`). -/
theorem fileCrashedR_rzMeta {tr : Bool} {i : Ino} {tg n : Nat} {m : OsMeta} {sv : List ByteG}
    {rs : List (Nat × DFrac × List ByteG)} {fo : Option OsFile}
    (h : FileCrashedR (TokInfo.meta ⟨i, rsKind tr tg, n, m, sv⟩) rs fo)
    (hp : TokPast ⟨i, rsKind tr tg, n, m, sv⟩ fo) :
    FileCrashedR (rzMeta tr m tg n) rs fo := by
  rw [rsKind_meta] at h
  intro f' hf'
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h f' hf'
  refine ⟨h1, h2, h3, h4, h5, fun b c hb hc hbs => ?_⟩
  change rsTail tr m tg m.size n [] !! b = some c at hc
  rw [rsTail_lookup] at hc
  split at hc
  · rename_i hin
    have hsb : m.size ≤ b := hin.2.2
    rw [if_neg (by omega)] at hc
    obtain ⟨c', hc', rfl⟩ := Option.map_eq_some_iff.1 hc
    have := hp f' hf' b c' hsb
      (by simp only [rsKind_lo, rsKind_hi, inRange, Bool.and_eq_true, decide_eq_true_eq]; omega) hc' hbs
    simp only [rsKind_val, rsKind_meta] at this
    exact this
  · exact h6 b c hb hc hbs

/-- **A crash after a truncate landed is one the layout's `OsMeta` of it in flight allows**
(`fileCrashedR_rsPostK`, with the candidates of the bytes announced past the old size, which the
landing keeps too). -/
theorem fileCrashedR_rsPostK_rz {m : OsMeta} {tg n : Nat} {xs ys : List ByteG} {q : Iris.DFrac}
    {fo : Option OsFile} (htg : tg ≤ m.size) (hxl : xs.length = m.size - tg) (hyl : ys.length = tg)
    (h : FileCrashedR (rsPostK true true m tg tg n xs) [(0, q, ys)] fo) :
    FileCrashedR (rzMeta true m tg n) [(0, q, ys ++ rsAnn n xs)] fo := by
  have h' := fileCrashedR_rsPostK htg hxl hyl h
  intro f' hf'
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h' f' hf'
  obtain ⟨-, -, -, -, -, k6⟩ := h f' hf'
  refine ⟨h1, h2, h3, h4, h5, fun b c hb hc hbs => ?_⟩
  change rsTail true m tg m.size n [] !! b = some c at hc
  rw [rsTail_lookup] at hc
  split at hc
  · rename_i hin
    have hsb : m.size ≤ b := hin.2.2
    rw [if_neg (by omega)] at hc
    have htc := rsPostK_true_tc_past (tr := true) (m := m) (tg := tg) (sz' := tg) (n := n) (xs := xs)
      (by omega) hsb hin.2.1
    rw [hc] at htc
    exact k6 b c (by show tg ≤ b; omega) htc hbs
  · exact h6 b c hb hc hbs

/-! ## Taking a token at a fixed crash -/

section take
variable {GF : BundledGFunctors}

/-- **Taking the file a change in flight is on, at a fixed crash** (`crashRestAt_take` with the
change's token in place of the file's `OsMeta`). -/
theorem crashRestAt_take_tok (hL : OsGS GF) (Q : OsState → OsState → Prop) (hL' : OsGS GF)
    (D : List Ino) (tt : Bool) (V' : Hist) (st st' : OsState) (t : Nat) (ti : TokInfo)
    (hi : ti.ino ∉ D) (rs : List (Nat × DFrac × List ByteG)) :
    ⊢ crashRestAt Q hL hL' D tt V' st st' -∗ gElem hL hL.γt t (DFrac.own 1) ti -∗
      ([∗list] r ∈ rs, bytesG hL ti.ino r.1 r.2.1 r.2.2) -∗
      ⌜FileCrashAt st st' V' ti.ino ti.meta ((ti.lo, DFrac.own 1, ti.saved) :: rs) ∧
        TokPast ti (st'.fs.files !! ti.ino)⌝ ∗
        fileStartO hL' ti.ino (st'.fs.files !! ti.ino) ∗
        crashRestAt Q hL hL' (ti.ino :: D) tt V' st st' ∗
        gElem hL hL.γt t (DFrac.own 1) ti ∗ ([∗list] r ∈ rs, bytesG hL ti.ino r.1 r.2.1 r.2.2) := by
  unfold crashRestAt
  iintro ⟨%Γb, %Γm, %F, %Γf, %Γt, %V, %hrel, Hab, Ham, Hfs, HAt, Htok, HAd, Htl⟩ Ht Hbs
  obtain ⟨hwf, hcoh, hcr, hQ, hF, hroots, htc, hnamed, htd⟩ := hrel
  icases gAuth_lookup hL _ _ _ _ _ $$ HAt Ht with %hti
  unfold tokRes
  icases (BigSepM.bigSepM_delete (Φ := fun _ (ti : TokInfo) => iprop(
      gElem hL hL.γm ti.ino (DFrac.own 1) ti.meta ∗
      bytesG hL ti.ino ti.lo (DFrac.own 1) ti.saved)) hti).1
    $$ Htok with ⟨⟨Hm, Hb⟩, Htok⟩
  icases gAuth_lookup hL _ _ _ _ _ $$ Ham Hm with %hmo
  icases bytesG_lookup_runs hL ti.ino Γb ((ti.lo, DFrac.own 1, ti.saved) :: rs) $$ Hab [Hb Hbs]
    with %hxs
  · iapply BigSepL.bigSepL_cons.2; iframe
  icases files_take hL' F ti.ino $$ Hfs with ⟨Hf, Hfs⟩
  have hFi := hF ti.ino hi
  have hseen : CrashSeenR Q ti.ino ti.meta ((ti.lo, DFrac.own 1, ti.saved) :: rs) [(t, ti)]
      (F !! ti.ino) := by
    refine ⟨st, st', Γb, Γm, Γf, Γt, hwf, hcoh, hcr, hQ, hFi.symm, hmo, hxs,
      fun t' ti' ht' hp => ?_, fun x hx => ?_⟩
    · obtain ⟨rfl, rfl⟩ := tok_one hwf hcoh hti ht' hp
      exact List.mem_singleton.2 rfl
    · rw [List.mem_singleton] at hx; subst hx; exact hti
  have hpast := tok_crash_past hcoh hcr hti
  rw [hFi] at hseen
  rw [hFi]
  iframe Hf Ht Hbs
  isplitr
  · ipureintro
    refine ⟨⟨crashSeen_crashed hseen, fun hn => hnamed _ hn, ?_⟩, hpast⟩
    obtain ⟨f, hf, -⟩ := hcoh.meta_some ti.ino ti.meta hmo
    refine ⟨f, hf, fun hcut r hr k hk => ?_⟩
    obtain ⟨f1, hf1, -, -, -, hrel⟩ := hcoh.bytes ti.ino _ _ (hxs r hr k hk)
    simp only [OsState.file, hf, Option.some.injEq] at hf1
    subst hf1
    have hc : cutOf Γm ti.ino = none := by simp [cutOf, hmo, hcut]
    rw [hc] at hrel
    exact hrel
  iexists Γb, Γm, GMap.delete ti.ino F, Γf, Γt, V
  iframe Hab Ham Hfs HAt HAd Htl
  isplitr
  · ipureintro
    exact ⟨hwf, hcoh, hcr, hQ, crashRest_files_delete hF, hroots, htc, hnamed, htd⟩
  iapply (BigSepM.bigSepM_delete (Φ := fun _ (ti : TokInfo) => iprop(
      gElem hL hL.γm ti.ino (DFrac.own 1) ti.meta ∗
      bytesG hL ti.ino ti.lo (DFrac.own 1) ti.saved)) hti).2
  iframe

end take

/-! ## Taking the segments -/

section segs
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF]

/-- What a crash did to the segment `g` (the layout's), from the state `st` to `st'`. -/
def SegCrashAt (st st' : OsState) (V' : Hist) (g : SegG) : Prop :=
  FileCrashedR g.om [(0, DFrac.own (1 : Qp).half, g.bs)] (st'.fs.files !! g.ino) ∧
    (Named V'.now g.ino → (st'.fs.files !! g.ino).isSome) ∧
    ∃ f, st.fs.files !! g.ino = some f ∧ ∀ b (y : ByteG), g.bs[b]? = some y → f.cand b = y.2

/-- **Taking a segment, idle or with a write or a resize in flight, at a fixed crash.** -/
theorem crashRestAt_take_seg (Q : OsState → OsState → Prop) (L L' : GooseLocalGS GF)
    (D : List Ino) (tt : Bool) (V' : Hist) (st st' : OsState) (F : GMap Ino SegFl) (g : SegG)
    (hi : g.ino ∉ D) (hcut : g.om.cut = none) :
    ⊢ crashRestAt Q (gooseOsGS (L := L)) (gooseOsGS (L := L')) D tt V' st st' -∗
      segResF (L := L) F g -∗
      ⌜SegCrashAt st st' V' g⌝ ∗ osFileStartO (L := L') g.ino (st'.fs.files !! g.ino) ∗
        crashRestAt Q (gooseOsGS (L := L)) (gooseOsGS (L := L')) (g.ino :: D) tt V' st st' ∗
        segResF (L := L) F g := by
  iintro Hr Hs
  unfold segResF
  cases hF : F !! g.ino with
  | none =>
    simp only []
    unfold segRes osMeta osBytes
    icases Hs with ⟨Hm, Hb⟩
    icases crashRestAt_take (gooseOsGS (L := L)) Q (gooseOsGS (L := L')) D tt V' st st' g.ino hi
      (DFrac.own (1 : Qp).half) g.om [(0, DFrac.own (1 : Qp).half, g.bs)] $$ Hr Hm [Hb]
      with ⟨%hfc, Hf, Hr, Hm, Hb⟩
    · iapply BigSepL.bigSepL_singleton.2; iexact Hb
    icases BigSepL.bigSepL_singleton.1 $$ Hb with Hb
    iframe Hr Hm Hb
    isplitr
    · ipureintro
      obtain ⟨h1, h2, f, hf, h3⟩ := hfc
      exact ⟨h1, h2, f, hf, cands_cover (runsCover_one _ _) (h3 hcut)⟩
    iapply (fileStartO_eq (L := L') g.ino _).1 $$ Hf
  | some fl =>
    simp only []
    cases hrz : fl.rz with
    | none =>
      simp only []
      icases Hs with ⟨Ht, Hb1, Hb2, %hok⟩
      unfold pwTok osTok osBytes
      icases Ht with ⟨Ht, %hgap⟩
      have hcut0 : fl.m.cut = none := hok.2.2.2.1
      icases crashRestAt_take_tok (gooseOsGS (L := L)) Q (gooseOsGS (L := L')) D tt V' st st' fl.t
        ⟨g.ino, .write fl.off fl.data, fl.n, fl.m, pwAnn fl.data fl.n (cfRange fl.m fl.bs fl.off fl.data.length)⟩
        hi [(0, DFrac.own (1 : Qp).half, fl.bs.take (cfLo fl.m fl.off)),
          (cfHi fl.m fl.off fl.data.length, DFrac.own (1 : Qp).half, fl.bs.drop (cfHi fl.m fl.off fl.data.length))]
        $$ Hr Ht [Hb1 Hb2] with ⟨%hfc, Hf, Hr, Ht, Hbs⟩
      · iapply BigSepL.bigSepL_cons.2; iframe Hb1
        iapply BigSepL.bigSepL_singleton.2; iexact Hb2
      icases BigSepL.bigSepL_cons.1 $$ Hbs with ⟨Hb1, Hbs⟩
      icases BigSepL.bigSepL_singleton.1 $$ Hbs with Hb2
      obtain ⟨⟨h1, h2, f, hf, h3⟩, -⟩ := hfc
      have hcov := runsCover_fl hok
      have hmeta : g.om = cfMeta fl.m fl.off fl.data.length := hok.2.2.2.2.1
      iframe Hr Hb1 Hb2
      isplitr
      · ipureintro
        refine ⟨?_, h2, f, hf, cands_cover hcov (h3 ?_)⟩
        · rw [hmeta]; exact fileCrashedR_cover _ hcov h1
        · show (cfMeta fl.m fl.off fl.data.length).cut = none
          simp [cfMeta, OsMeta.announce, hcut0]
      isplitl [Hf]
      · iapply (fileStartO_eq (L := L') g.ino _).1 $$ Hf
      iframe Ht
      ipureintro; exact ⟨hgap, hok⟩
    | some p =>
      obtain ⟨tr, tg⟩ := p
      simp only []
      icases Hs with ⟨Ht, Hb1, %hok⟩
      unfold rsTok osTok osBytes
      icases Ht with ⟨Ht, %hxl⟩
      have hcut0 : fl.m.cut = none := hok.2.1
      icases crashRestAt_take_tok (gooseOsGS (L := L)) Q (gooseOsGS (L := L')) D tt V' st st' fl.t
        ⟨g.ino, rsKind tr tg, fl.n, fl.m, rsAnn fl.n (fl.bs.drop (min fl.m.size tg))⟩
        hi [(0, DFrac.own (1 : Qp).half, fl.bs.take (min fl.m.size tg))]
        $$ Hr Ht [Hb1] with ⟨%hfc, Hf, Hr, Ht, Hbs⟩
      · iapply BigSepL.bigSepL_singleton.2; iexact Hb1
      icases BigSepL.bigSepL_singleton.1 $$ Hbs with Hb1
      obtain ⟨⟨h1, h2, f, hf, h3⟩, hpast⟩ := hfc
      simp only [rsKind_lo] at h1 h3
      have hcov := runsCover_rz hok
      iframe Hr Hb1
      isplitr
      · ipureintro
        refine ⟨?_, h2, f, hf, cands_cover hcov (h3 ?_)⟩
        · rw [hok.2.2.1]; exact fileCrashedR_rzMeta (fileCrashedR_cover _ hcov h1) hpast
        · rw [rsKind_meta]; simp [hcut0]
      isplitl [Hf]
      · iapply (fileStartO_eq (L := L') g.ino _).1 $$ Hf
      iframe Ht
      ipureintro; exact ⟨hxl, hok⟩

/-- **Taking the segments `gs`, idle or with writes in flight, at a fixed crash.** -/
theorem crashRestAt_take_segs (Q : OsState → OsState → Prop) (L L' : GooseLocalGS GF)
    (tt : Bool) (V' : Hist) (st st' : OsState) (F : GMap Ino SegFl) :
    ∀ (gs : List SegG) (D : List Ino), (∀ g ∈ gs, g.ino ∉ D) → (gs.map (·.ino)).Nodup →
    (∀ g ∈ gs, g.om.cut = none) →
    ⊢ crashRestAt Q (gooseOsGS (L := L)) (gooseOsGS (L := L')) D tt V' st st' -∗
      ([∗list] g ∈ gs, segResF (L := L) F g) -∗
      ⌜∀ g ∈ gs, SegCrashAt st st' V' g⌝ ∗
        ([∗list] i ∈ gs.map (·.ino), osFileStartO (L := L') i (st'.fs.files !! i)) ∗
        crashRestAt Q (gooseOsGS (L := L)) (gooseOsGS (L := L')) (gs.map (·.ino) ++ D) tt V' st st' ∗
        ([∗list] g ∈ gs, segResF (L := L) F g)
  | [], D, _, _, _ => by
    iintro Hr Hx
    isplitr
    · ipureintro; intro x hx; cases hx
    simp only [List.map_nil, List.nil_append]
    iframe Hr Hx
    iapply BigSepL.bigSepL_nil.2; iempintro
  | g :: gs, D, hD, hnd, hcut => by
    have hg : g.ino ∉ D := hD g (List.mem_cons_self ..)
    have hnd' := List.nodup_cons.1 (show (g.ino :: gs.map (·.ino)).Nodup from hnd)
    have hD' : ∀ y ∈ gs, y.ino ∉ g.ino :: D := by
      intro y hy hm
      rcases List.mem_cons.1 hm with h | h
      · exact hnd'.1 (h ▸ List.mem_map_of_mem hy)
      · exact hD y (List.mem_cons_of_mem _ hy) h
    iintro Hr Hxs
    icases BigSepL.bigSepL_cons.1 $$ Hxs with ⟨Hx, Hxs⟩
    icases crashRestAt_take_seg Q L L' D tt V' st st' F g hg (hcut g (List.mem_cons_self ..))
      $$ Hr Hx with ⟨%h1, Hf, Hr, Hx⟩
    icases crashRestAt_take_segs Q L L' tt V' st st' F gs (g.ino :: D) hD' hnd'.2
      (fun y hy => hcut y (List.mem_cons_of_mem _ hy)) $$ Hr Hxs with ⟨%h2, Hfs, Hr, Hxs⟩
    isplitr
    · ipureintro
      intro y hy
      rcases List.mem_cons.1 hy with rfl | hy
      · exact h1
      · exact h2 y hy
    isplitl [Hf Hfs]
    · simp only [List.map_cons]
      iapply BigSepL.bigSepL_cons.2; iframe
    isplitl [Hr]
    · iapply crashRestAt_mono (gooseOsGS (L := L)) Q (gooseOsGS (L := L')) _ _ tt V' st st' _ $$ Hr
      intro i hi
      simp only [List.mem_append, List.mem_map, List.mem_cons, List.map_cons] at hi ⊢
      rcases hi with h | h | h
      · exact Or.inl (Or.inr h)
      · exact Or.inl (Or.inl h)
      · exact Or.inr h
    iapply BigSepL.bigSepL_cons.2
    iframe

/-- **The crashed state's segments, all at once, writes in flight included** (`crashRest` with
one crashed state for all of them). -/
theorem crashRest_take_segs (Q : OsState → OsState → Prop) (L L' : GooseLocalGS GF)
    (D : List Ino) (tt : Bool) (V' : Hist) (F : GMap Ino SegFl) (gs : List SegG)
    (hD : ∀ g ∈ gs, g.ino ∉ D) (hnd : (gs.map (·.ino)).Nodup) (hcut : ∀ g ∈ gs, g.om.cut = none) :
    ⊢ crashRest Q (gooseOsGS (L := L)) (gooseOsGS (L := L')) D tt V' -∗
      ([∗list] g ∈ gs, segResF (L := L) F g) -∗
      ∃ (st st' : OsState), ⌜Q st st' ∧ st'.fs.treeDur = V'.now ∧
          ∀ g ∈ gs, SegCrashAt st st' V' g⌝ ∗
        ([∗list] i ∈ gs.map (·.ino), osFileStartO (L := L') i (st'.fs.files !! i)) ∗
        crashRest Q (gooseOsGS (L := L)) (gooseOsGS (L := L')) (gs.map (·.ino) ++ D) tt V' ∗
        ([∗list] g ∈ gs, segResF (L := L) F g) := by
  iintro Hr Hs
  icases (crashRest_at (gooseOsGS (L := L)) Q (gooseOsGS (L := L')) D tt V').1 $$ Hr
    with ⟨%st, %st', Hr⟩
  icases crashRestAt_facts (gooseOsGS (L := L)) Q (gooseOsGS (L := L')) D tt V' st st' $$ Hr
    with ⟨%hf, Hr⟩
  icases crashRestAt_take_segs Q L L' tt V' st st' F gs D hD hnd hcut $$ Hr Hs
    with ⟨%h, Hfs, Hr, Hs⟩
  iexists st, st'
  iframe Hfs Hs
  isplitr
  · ipureintro; exact ⟨hf.1, hf.2, h⟩
  iapply (crashRest_at (gooseOsGS (L := L)) Q (gooseOsGS (L := L')) _ tt V').2
  iexists st, st'; iexact Hr

end segs

end WalFs
end EtcdGrove
end Perennial

end
