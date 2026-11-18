/-
The shared mode of the tree: the mode switch (`wp_osShare'`) and `CallBegin` in the shared mode
(`wp_osCallBeginS'`), with the facts they rest on (`notes/wal-fsext-i2-design.md`, §2.3): the log as
a map (`logMap_lookup`), the claims a switch allocates (`claimsInit`), the shared coherence of a
sequential log (`cohS_switch`). `TreeShared.lean` states the API and takes its proofs from here.
Untrusted.
-/
module

public import GooseLang.Ext.Fs.TreeSharedRes

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace Perennial
namespace Fs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode

/-! ## Pure facts -/

/-- The log as a map has the log's entries. -/
theorem logMap_lookup (log : List LogEntry) (x : Nat) : logMap log !! x = log[x]? := by
  have key : ∀ n, ((List.range n).foldl (fun m x => match log[x]? with
      | some e => <[x := e]> m
      | none => m) (∅ : GMap Nat LogEntry)) !! x = if x < n then log[x]? else none := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      cases hn : log[n]? with
      | none =>
        simp only []
        rw [ih]
        by_cases hx : x < n
        · simp [hx, Nat.lt_succ_of_lt hx]
        · by_cases hxn : x = n
          · subst hxn; simp [hn]
          · have : ¬ x < n + 1 := by omega
            simp [hx, this]
      | some e =>
        simp only []
        by_cases hxn : n = x
        · subst hxn; rw [GMap.lookup_insert]; simp [hn]
        · rw [GMap.lookup_insert_ne _ _ hxn, ih]
          by_cases hx : x < n
          · simp [hx, Nat.lt_succ_of_lt hx]
          · have : ¬ x < n + 1 := by omega
            simp [hx, this]
  unfold logMap
  refine (key log.length).trans ?_
  by_cases hx : x < log.length
  · simp [hx]
  · simp [hx, List.getElem?_eq_none (by omega : log.length ≤ x)]

/-- The claims a switch allocates: one on all the names of each directory of `js`. -/
def claimsInit (V : Hist) : List Ino → GMap (Ino × NameSet) NamesH
  | [] => ∅
  | j :: js => <[(j, .except []) := namesOf V j (.except [])]> (claimsInit V js)

theorem claimsInit_lookup (V : Hist) (js : List Ino) (k : Ino × NameSet) :
    claimsInit V js !! k = if k.2 = .except [] ∧ k.1 ∈ js then some (namesOf V k.1 k.2) else none := by
  induction js with
  | nil => simp [claimsInit]
  | cons j js ih =>
    unfold claimsInit
    by_cases hk : (j, NameSet.except []) = k
    · subst hk; rw [GMap.lookup_insert]; simp
    · rw [GMap.lookup_insert_ne _ _ hk, ih]
      obtain ⟨k1, k2⟩ := k
      by_cases h2 : k2 = .except []
      · subst h2
        have : k1 ≠ j := fun h => hk (by rw [h])
        simp [this]
      · simp [h2]

/-- The claims a switch allocates are coherent with the history. -/
theorem namesCoh_init (V : Hist) (hs : Starts V.2) :
    NamesCoh V (claimsInit V ((GMap.toList V.now).map (·.1))) := by
  refine ⟨fun j N h hl => ?_, fun j N N' h h' b hl hl' hne _ => ?_, fun j b hj => ?_,
    fun j N h hl => ?_, hs⟩
  · rw [claimsInit_lookup] at hl
    split at hl
    · cases hl; rfl
    · cases hl
  · rw [claimsInit_lookup] at hl hl'
    split at hl
    · split at hl'
      · rename_i h1 h2; exact absurd (h1.1.trans h2.1.symm) hne
      · cases hl'
    · cases hl
  · refine ⟨.except [], namesOf V j (.except []), ?_, by simp [NameSet.Mem]⟩
    rw [claimsInit_lookup]
    have hm : j ∈ (GMap.toList V.now).map (·.1) := by
      rw [GMap.mem_iff] at hj
      cases hv : V.now !! j with
      | none => rw [hv] at hj; exact absurd hj (by simp)
      | some v => exact List.mem_map.2 ⟨(j, v), (GMap.mem_toList _ _ _).2 hv, rfl⟩
    simp [hm]
  · rw [claimsInit_lookup] at hl
    split at hl
    · rename_i hk
      obtain ⟨⟨j1, v⟩, hv, hj1⟩ := List.mem_map.1 hk.2
      simp only at hj1
      subst hj1
      rw [GMap.mem_iff, (GMap.mem_toList _ _ _).1 hv]; rfl
    · cases hl

/-- The shared coherence of a state whose log is sequential, with no directory fd and no call: the
shared mode begun at the log's length. -/
theorem cohS_switch {st : OsState} {V : Hist} {Γdf : GMap w64 (Ino × DirPh)}
    {Γc : GMap Nat CallV} (hw : FsTreeWf st) (hc : TreeCoh st V Γdf Γc) (hdf : Γdf = ∅) (hcl : Γc = ∅) :
    TreeCohS st st.fs.metaLog.length ∅ ∅ ∅ := by
  have hseq := hc.seq
  have htw : TreeWf st.fs.roots st.tree := by
    have := (hw.hist st.fs.metaLog.length (Nat.le_refl _)).1
    rwa [List.take_of_length_le (by simp)] at this
  obtain ⟨ρ, hroots, hents⟩ := rootTags_exists hw.roots.2.1 htw
  have hlt : ∀ x (e : LogEntry), st.fs.metaLog[x]? = some e → x < st.fs.metaLog.length := by
    intro x e h
    exact (List.getElem?_eq_some_iff.1 h).1
  refine ⟨fun x e h => Nat.le_of_eq (hseq x e h), fun x y ex ey hyx hx _ _ => by rw [hseq x ex hx]; exact hyx,
    ⟨ρ, ⟨⟨hroots, fun t ht1 ht2 => ?_, fun x e hx he => absurd (hlt x e he) (by omega)⟩,
      fun x ex hx => ⟨fun _ => ⟨hseq x ex hx, fun z ez hz hez => by rw [hseq z ez hez]; exact hz⟩,
        fun _ => ⟨fun y ey h1 h2 => absurd h2 (by rw [hseq x ex hx] at h1; omega),
          fun z ez hz hez _ => by rw [hseq z ez hez]; exact hz⟩⟩,
      fun x e hx he => absurd (hlt x e he) (by omega)⟩,
      ⟨fun t x hx => by simp at hx, fun t x hx => by simp at hx, fun c x t g hx => by simp at hx⟩⟩,
    fun x e hx hn => absurd (Or.inr (hlt x e hx)) hn, Nat.le_refl _, fun fd => ?_,
    fun fd x df hx => by simp at hx, fun t x hx => by simp at hx, fun t x hx => by simp at hx,
    fun t x hx => by simp at hx, fun t x hx => by simp at hx, fun t s hs => ?_⟩
  · have hpt : prefTree st.fs.treeDur st.fs.metaLog st.fs.metaLog.length = st.tree := by
      simp [prefTree, OsState.tree]
    rw [show t = st.fs.metaLog.length by omega, hpt]; exact hents
  · have := hc.fds fd; rw [hdf] at this; simpa using this
  · have := hc.calls t; rw [hcl, hs] at this; simp at this

/-- A key of the logging or guard calls is a call in flight. -/
theorem TreeCohS.fresh {st : OsState} {s0 : Nat} {Γdf : GMap w64 (Ino × DirPhS)}
    {Γc Γg : GMap Nat CallV} (hc : TreeCohS st s0 Γdf Γc Γg) {t : Nat}
    (ht : st.proc.calls !! t = none) : Γc !! t = none ∧ Γg !! t = none := by
  constructor
  · cases h0 : Γc !! t with
    | none => rfl
    | some x => have := hc.calls t x h0; rw [ht] at this; cases this
  · cases h0 : Γg !! t with
    | none => rfl
    | some x => have := hc.gcalls t x h0; rw [ht] at this; cases this

/-- The state after `CallBegin` of the call `t` on `p`. -/
abbrev OsState.callBegin (st : OsState) (t : Nat) (p : GoString) : OsState :=
  st.setProc { st.proc with calls := <[t := (st.fs.metaLog.length, p)]> st.proc.calls }

/-- The shared coherence with a logging call begun, holding `q`. -/
theorem treeCohS_begin {st : OsState} {s0 : Nat} {Γdf : GMap w64 (Ino × DirPhS)}
    {Γc Γg : GMap Nat CallV} (hc : TreeCohS st s0 Γdf Γc Γg) (t : Nat) (p : GoString) (q : Qp)
    (ht : st.proc.calls !! t = none) :
    TreeCohS (st.callBegin t p) s0 Γdf (<[t := (((st.fs.metaLog.length, p), q) : CallV)]> Γc) Γg := by
  obtain ⟨hct, hgt⟩ := hc.fresh ht
  have hnone : ∀ y, st.fs.metaLog.length ≤ y → st.fs.metaLog[y]? = none := fun y hy =>
    List.getElem?_eq_none_iff.2 hy
  refine ⟨hc.starts, hc.pss, hc.rc.elim (fun ρ h => ⟨ρ, h.1.congr rfl rfl rfl, ?_⟩), hc.valid, hc.s0le,
    hc.fds, hc.ph, fun t0 x hx => ?_, fun t0 x hx => ?_, fun t0 x hx => ?_,
    fun t0 x hx => ?_, fun t0 s hs => ?_⟩
  · obtain ⟨hw, ha, hp⟩ := h.2
    refine ⟨fun t0 x hx hq y ey hy he => ?_, fun t0 x hx y ey he hd => ?_,
      fun c x t0 g hx hg hk hq hle y ey hy he => ?_⟩
    · by_cases h0 : t = t0
      · subst h0; rw [GMap.lookup_insert] at hx; cases hx
        change st.fs.metaLog[y]? = some ey at he; rw [hnone y hy] at he; cases he
      · rw [GMap.lookup_insert_ne _ _ h0] at hx; exact hw t0 x hx hq y ey hy he
    · by_cases h0 : t = t0
      · subst h0; rw [GMap.lookup_insert] at hx; cases hx
        exact (List.getElem?_eq_some_iff.1 he).1
      · rw [GMap.lookup_insert_ne _ _ h0] at hx; exact ha t0 x hx y ey he hd
    · by_cases h0 : t = c
      · subst h0; rw [GMap.lookup_insert] at hx; cases hx
        change st.fs.metaLog[y]? = some ey at he; rw [hnone y hy] at he; cases he
      · rw [GMap.lookup_insert_ne _ _ h0] at hx; exact hp c x t0 g hx hg hk hq hle y ey hy he
  · show (<[t := (st.fs.metaLog.length, p)]> st.proc.calls) !! t0 = _
    by_cases h0 : t = t0
    · subst h0; rw [GMap.lookup_insert] at hx; cases hx; simp
    · rw [GMap.lookup_insert_ne _ _ h0] at hx; rw [GMap.lookup_insert_ne _ _ h0]; exact hc.calls t0 x hx
  · by_cases h0 : t = t0
    · subst h0; rw [GMap.lookup_insert] at hx; cases hx; exact Nat.le_refl _
    · rw [GMap.lookup_insert_ne _ _ h0] at hx; exact hc.callsLe t0 x hx
  · show (<[t := (st.fs.metaLog.length, p)]> st.proc.calls) !! t0 = _
    by_cases h0 : t = t0
    · subst h0; rw [hgt] at hx; cases hx
    · rw [GMap.lookup_insert_ne _ _ h0]; exact hc.gcalls t0 x hx
  · by_cases h0 : t = t0
    · subst h0; rw [hgt] at hx; cases hx
    · rw [GMap.lookup_insert_ne _ _ h0]; exact hc.gdisj t0 x hx
  · change (<[t := (st.fs.metaLog.length, p)]> st.proc.calls) !! t0 = some s at hs
    by_cases h0 : t = t0
    · subst h0; left; rw [GMap.lookup_insert]; simp
    · rw [GMap.lookup_insert_ne _ _ h0] at hs; rw [GMap.lookup_insert_ne _ _ h0]; exact hc.cover t0 s hs

/-- The shared coherence with a guard call begun, holding `g`. -/
theorem treeCohS_beginGuard {st : OsState} {s0 : Nat} {Γdf : GMap w64 (Ino × DirPhS)}
    {Γc Γg : GMap Nat CallV} (hc : TreeCohS st s0 Γdf Γc Γg) (t : Nat) (p : GoString) (g : Qp)
    (ht : st.proc.calls !! t = none) :
    TreeCohS (st.callBegin t p) s0 Γdf Γc (<[t := (((st.fs.metaLog.length, p), g) : CallV)]> Γg) := by
  obtain ⟨hct, hgt⟩ := hc.fresh ht
  have hnone : ∀ y, st.fs.metaLog.length ≤ y → st.fs.metaLog[y]? = none := fun y hy =>
    List.getElem?_eq_none_iff.2 hy
  refine ⟨hc.starts, hc.pss, hc.rc.elim (fun ρ h => ⟨ρ, h.1.congr rfl rfl rfl, ?_⟩), hc.valid, hc.s0le,
    hc.fds, hc.ph, fun t0 x hx => ?_, hc.callsLe, fun t0 x hx => ?_,
    fun t0 x hx => ?_, fun t0 s hs => ?_⟩
  · obtain ⟨hw, ha, hp⟩ := h.2
    refine ⟨hw, ha, fun c x t0 g' hx hg hk hq hle y ey hy he => ?_⟩
    by_cases h0 : t = t0
    · subst h0; rw [GMap.lookup_insert] at hg; cases hg
      have := Nat.le_antisymm (hc.callsLe c x hx) hle
      change st.fs.metaLog[y]? = some ey at he
      have hy' : st.fs.metaLog.length ≤ y := by
        have : x.1.1 = st.fs.metaLog.length := this
        omega
      rw [hnone y hy'] at he; cases he
    · rw [GMap.lookup_insert_ne _ _ h0] at hg; exact hp c x t0 g' hx hg hk hq hle y ey hy he
  · show (<[t := (st.fs.metaLog.length, p)]> st.proc.calls) !! t0 = _
    by_cases h0 : t = t0
    · subst h0; rw [hct] at hx; cases hx
    · rw [GMap.lookup_insert_ne _ _ h0]; exact hc.calls t0 x hx
  · show (<[t := (st.fs.metaLog.length, p)]> st.proc.calls) !! t0 = _
    by_cases h0 : t = t0
    · subst h0; rw [GMap.lookup_insert] at hx; cases hx; simp
    · rw [GMap.lookup_insert_ne _ _ h0] at hx; rw [GMap.lookup_insert_ne _ _ h0]; exact hc.gcalls t0 x hx
  · by_cases h0 : t = t0
    · subst h0; exact hct
    · rw [GMap.lookup_insert_ne _ _ h0] at hx; exact hc.gdisj t0 x hx
  · change (<[t := (st.fs.metaLog.length, p)]> st.proc.calls) !! t0 = some s at hs
    by_cases h0 : t = t0
    · subst h0; right; rw [GMap.lookup_insert]; simp
    · rw [GMap.lookup_insert_ne _ _ h0] at hs; rw [GMap.lookup_insert_ne _ _ h0]; exact hc.cover t0 s hs

theorem osShN_sub {E : CoPset} (h : ↑osShN ⊆ E) : (↑osShN : CoPset) ⊆ E \ ↑osN := by
  have hd : (↑osShN : CoPset) ## ↑osN := ndot_ne_disjoint nroot (by decide)
  intro p hp
  exact LawfulSet.mem_diff.2 ⟨h p hp, fun hn => hd p ⟨hp, hn⟩⟩

section ghost
variable {GF : BundledGFunctors} (hL : OsGS GF)

/-- The claims a switch allocates, from the empty authority. -/
theorem claims_alloc (V : Hist) : ∀ js : List Ino, js.Nodup →
    ⊢ gAuth hL hL.γn (∅ : GMap (Ino × NameSet) NamesH) ==∗
      gAuth hL hL.γn (claimsInit V js) ∗
      [∗list] j ∈ js, gElem hL hL.γn (j, NameSet.except []) (DFrac.own 1)
        (namesOf V j (.except []))
  | [], _ => by
    rw [show claimsInit V [] = ∅ from rfl]
    iintro H
    imodintro
    iframe H
    iapply BigSepL.bigSepL_nil.2; itrivial
  | j :: js, hnd => by
    have hj : j ∉ js := (List.nodup_cons.1 hnd).1
    iintro H
    imod claims_alloc V js (List.nodup_cons.1 hnd).2 $$ H with ⟨H, Hs⟩
    have hfresh : claimsInit V js !! (j, .except []) = none := by
      rw [claimsInit_lookup]; simp [hj]
    imod gAuth_insert hL _ _ _ (namesOf V j (.except [])) hfresh $$ H with ⟨H, Hj⟩
    imodintro
    rw [show claimsInit V (j :: js) =
      <[(j, NameSet.except []) := namesOf V j (.except [])]> (claimsInit V js) from rfl]
    iframe H
    iapply BigSepL.bigSepL_cons.2
    iframe

/-- The log's map, from the empty authority. -/
theorem log_alloc (log : List LogEntry) :
    ⊢ gAuth hL hL.γlog (∅ : GMap Nat LogEntry) ==∗ gAuth hL hL.γlog (logMap log) := by
  unfold gAuth
  letI := hL.osAllG
  iintro H
  imod ghost_map_insert_big (logMap log) (fun k _ h => by simp at h) $$ H with ⟨H, -⟩
  have : logMap log ∪ (∅ : GMap Nat LogEntry) = logMap log := by
    apply GMap.ext; intro k; simp [gmap_lookup_union]
  rw [this]
  imodintro; iexact H

/-- The call permission of every key, from the empty authority. -/
theorem perm_alloc (R : Roots) :
    ⊢ gAuth hL hL.γperm (∅ : GMap GoString Unit) ==∗
      [∗map] r ↦ u ∈ permMap R, gElem hL hL.γperm r (DFrac.own 1) u := by
  unfold gAuth gElem
  letI := hL.osAllG
  iintro H
  imod ghost_map_insert_big (permMap R) (fun k _ h => by simp at h) $$ H with ⟨-, H⟩
  imodintro; iexact H

end ghost

/-! ## The switch and `CallBegin` -/

section specs
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext] [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
variable {s : Stuckness} {E : CoPset}

theorem histMap_insert_empty (RV : Roots × Hist) :
    (<[() := RV]> (∅ : GMap Unit (Roots × Hist))) = histMap RV := by
  apply GMap.ext; intro u; cases u; simp [histMap]

theorem wp_osShare' (R : Roots) (V : Hist) (op : String) (v : val) (hE : ↑osN ⊆ E)
    (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osTree (L := L) (DFrac.own 1) R V -∗
      (osSharedInv (L := L) R -∗ osCallPerms (L := L) R -∗ osLogLb (L := L) V.2.length -∗
        ([∗list] j ∈ (GMap.toList V.now).map (·.1),
          osNames (L := L) j (.except []) (DFrac.own 1) (namesOf V j (.except []))) -∗
        WP (ExternalOp fsExt.name op (Val v)) @ s; E {{ Φ }}) -∗
      WP (ExternalOp fsExt.name op (Val v)) @ s; E {{ Φ }} := by
  iintro #Hinv Hh HΦ
  iapply wp_ext_acc (X := fsExt) (ExternalOp fsExt.name op (Val v)) Φ rfl
  iintro %σ %g Hl Hg
  icases (os_local_ctx_eq σ).mp $$ Hl with Hl
  unfold osCtx
  icases Hl with ⟨HF, Ht, Hof⟩
  icases treeCtx_legacy _ (legacyWit_tree _ _ _) σ $$ Hh Ht with ⟨Hh, Ht, Hcm⟩
  unfold treeLegacy legacyHolds
  icases Ht with ⟨%V0, %Γdf, %Γc, %hns, HAd, HAdf, HAc, Hrd, Hcr, Has, Hadfs, Hacs, Hperm, Han,
    Halen, Halog, Hag⟩
  icases osTree_auth _ _ _ _ _ $$ HAd Hh with %Heq
  obtain ⟨rfl, rfl⟩ := Heq
  icases whole_alone _ _ Γdf Γc $$ Hh Hrd Hcr with ⟨%Hal, Hh, -, -⟩
  obtain ⟨hdf, hcl⟩ := Hal
  have hcohS := cohS_switch hns.1 hns.2 hdf hcl
  have hV : V = (σ.fs.treeDur, σ.fs.metaLog) := hns.2.hist
  subst hdf hcl
  imod gAuth_insert _ _ _ () (σ.fs.roots, V) (by rfl) $$ Has with ⟨Has, Hs⟩
  rw [histMap_insert_empty]
  imod (letI := (gooseOsGS (L := L)).osAllG;
    mono_nat_own_update (γ := (gooseOsGS (L := L)).γlen) V.2.length (Nat.zero_le _)) $$ Halen
    with ⟨Halen, #Hlb⟩
  imod log_alloc _ V.2 $$ Halog with Halog
  imod perm_alloc _ σ.fs.roots $$ Hperm with Hperm
  imod claims_alloc _ V _ (GMap.toList_keys_nodup _) $$ Han with ⟨Han, Hcl⟩
  imod inv_alloc osShN E iprop(∃ (Vs : Hist) (Γn : GMap (Ino × NameSet) NamesH),
    gElem (gooseOsGS (L := L)) (gooseOsGS (L := L)).γs () (DFrac.own 1) (σ.fs.roots, Vs) ∗
    gAuth (gooseOsGS (L := L)) (gooseOsGS (L := L)).γn Γn ∗ ⌜RootsOk σ.fs.roots ∧ NamesCoh Vs Γn⌝ ∗
    (letI := (gooseOsGS (L := L)).osAllG; monoNatAuthOwn (gooseOsGS (L := L)).γlen 1 Vs.2.length) ∗
    gAuth (gooseOsGS (L := L)) (gooseOsGS (L := L)).γlog (logMap Vs.2)) $$ [Hs Han Halen Halog]
    with #Hsi
  · inext
    iexists V, (claimsInit V ((GMap.toList V.now).map (·.1)))
    iframe Hs Han Halen Halog
    ipureintro; exact ⟨hns.1.roots, namesCoh_init V (by rw [hV]; exact hcohS.starts)⟩
  imodintro
  isplitl [HF Hh HAd HAdf HAc Has Hadfs Hacs Hag Hcm Hof]
  · iapply (os_local_ctx_eq σ).mpr
    unfold osCtx treeCtx
    iframe HF Hcm Hof
    iright
    unfold treeShared
    iexists V, σ.fs.metaLog.length, ∅, ∅, ∅
    rw [← hV]
    unfold osTree
    iframe HAd Hh HAdf HAc Has Hadfs Hacs Hag
    isplitr
    · ipureintro; exact ⟨hns.1, hcohS⟩
    unfold callResS
    isplitl []
    · iapply BigSepM.bigSepM_empty.2; itrivial
    · iapply BigSepM.bigSepM_empty.2; itrivial
  iframe Hg
  simp only [osNames_except]
  unfold osSharedInv osCallPerms osCallPerm osLogLb
  iapply HΦ $$ Hsi Hperm Hlb Hcl

instance osSharedBody_timeless (R : Roots) : Timeless (PROP := IProp GF)
    iprop(∃ (Vs : Hist) (Γn : GMap (Ino × NameSet) NamesH),
      gElem (gooseOsGS (L := L)) (gooseOsGS (L := L)).γs () (DFrac.own 1) (R, Vs) ∗
      gAuth (gooseOsGS (L := L)) (gooseOsGS (L := L)).γn Γn ∗ ⌜RootsOk R ∧ NamesCoh Vs Γn⌝ ∗
      (letI := (gooseOsGS (L := L)).osAllG; monoNatAuthOwn (gooseOsGS (L := L)).γlen 1 Vs.2.length) ∗
      gAuth (gooseOsGS (L := L)) (gooseOsGS (L := L)).γlog (logMap Vs.2)) := by
  letI := (gooseOsGS (L := L)).osAllG; infer_instance

theorem commitRes_setProc (st : OsState) (p : ProcState) :
    commitRes (gooseOsGS (L := L)) st ⊢ commitRes (gooseOsGS (L := L)) (st.setProc p) :=
  commitRes_grow _ (commitGrows_of_eq rfl)

/-- A shared resource (a fraction of the call permission) excludes the legacy mode. -/
theorem legacy_perm_excl (st : OsState) (r : GoString) (q : Qp) :
    ⊢ osCallPerm (L := L) r q -∗ treeLegacy (gooseOsGS (L := L)) st -∗ False := by
  unfold treeLegacy legacyHolds osCallPerm
  iintro Hq ⟨%V0, %Γdf, %Γc, %hns, -, -, -, -, -, -, -, -, Hperm, -⟩
  icases gAuth_lookup _ _ _ _ _ _ $$ Hperm Hq with %Hv
  simp at Hv

theorem wp_osCallBeginS' (R : Roots) (p : GoString) (q : Qp) (n : Nat) (hE : ↑osN ⊆ E)
    (hE' : ↑osShN ⊆ E) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osSharedInv (L := L) R -∗ osCallPerm (L := L) (callKey R p) q -∗
      osLogLb (L := L) n -∗
      (∀ (t s0 : Nat), ⌜n ≤ s0⌝ -∗ osCallS (L := L) t s0 p q -∗ osLogLb (L := L) s0 -∗
        Φ (osTokV t)) -∗
      WP (ExternalOp fsExt.name "CallBegin" (Val (#p))) @ s; E {{ Φ }} := by
  iintro #Hinv #Hsi Hq #Hlb HΦ
  iapply wp_fs_stepM "CallBegin" _ Φ (by simp [val.isPanic]) hE $$ Hinv
  iintro %st %Γb %Γm %Γf %Γt %h Hw Ht
  unfold treeCtx
  icases Ht with ⟨Hm, Hcm⟩
  icases Hm with (Hm | Hm)
  · iexfalso; iapply legacy_perm_excl st _ q $$ Hq Hm
  unfold treeShared
  icases Hm with ⟨%V0, %s0, %Γdf, %Γc, %Γg, %hns, HAd, Hd, HAdf, HAc, Has, Hadfs, Hacs, Hcr, HAg, Hgr⟩
  obtain ⟨hw, hc⟩ := hns
  unfold osSharedInv
  imod inv_acc (osShN_sub hE') $$ Hsi with ⟨Hi, Hclose⟩
  icases Hi with >Hi
  icases Hi with ⟨%Vs, %Γn, Hs, HAn, %hcoh, Halen, HAlog⟩
  icases gAuth_lookup _ _ _ _ _ _ $$ Has Hs with %hVs
  simp only [histMap, GMap.lookup_singleton_eq, Option.some.injEq, Prod.mk.injEq] at hVs
  obtain ⟨hR, rfl⟩ := hVs
  unfold osLogLb
  icases (letI := (gooseOsGS (L := L)).osAllG; monoNatLbOwn_valid _ _ _ _) $$ Halen Hlb with %hn
  ihave #Hlb' := (letI := (gooseOsGS (L := L)).osAllG; monoNatLbOwn_get _ _ _) $$ Halen
  imod Hclose $$ [Hs HAn Halen HAlog] with -
  · inext; iexists _, Γn; iframe; ipureintro; exact hcoh
  unfold osWorld
  icases Hw with ⟨%Hwc, HAb, HAm, HAf, HAt, Htok, Hcells, Hσ⟩
  obtain ⟨hwf, hcoh'⟩ := Hwc
  icases cellsRes_lookup h _ $$ Hσ Hcells with %Hag
  obtain ⟨t, ht1, ht2⟩ := exists_fresh2 st.proc.calls st.proc.inflight
  have hs : FilesSame st (st.setProc { st.proc with
      calls := <[t := (st.fs.metaLog.length, p)]> st.proc.calls }) := ⟨rfl, rfl, rfl, rfl, rfl⟩
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ E \ ↑osN from Std.LawfulSet.empty_subset)
  iintro Hclose2
  isplitr
  · ipureintro
    obtain ⟨hfr, hr⟩ := step_filesSame (h := h) hwf hs Hag
    exact ⟨_, h, _, ⟨t, p, rfl, ht1, ht2, rfl, rfl⟩, hfr, hr⟩
  inext
  iintro %e' %h' %st' %Hst
  imod Hclose2
  obtain ⟨Hst, Hfr, Hr⟩ := Hst
  simp only [IsFsStep] at Hst
  obtain ⟨t', p', hpv, h1', h2', rfl, rfl⟩ := Hst
  cases go.intoVal_inj hpv
  imod osWorld_filesSame (st := st)
    (st' := st.setProc { st.proc with calls := <[t' := (st.fs.metaLog.length, p)]> st.proc.calls })
    ⟨rfl, rfl, rfl, rfl, rfl⟩ Hr Hfr $$ [HAb HAm HAf HAt Htok Hcells Hσ]
    with Hw
  · unfold osWorld; iframe; ipureintro; exact ⟨hwf, hcoh'⟩
  have hΓc : Γc !! t' = none := (hc.fresh h1').1
  imod gAuth_insert _ _ _ _ (((st.fs.metaLog.length, p), q) : CallV) hΓc $$ Hacs with ⟨Hacs, Hk⟩
  imodintro
  iexists Γb, Γm, Γf, Γt
  dsimp only
  isplitl [Hw]
  · unfold osWorld; iexact Hw
  isplitl [HAd Hd HAdf HAc Has Hadfs Hacs Hcr HAg Hgr Hq Hcm]
  · isplitr [Hcm]
    rotate_left
    · iapply commitRes_setProc $$ Hcm
    iright
    simp only [OsState.setProc]
    iexists V0, s0, Γdf, <[t' := (((st.fs.metaLog.length, p), q) : CallV)]> Γc, Γg
    iframe HAd Hd HAdf HAc Has Hadfs Hacs HAg Hgr
    isplitr
    · ipureintro
      exact ⟨⟨hw.roots, hw.hist, hw.dfds, hw.disj, hw.files_lt⟩, treeCohS_begin hc t' p q h1'⟩
    · unfold callResS
      iapply (BigSepM.bigSepM_insert (Φ := fun (_t : Nat) (x : CallV) =>
        gElem (gooseOsGS (L := L)) (gooseOsGS (L := L)).γperm (callKey st.fs.roots x.1.2)
          (DFrac.own x.2) ()) hΓc).2
      iframe Hcr
      unfold osCallPerm; rw [hR]; iexact Hq
  iapply wp_value'
  unfold osCallS
  iapply HΦ $$ %t' %st.fs.metaLog.length %hn.2 Hk Hlb'

end specs

end Fs
end Perennial

end
