/-
`updateAttributes`, `mergeAttributes`, `equal` against the model's `updateAttributes`,
`mergeAttributes`, `depsEqual`.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.epaxos.HCtx

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net github_com.imdea_software.swiftpaxos_epaxos.kvs
open model epaxosProof

attribute [local instance] GooseGlobalGS.gooseInvGS

variable [GooseExts]

theorem getD_of_lt {α : Type} (l : List α) (k : Nat) (a : α) (h : k < l.length) :
    l.getD k a = l[k] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]; rfl

theorem depsEqual_true_of (d1 d2 : List w32)
    (h : ∀ j < d1.length, d1.getD j (W32 0) = d2.getD j (W32 0)) : depsEqual d1 d2 = true := by
  simp only [depsEqual, List.all_eq_true, List.mem_range, beq_iff_eq]
  exact h

theorem depsEqual_false_of (d1 d2 : List w32) (k : Nat) (hk : k < d1.length)
    (h : d1.getD k (W32 0) ≠ d2.getD k (W32 0)) : depsEqual d1 d2 = false := by
  simp only [depsEqual, List.all_eq_false, List.mem_range, beq_iff_eq]
  exact ⟨k, hk, h⟩

theorem take_succ_foldl {α β : Type} (f : α → β → α) (a : α) (l : List β) (j : Nat) (b : β)
    (h : l[j]? = some b) : (l.take (j + 1)).foldl f a = f ((l.take j).foldl f a) b := by
  rw [List.take_succ, h, List.foldl_append]; rfl

/-- One raise of `updateAttributes`' first loop in row `q` over the entry `d`
(`if d > deps[q] { deps[q] = d; if seq <= InstanceSpace[q][d].Seq {...}; changed = true }`). -/
def uaDS (σ : RState) (q : Nat) (acc : w32 × List w32 × Bool) (d : w32) :
    w32 × List w32 × Bool :=
  if (acc.2.1.getD q (W32 0)).slt d then
    let dseq := ((σ.inst ⟨q, toN d⟩).map (·.seq)).getD (W32 0)
    (if acc.1.sle dseq then dseq + 1 else acc.1, acc.2.1.set q d, true)
  else acc

/-- The key's step (the conflicts map's entry) of one command in row `q`. -/
def uaKey (σ : RState) (q : Nat) (acc : w32 × List w32 × Bool) (c : WCmd) :
    w32 × List w32 × Bool :=
  match σ.conflicts q c.key with
  | none => acc
  | some p => uaDS σ q acc (if c.op ≠ opGET then p.last else p.lastWrite)

/-- The class entry (fix S1) read for command `c` in row `q`. -/
def uaCls (σ : RState) (q : Nat) (c : WCmd) : w32 :=
  if c.op = opSCAN then σ.lastPut q else if c.op = opPUT then σ.lastScan q else W32 (-1)

/-- One command of `updateAttributes`' first loop, in row `q`: the key's entry, then the class
entry (stage 2). -/
def uaStep (σ : RState) (q : Nat) (acc : w32 × List w32 × Bool) (c : WCmd) :
    w32 × List w32 × Bool :=
  uaDS σ q (uaKey σ q acc c) (uaCls σ q c)

/-- One row of `updateAttributes`' first loop. -/
def uaRow (σ : RState) (cmds : List WCmd) (acc : w32 × List w32 × Bool) (q : Nat) :
    w32 × List w32 × Bool :=
  cmds.foldl (uaStep σ q) acc

/-- One command of `updateAttributes`' second loop. -/
def uaMsk (σ : RState) (acc : w32 × List w32 × Bool) (c : WCmd) : w32 × List w32 × Bool :=
  match σ.maxSeqPerKey c.key with
  | some s => if acc.1.sle s then (s + 1, acc.2.1, true) else acc
  | none => acc

/-- The first loop after `k` rows. -/
def uaAcc (σ : RState) (cmds : List WCmd) (seq : w32) (deps : List w32) (k : Nat) :
    w32 × List w32 × Bool :=
  (List.range k).foldl (uaRow σ cmds) (seq, deps, false)

/-- The first loop's row `k` after `j` commands. -/
def uaIn (σ : RState) (cmds : List WCmd) (seq : w32) (deps : List w32) (k j : Nat) :
    w32 × List w32 × Bool :=
  (cmds.take j).foldl (uaStep σ k) (uaAcc σ cmds seq deps k)

theorem uaIn_succ (σ : RState) (cmds : List WCmd) (seq : w32) (deps : List w32) (k j : Nat)
    (c : WCmd) (hc : cmds[j]? = some c) :
    uaIn σ cmds seq deps k (j + 1) = uaStep σ k (uaIn σ cmds seq deps k j) c := by
  unfold uaIn; rw [take_succ_foldl _ _ _ _ _ hc]

theorem uaKey_none (σ : RState) (k : Nat) (acc : w32 × List w32 × Bool) (c : WCmd)
    (h : σ.conflicts k c.key = none) : uaKey σ k acc c = acc := by
  unfold uaKey; rw [h]

theorem uaKey_some' (σ : RState) (k : Nat) (acc : w32 × List w32 × Bool) (c : WCmd)
    (pr : InstPair) (h : σ.conflicts k c.key = some pr) :
    uaKey σ k acc c = uaDS σ k acc (if c.op ≠ opGET then pr.last else pr.lastWrite) := by
  unfold uaKey; rw [h]

theorem uaAcc_succ (σ : RState) (cmds : List WCmd) (seq : w32) (deps : List w32) (k : Nat) :
    uaAcc σ cmds seq deps (k + 1) = uaRow σ cmds (uaAcc σ cmds seq deps k) k := by
  unfold uaAcc; rw [List.range_succ, List.foldl_append]; rfl

theorem uaIn_len (σ : RState) (cmds : List WCmd) (seq : w32) (deps : List w32) (k : Nat) :
    uaIn σ cmds seq deps k cmds.length = uaAcc σ cmds seq deps (k + 1) := by
  rw [uaAcc_succ]; unfold uaIn uaRow; rw [List.take_length]

theorem uaMsk_deps (σ : RState) (l : List WCmd) (acc : w32 × List w32 × Bool) :
    (l.foldl (uaMsk σ) acc).2.1 = acc.2.1 := by
  induction l generalizing acc with
  | nil => rfl
  | cons c l ih =>
    rw [List.foldl_cons, ih]; unfold uaMsk
    split
    · split <;> rfl
    · rfl

theorem uaMsk_none (σ : RState) (acc : w32 × List w32 × Bool) (c : WCmd)
    (h : σ.maxSeqPerKey c.key = none) : uaMsk σ acc c = acc := by
  unfold uaMsk; rw [h]

theorem uaMsk_some (σ : RState) (acc : w32 × List w32 × Bool) (c : WCmd) (s : w32)
    (h : σ.maxSeqPerKey c.key = some s) :
    uaMsk σ acc c = if sint.Z acc.1 ≤ sint.Z s then (s + 1, acc.2.1, true) else acc := by
  unfold uaMsk; rw [h]; simp only
  by_cases hs : sint.Z acc.1 ≤ sint.Z s
  · rw [if_pos ((sle_iff _ _).mpr hs), if_pos hs]
  · rw [if_neg (fun e => hs ((sle_iff _ _).mp e)), if_neg hs]

theorem uaDS_eq (σ : RState) (k : Nat) (acc : w32 × List w32 × Bool) (d : w32)
    (hk : k < acc.2.1.length) :
    uaDS σ k acc d =
      if sint.Z acc.2.1[k] < sint.Z d then
        (if sint.Z acc.1 ≤ sint.Z (((σ.inst ⟨k, toN d⟩).map (·.seq)).getD (W32 0))
         then (((σ.inst ⟨k, toN d⟩).map (·.seq)).getD (W32 0)) + 1 else acc.1,
         acc.2.1.set k d, true)
      else acc := by
  unfold uaDS; simp only; rw [getD_of_lt _ _ _ hk]
  by_cases h1 : sint.Z acc.2.1[k] < sint.Z d
  · rw [if_pos ((slt_iff _ _).mpr h1), if_pos h1]
    by_cases h2 : sint.Z acc.1 ≤ sint.Z (((σ.inst ⟨k, toN d⟩).map (·.seq)).getD (W32 0))
    · rw [if_pos ((sle_iff _ _).mpr h2), if_pos h2]
    · rw [if_neg (fun e => h2 ((sle_iff _ _).mp e)), if_neg h2]
  · rw [if_neg (fun e => h1 ((slt_iff _ _).mp e)), if_neg h1]

/-- The instance a conflicts-map entry points to exists, in the row's range. -/
theorem ua_target (σ : RState) (hconf : ConfWf σ) (hib : instBounds σ.inst) (k : Nat) (c : WCmd)
    (pr : InstPair) (hp : σ.conflicts k c.key = some pr)
    (h0 : 0 ≤ sint.Z (if c.op ≠ opGET then pr.last else pr.lastWrite)) :
    ∃ w, σ.inst ⟨k, toN (if c.op ≠ opGET then pr.last else pr.lastWrite)⟩ = some w ∧
      toN (if c.op ≠ opGET then pr.last else pr.lastWrite) + 1 < MAX_INSTANCE := by
  obtain ⟨-, h1, h2⟩ := hconf.1 k c.key pr hp
  have hne : σ.inst ⟨k, toN (if c.op ≠ opGET then pr.last else pr.lastWrite)⟩ ≠ none := by
    by_cases ho : c.op ≠ opGET
    · rw [if_pos ho] at h0 ⊢; exact h1 h0
    · rw [if_neg ho] at h0 ⊢; exact h2 h0
  obtain ⟨w, hw⟩ := Option.ne_none_iff_exists'.mp hne
  refine ⟨w, hw, Classical.byContradiction fun hc => ?_⟩
  have := hib ⟨k, toN (if c.op ≠ opGET then pr.last else pr.lastWrite)⟩ (Or.inr (by simp only; omega))
  rw [hw] at this; exact absurd this (by simp)

/-- The instance a class entry (`lastPut[q]`/`lastScan[q]`) points to exists, in the row's
range (`ConfWf`'s second clause). -/
theorem ua_cls_target (σ : RState) (hconf : ConfWf σ) (hib : instBounds σ.inst) (k : Nat)
    (hk : k < nR) (c : WCmd) (h0 : 0 ≤ sint.Z (uaCls σ k c)) :
    ∃ w, σ.inst ⟨k, toN (uaCls σ k c)⟩ = some w ∧ toN (uaCls σ k c) + 1 < MAX_INSTANCE := by
  obtain ⟨h1, h2, -, -⟩ := hconf.2 k hk
  have hne : σ.inst ⟨k, toN (uaCls σ k c)⟩ ≠ none := by
    unfold uaCls at h0 ⊢
    by_cases hs : c.op = opSCAN
    · rw [if_pos hs] at h0 ⊢; exact h2 h0
    · rw [if_neg hs] at h0 ⊢
      by_cases hp : c.op = opPUT
      · rw [if_pos hp] at h0 ⊢; exact h1 h0
      · rw [if_neg hp] at h0; exact absurd h0 (by decide)
  obtain ⟨w, hw⟩ := Option.ne_none_iff_exists'.mp hne
  refine ⟨w, hw, Classical.byContradiction fun hc => ?_⟩
  have := hib ⟨k, toN (uaCls σ k c)⟩ (Or.inr (by simp only; omega))
  rw [hw] at this; exact absurd this (by simp)

theorem depsOk_set (l : List w32) (k : Nat) (d : w32) (h : depsOk l)
    (hd : 0 ≤ sint.Z d ∧ toN d + 1 < MAX_INSTANCE) : depsOk (l.set k d) := by
  refine ⟨by rw [List.length_set]; exact h.1, fun x hx => ?_⟩
  rcases List.mem_or_eq_of_mem_set hx with hx | rfl
  · exact h.2 x hx
  · exact Or.inr hd

theorem updP_self' {α : Type} (P : InstId → α) (x : InstId) : updP P x (P x) = P := by
  funext y; unfold updP; split
  · subst_vars; rfl
  · rfl

theorem updateAttributes_eq (σ : RState) (cmds : List WCmd) (seq : w32) (deps : List w32) :
    updateAttributes σ cmds seq deps = cmds.foldl (uaMsk σ) (uaAcc σ cmds seq deps nR) := rfl

/-- One row of `mergeAttributes`' loop. -/
def mstep (deps2 : List w32) (acc : List w32 × Bool) (q : Nat) : List w32 × Bool :=
  let a := acc.1.getD q (W32 0)
  let b := deps2.getD q (W32 0)
  if a ≠ b then (if a.slt b then acc.1.set q b else acc.1, false) else acc

theorem mergeAttributes_eq (seq1 : w32) (deps1 : List w32) (seq2 : w32) (deps2 : List w32) :
    mergeAttributes seq1 deps1 seq2 deps2 =
      (if seq1 ≠ seq2 ∧ seq1.slt seq2 then seq2 else seq1,
       ((List.range nR).foldl (mstep deps2) (deps1, true)).1,
       (seq1 == seq2) && ((List.range nR).foldl (mstep deps2) (deps1, true)).2) := rfl

theorem mstep_len (deps2 : List w32) (l : List Nat) (acc : List w32 × Bool) :
    (l.foldl (mstep deps2) acc).1.length = acc.1.length := by
  induction l generalizing acc with
  | nil => rfl
  | cons x l ih =>
    simp only [List.foldl_cons]; rw [ih]; unfold mstep; simp only
    split
    · split <;> simp
    · rfl

theorem mstep_range_succ (deps2 deps1 : List w32) (k : Nat) :
    (List.range (k + 1)).foldl (mstep deps2) (deps1, true) =
      mstep deps2 ((List.range k).foldl (mstep deps2) (deps1, true)) k := by
  rw [List.range_succ, List.foldl_append]; rfl

theorem mstep_eq (deps2 : List w32) (acc : List w32 × Bool) (q : Nat) (hq1 : q < acc.1.length)
    (hq2 : q < deps2.length) (h : acc.1[q] = deps2[q]) : mstep deps2 acc q = acc := by
  unfold mstep; rw [getD_of_lt _ _ _ hq1, getD_of_lt _ _ _ hq2]; simp [h]

theorem mstep_ne (deps2 : List w32) (acc : List w32 × Bool) (q : Nat) (hq1 : q < acc.1.length)
    (hq2 : q < deps2.length) (h : ¬ acc.1[q] = deps2[q]) : mstep deps2 acc q =
      (if sint.Z acc.1[q] < sint.Z deps2[q] then acc.1.set q deps2[q] else acc.1, false) := by
  unfold mstep; rw [getD_of_lt _ _ _ hq1, getD_of_lt _ _ _ hq2]; simp only [ne_eq, h,
    not_false_eq_true, if_true]
  congr 1
  by_cases hs : sint.Z acc.1[q] < sint.Z deps2[q]
  · rw [if_pos ((slt_iff _ _).mpr hs), if_pos hs]
  · rw [if_neg (fun e => hs ((slt_iff _ _).mp e)), if_neg hs]

theorem mstep_self (deps : List w32) (l : List Nat) :
    l.foldl (mstep deps) (deps, true) = (deps, true) := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    simp only [List.foldl_cons]
    have : mstep deps (deps, true) x = (deps, true) := by unfold mstep; simp
    rw [this]; exact ih

section heap
variable [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [go.Semantics]
variable [epaxos.Assumptions] [HasExt netExt] [π : NetProtoGS]
variable [state.Assumptions] [github_com.emirpasic.gods.maps.treemap.Assumptions] [TH : TreemapHyp GF]

/-- An absent key, read. -/
theorem conflictRow_read_absent (m : GoMap) (row : w64 → Option InstPair) (K : w64)
    (h : row K = none) :
    ownConflictRow (GF := GF) m row ⊢ ∃ (g : GMap w64 Loc), m ↦$ g ∗ ⌜g.lookup K = none⌝ ∗
      (m ↦$ g -∗ ownConflictRow m row) := by
  unfold ownConflictRow
  iintro ⟨%g, Hm, %Hdom, Hps⟩
  have hK : g.lookup K = none := by
    have := Hdom K; rw [h] at this; simpa using this
  iexists g
  iframe Hm
  isplitr
  · ipureintro; exact hK
  iintro Hm
  iexists g
  iframe Hm Hps
  ipureintro; exact Hdom

/-- A present key, read. -/
theorem conflictRow_read_present (m : GoMap) (row : w64 → Option InstPair) (K : w64)
    (p : InstPair) (h : row K = some p) :
    ownConflictRow (GF := GF) m row ⊢ ∃ (g : GMap w64 Loc) (l : Loc), m ↦$ g ∗ ⌜g.lookup K = some l⌝ ∗
      l ↦ epaxos.InstPair.mk p.last p.lastWrite ∗
      (m ↦$ g -∗ l ↦ epaxos.InstPair.mk p.last p.lastWrite -∗ ownConflictRow m row) := by
  unfold ownConflictRow
  iintro ⟨%g, Hm, %Hdom, Hps⟩
  have hK : (g.lookup K).isSome = true := by rw [Hdom, h]; rfl
  obtain ⟨l, hl⟩ : ∃ l, g.lookup K = some l := Option.isSome_iff_exists.mp hK
  icases BigSepM.bigSepM_lookup_acc hl $$ Hps with ⟨Hl, Hclose⟩
  iexists g, l
  iframe Hm
  isplitr
  · ipureintro; exact hl
  isplitl [Hl]
  · rw [h]; simp only [Option.map_some, Option.getD_some]; iexact Hl
  iintro Hm Hl
  iexists g
  iframe Hm
  isplitr
  · ipureintro; exact Hdom
  iapply Hclose
  rw [h]; simp only [Option.map_some, Option.getD_some]; iexact Hl

/-- `updateAttributes(cmds, seq, deps, replica, instance)`: reads the conflicts map, the
instances it points to (`InstanceSpace[q][d].Seq`, through any slot predicate `P` that lets it
read `Seq`: `SeqReadable`), `maxSeqPerKey`, `lastScan`/`lastPut` (fix S1); writes `deps` in
place. -/
theorem wp_updateAttributes (γ : EpNames) (i : Nat) (r rr : Loc) (L : List GoString) (p : FwPtrs)
    (σ : RState) (P : InstId → Loc → IProp GF) (hP : SeqReadable σ.inst P)
    (hconf : ConfWf σ) (hib : instBounds σ.inst)
    (cs : GoSlice) (cmds : List WCmd) (dq : DFrac) (seq : w32) (dsl : GoSlice) (deps : List w32)
    (hdeps : depsOk deps) (replica n : w32) :
    {{ pkgInit_epaxos (GF := GF) ∗ efld r go!"Replica" ↦□ rr ∗ fwRO γ rr i L p ∗ repInstsP r P ∗
        repConf r σ.conflicts ∗ repMsk r σ.maxSeqPerKey ∗
        repRowArr r go!"lastScan" σ.lastScan ∗ repRowArr r go!"lastPut" σ.lastPut ∗
        ownCmds cs cmds dq ∗ dsl ↦* deps }}
      (App (App (App (App (App (Val (r @!! go.GoType.PointerType epaxos.Replica.ty
        @!! go!"updateAttributes")) (Val #cs)) (Val #seq)) (Val #dsl)) (Val #replica)) (Val #n))
    {{ RET (PairV (PairV #(updateAttributes σ cmds seq deps).1 #dsl)
          #(updateAttributes σ cmds seq deps).2.2);
        repInstsP r P ∗ repConf r σ.conflicts ∗ repMsk r σ.maxSeqPerKey ∗
        repRowArr r go!"lastScan" σ.lastScan ∗ repRowArr r go!"lastPut" σ.lastPut ∗
        ownCmds cs cmds dq ∗ dsl ↦* (updateAttributes σ cmds seq deps).2.1 }} := by
  wp_start as ⟨#Hrr, #Hfro, Hins, Hconf, Hmsk, HlS, HlP, Hcs, Hdsl⟩
  ihave ⟨#HN, -, -, -, -, -, -, -, -, -, -, -, -, %HLn⟩ := fwRO_fields _ _ _ _ _ $$ Hfro
  have hL5 : L.length = nR := HLn.1
  icases ownCmds_open _ _ _ $$ Hcs with ⟨%vs, Hcs, %Hvslen, #Hcms⟩
  ihave %Hcslen := ownSlice_len _ _ _ $$ Hcs
  unfold repConf repMsk
  icases Hconf with ⟨%cfs, %cms, #Hcfs, #Hcms', %Hcmlen, Hrows⟩
  icases Hmsk with ⟨%mm, %gm, #Hmm, Hgm, %Hgmeq⟩
  rw [updateAttributes_eq]
  wp_auto
  ihave HO : (∃ k : Nat, "Hq" ∷ q_ptr ↦ W64 k ∗
      "Hseq" ∷ seq_ptr ↦ (uaAcc σ cmds seq deps k).1 ∗
      "Hdsl" ∷ dsl ↦* (uaAcc σ cmds seq deps k).2.1 ∗
      "Hch" ∷ changed_ptr ↦ (uaAcc σ cmds seq deps k).2.2 ∗
      "%Hk" ∷ ⌜k ≤ nR ∧ depsOk (uaAcc σ cmds seq deps k).2.1⌝ : IProp GF) $$ [q seq Hdsl changed]
  · iexists 0; iframe; ipureintro; exact ⟨Nat.zero_le _, hdeps⟩
  wp_for HO
  rw [hL5]
  wp_if_destruct
  · have hk : k < nR := by
      (try simp only [intoVal_eq_iff, decide_eq_true_eq] at Hif); unfold nR at *; word
    ihave HI : (∃ j : Nat, "Hi" ∷ i_ptr ↦ W64 j ∗
        "Hseq" ∷ seq_ptr ↦ (uaIn σ cmds seq deps k j).1 ∗
        "Hdsl" ∷ dsl ↦* (uaIn σ cmds seq deps k j).2.1 ∗
        "Hch" ∷ changed_ptr ↦ (uaIn σ cmds seq deps k j).2.2 ∗
        "%Hj" ∷ ⌜j ≤ cmds.length ∧ depsOk (uaIn σ cmds seq deps k j).2.1⌝ : IProp GF)
        $$ [«i» Hseq Hdsl Hch]
    · iexists 0; unfold uaIn; simp only [List.take_zero, List.foldl_nil]; iframe
      ipureintro; exact ⟨Nat.zero_le _, Hk.2⟩
    wp_for HI
    wp_if_destruct
    · -- an iteration: command `j`
      have hjl : j < cmds.length := by have := Hcslen.1; rw [← Hvslen]; word
      obtain ⟨c, hc⟩ : ∃ c, cmds[j]? = some c := ⟨cmds[j], List.getElem?_eq_getElem hjl⟩
      obtain ⟨v, hv⟩ : ∃ v, vs[j]? = some v :=
        ⟨vs[j]'(by omega), List.getElem?_eq_getElem (by omega)⟩
      ihave ⟨%c', %hc', #Hok⟩ := BigSepL.bigSepL_lookup hv $$ Hcms
      rw [hc] at hc'; cases hc'
      unfold cmdOk
      icases Hok with ⟨%Hokp, #Hokv⟩
      have hjj : (sint.Z (W64 (j : Int))).toNat = j := by have := Hcslen.1; word
      have hb : 0 ≤ sint.Z (W64 (j : Int)) ∧ sint.Z (W64 (j : Int)) < sint.Z cs.len :=
        ⟨by word, Hif⟩
      have hkk : (sint.Z (W64 (k : Int))).toNat = k := by unfold nR at *; word
      wp_join iprop(∃ acc' : w32 × List w32 × Bool, "Hseq" ∷ seq_ptr ↦ acc'.1 ∗
          "Hdsl" ∷ dsl ↦* acc'.2.1 ∗ "Hch" ∷ changed_ptr ↦ acc'.2.2 ∗ "Hins" ∷ repInstsP r P ∗
          "Hcs" ∷ cs ↦*{dq} vs ∗
          "Hrows" ∷ ([∗list] q ↦ m ∈ cms, ownConflictRow m (σ.conflicts q)) ∗
          "deps" ∷ deps_ptr ↦ dsl ∗ "Hq" ∷ q_ptr ↦ W64 (k : Int) ∗ "r" ∷ r_ptr ↦ r ∗
          "cmds" ∷ cmds_ptr ↦ cs ∗ "Hi" ∷ i_ptr ↦ W64 (j : Int) ∗
          "%Hacc" ∷ ⌜acc' = uaKey σ k (uaIn σ cmds seq deps k j) c ∧ depsOk acc'.2.1⌝)
          at next with [Hseq Hdsl Hch Hins Hcs Hrows deps Hq r cmds Hi]
          as ⟨%acc', Hseq, Hdsl, Hch, Hins, Hcs, Hrows, deps, Hq, r, cmds, Hi, %Hacc⟩
      · icases ownSlice_elem_acc (sint.Z (W64 (j : Int))) v cs dq vs hb.1 (by rw [hjj]; exact hv)
          $$ Hcs with ⟨Hv, Hcsc⟩
        simp only [hb, _root_.and_self, ↓reduceIte]
        ihave %Hvnn := typedPointsto_not_null _ _ _ $$ Hv
        iStructNamed Hv
        wp_auto
        ihave %Hcmlen' := ownSlice_len _ _ _ $$ Hcms'
        have h4 : 0 ≤ sint.Z (W64 (k : Int)) ∧ sint.Z (W64 (k : Int)) < sint.Z cfs.len := by
          have := Hcmlen'.1; rw [Hcmlen] at this; unfold nR at *; constructor <;> word
        obtain ⟨mq, Hmq⟩ : ∃ mq, cms[k]? = some mq :=
          ⟨cms[k]'(by omega), List.getElem?_eq_getElem (by omega)⟩
        simp only [h4, _root_.and_self, ↓reduceIte]
        wp_apply wp_load_slice_index cfs _ cms _ mq h4.1 $$ [$Hcms'] as -
        · ipureintro; rw [hkk]; exact Hmq
        icases (BigSepL.bigSepL_lookup_acc Hmq).1 $$ Hrows with ⟨Hrow, Hrclose⟩
        rw [Hokp.2]
        rcases hp : σ.conflicts k c.key with _ | pr
        · -- absent
          icases conflictRow_read_absent _ _ _ hp $$ Hrow with ⟨%g, Hm, %Hgl, Hrc2⟩
          wp_apply wp_map_lookup2 $$ [$Hm] as Hm
          rw [show (g !! c.key) = none from Hgl]
          cleanup_bool_decide
          simp only [Option.isSome_none, Bool.false_eq_true, _root_.decide_false]
          wp_auto
          ihave Hrow := Hrc2 $$ Hm
          ihave Hrows := Hrclose $$ %mq Hrow
          rw [list_set_lookup_self _ _ _ Hmq]
          ihave Hv : sliceIndexRef state.Command (sint.Z (W64 (j : Int))) cs ↦{dq} v $$ [Op K V]
          · iapply typedPointsto_combine _ _ _ Hvnn
            simp only [TypedPointsto.typedPointstoDef]
            rw [Hokp.2]
            iframe Op K V
          ihave Hcs := Hcsc $$ Hv
          rw [hjj, list_set_lookup_self _ _ _ hv]
          wp_join_done
          iexists uaIn σ cmds seq deps k j
          iframe; ipureintro; exact ⟨(uaKey_none _ _ _ _ hp).symm, Hj.2⟩
        · -- present
          icases conflictRow_read_present _ _ _ _ hp $$ Hrow with ⟨%g, %l, Hm, %Hgl, Hl, Hrc2⟩
          wp_apply wp_map_lookup2 $$ [$Hm] as Hm
          rw [show (g !! c.key) = some l from Hgl]
          ihave %Hlnn := typedPointsto_not_null _ _ _ $$ Hl
          iStructNamed Hl
          cleanup_bool_decide
          simp only [Option.isSome_some, _root_.decide_true, Option.getD_some]
          wp_auto
          simp only [hb, _root_.and_self, ↓reduceIte]
          wp_auto
          rw [Hokp.1]
          wp_join iprop(d_ptr ↦ (if c.op ≠ opGET then pr.last else pr.lastWrite) ∗
              structFieldRef epaxos.InstPair go!"last" l ↦ pr.last) with [d dpair last] as ⟨Hd, last⟩
          · rw [if_neg (by unfold opGET; simpa using Hif)]; iframe
          · rw [if_pos (by unfold opGET; simpa using Hif)]; iframe
          -- the pair and the command are no longer read
          ihave Hrow := Hrc2 $$ Hm [last lastWrite]
          · iapply typedPointsto_combine _ _ _ Hlnn
            simp only [TypedPointsto.typedPointstoDef]
            iframe last lastWrite
          ihave Hrows := Hrclose $$ %mq Hrow
          rw [list_set_lookup_self _ _ _ Hmq]
          ihave Hv : sliceIndexRef state.Command (sint.Z (W64 (j : Int))) cs ↦{dq} v $$ [Op K V]
          · iapply typedPointsto_combine _ _ _ Hvnn
            simp only [TypedPointsto.typedPointstoDef]
            rw [Hokp.1, Hokp.2]
            iframe Op K V
          ihave Hcs := Hcsc $$ Hv
          rw [hjj, list_set_lookup_self _ _ _ hv]
          -- `if d > deps[q]`
          ihave %Hdl := ownSlice_len _ _ _ $$ Hdsl
          have hcl : (uaIn σ cmds seq deps k j).2.1.length = nR := Hj.2.1
          have hkc : k < (uaIn σ cmds seq deps k j).2.1.length := by omega
          have hb3 : 0 ≤ sint.Z (W64 (k : Int)) ∧ sint.Z (W64 (k : Int)) < sint.Z dsl.len := by
            have := Hdl.1; rw [hcl] at this; unfold nR at *; constructor <;> word
          wp_join iprop(∃ acc' : w32 × List w32 × Bool, seq_ptr ↦ acc'.1 ∗ dsl ↦* acc'.2.1 ∗
              changed_ptr ↦ acc'.2.2 ∗ repInstsP r P ∗ deps_ptr ↦ dsl ∗ q_ptr ↦ W64 (k : Int) ∗
              r_ptr ↦ r ∗
              ⌜acc' = uaKey σ k (uaIn σ cmds seq deps k j) c ∧ depsOk acc'.2.1⌝) at (if: _ then _ else _)
              with [Hseq Hdsl Hch Hins Hd deps Hq r] as ⟨%acc', Hseq, Hdsl, Hch, Hins, deps, Hq, r, %Hacc⟩
          · simp only [hb3, _root_.and_self, ↓reduceIte]
            wp_apply wp_load_slice_index dsl _ _ _ ((uaIn σ cmds seq deps k j).2.1[k]'hkc) hb3.1
              $$ [$Hdsl] as Hdsl
            · ipureintro; rw [hkk]; exact List.getElem?_eq_getElem hkc
            rw [uaKey_some' _ _ _ _ _ hp, uaDS_eq _ _ _ _ hkc]
            wp_if_destruct
            · -- `d > deps[q]`
              have Hif' : sint.Z (uaIn σ cmds seq deps k j).2.1[k] <
                  sint.Z (if c.op ≠ opGET then pr.last else pr.lastWrite) := Hif
              have hcur := Hj.2.2 _ (List.getElem_mem hkc)
              have h0 : 0 ≤ sint.Z (if c.op ≠ opGET then pr.last else pr.lastWrite) := by
                rcases hcur with h | h <;> omega
              obtain ⟨w, hw, hwn⟩ := ua_target σ hconf hib k c pr hp h0
              rw [if_pos Hif']
              simp only [hb3, _root_.and_self, ↓reduceIte]
              wp_apply wp_store_slice_index $$ [$Hdsl] as Hdsl
              · ipureintro; exact ⟨hb3.1, by rw [hcl]; unfold nR at *; word⟩
              rw [hkk]
              icases repInstsP_acc r P ⟨k, toN (if c.op ≠ opGET then pr.last else pr.lastWrite)⟩ hk
                (by simp only; omega) $$ Hins with
                ⟨%iss, %rows, %row, %ptrs, %pt, #Hiss, #Hrows, %Hrow, Hptrs, %Hptr, HPx, Hclose⟩
              icases hP _ _ _ hw $$ HPx with ⟨%y, Hy, %Hys, Hyc⟩
              wp_auto
              ihave %Hrlen := ownSlice_len _ _ _ $$ Hrows
              ihave %Hplen := ownSlice_len _ _ _ $$ Hptrs
              have h1 : 0 ≤ sint.Z (W64 (k : Int)) ∧ sint.Z (W64 (k : Int)) < sint.Z iss.len := by
                have hl := (List.getElem?_eq_some_iff.mp Hrow).1
                have := Hrlen.1; unfold nR at *; constructor <;> word
              have hdz : (sint.Z (if ¬c.op = opGET then pr.last else pr.lastWrite)).toNat =
                  toN (if ¬c.op = opGET then pr.last else pr.lastWrite) := rfl
              have h2 : 0 ≤ sint.Z (W64 (sint.Z (if ¬c.op = opGET then pr.last else pr.lastWrite))) ∧
                  sint.Z (W64 (sint.Z (if ¬c.op = opGET then pr.last else pr.lastWrite))) <
                    sint.Z row.len := by
                have := Hptr.2; have := Hplen.1; simp only [toN] at *; unfold MAX_INSTANCE at *
                constructor <;> word
              have e2 : sint.Z (W64 (sint.Z (if ¬c.op = opGET then pr.last else pr.lastWrite))) =
                  sint.Z (if ¬c.op = opGET then pr.last else pr.lastWrite) := by word
              simp only [h1, _root_.and_self, ↓reduceIte]
              wp_apply wp_load_slice_index iss _ rows _ row h1.1 $$ [$Hrows] as -
              · ipureintro; rw [hkk]; exact Hrow
              simp only [h2, _root_.and_self, ↓reduceIte]
              wp_apply wp_load_slice_index row _ ptrs _ pt h2.1 $$ [$Hptrs] as Hptrs
              · ipureintro; rw [e2, hdz]; exact Hptr.1
              ihave %Hynn := typedPointsto_not_null _ _ _ $$ Hy
              iStructNamed Hy
              rw [Hys]
              have hds : ((σ.inst ⟨k, toN (if c.op ≠ opGET then pr.last else pr.lastWrite)⟩).map
                  (·.seq)).getD (W32 0) = w.seq := by rw [hw]; rfl
              rw [hds]
              have hpset : ptrs.set (toN (if c.op ≠ opGET then pr.last else pr.lastWrite)) pt = ptrs :=
                list_set_lookup_self _ _ _ Hptr.1
              have hdo' : depsOk ((uaIn σ cmds seq deps k j).2.1.set k
                  (if c.op ≠ opGET then pr.last else pr.lastWrite)) :=
                depsOk_set _ _ _ Hj.2 ⟨h0, hwn⟩
              wp_if_destruct
              · simp only [h1, _root_.and_self, ↓reduceIte]
                wp_apply wp_load_slice_index iss _ rows _ row h1.1 $$ [$Hrows] as -
                · ipureintro; rw [hkk]; exact Hrow
                simp only [h2, _root_.and_self, ↓reduceIte]
                wp_apply wp_load_slice_index row _ ptrs _ pt h2.1 $$ [$Hptrs] as Hptrs
                · ipureintro; rw [e2, hdz]; exact Hptr.1
                ihave Hy : pt ↦ y $$ [Cmds bal vbal Status Seq Deps lb Index Lowlink bfilter proposeTime id]
                · iapply typedPointsto_combine _ _ _ Hynn
                  simp only [TypedPointsto.typedPointstoDef]
                  rw [Hys]
                  iframe
                ihave HPx := Hyc $$ Hy
                ihave Hins := Hclose $$ %pt %(P ⟨k, toN (if c.op ≠ opGET then pr.last else pr.lastWrite)⟩) [Hptrs] HPx
                · rw [hpset]; iexact Hptrs
                rw [updP_self']
                wp_join_done
                iexists (w.seq + 1, (uaIn σ cmds seq deps k j).2.1.set k
                  (if c.op ≠ opGET then pr.last else pr.lastWrite), true)
                iframe
                ipureintro
                refine ⟨?_, hdo'⟩
                rw [if_pos Hif]
              · ihave Hy : pt ↦ y $$ [Cmds bal vbal Status Seq Deps lb Index Lowlink bfilter proposeTime id]
                · iapply typedPointsto_combine _ _ _ Hynn
                  simp only [TypedPointsto.typedPointstoDef]
                  rw [Hys]
                  iframe
                ihave HPx := Hyc $$ Hy
                ihave Hins := Hclose $$ %pt %(P ⟨k, toN (if c.op ≠ opGET then pr.last else pr.lastWrite)⟩) [Hptrs] HPx
                · rw [hpset]; iexact Hptrs
                rw [updP_self']
                wp_join_done
                iexists ((uaIn σ cmds seq deps k j).1, (uaIn σ cmds seq deps k j).2.1.set k
                  (if c.op ≠ opGET then pr.last else pr.lastWrite), true)
                iframe
                ipureintro
                refine ⟨?_, hdo'⟩
                rw [if_neg Hif]
              done
            · rw [if_neg Hif]
              wp_join_done
              iexists uaIn σ cmds seq deps k j
              iframe; ipureintro; exact ⟨rfl, Hj.2⟩
          wp_join_done
          iexists acc'
          iframe; ipureintro; exact Hacc
      -- the class step (fix S1): `d := -1`, or the row's last PUT (SCAN) / last SCAN (PUT)
      icases ownSlice_elem_acc (sint.Z (W64 (j : Int))) v cs dq vs hb.1 (by rw [hjj]; exact hv)
        $$ Hcs with ⟨Hv, Hcsc⟩
      simp only [hb, _root_.and_self, ↓reduceIte]
      ihave %Hvnn := typedPointsto_not_null _ _ _ $$ Hv
      iStructNamed Hv
      unfold repRowArr
      icases HlS with ⟨%slS, #HslS, HlSs⟩
      icases HlP with ⟨%slP, #HslP, HlPs⟩
      ihave %HlSlen := ownSlice_len _ _ _ $$ HlSs
      ihave %HlPlen := ownSlice_len _ _ _ $$ HlPs
      have hbS : 0 ≤ sint.Z (W64 (k : Int)) ∧ sint.Z (W64 (k : Int)) < sint.Z slS.len := by
        have := HlSlen.1; simp only [List.length_map, List.length_range] at this
        unfold nR at *; constructor <;> word
      have hbP : 0 ≤ sint.Z (W64 (k : Int)) ∧ sint.Z (W64 (k : Int)) < sint.Z slP.len := by
        have := HlPlen.1; simp only [List.length_map, List.length_range] at this
        unfold nR at *; constructor <;> word
      wp_auto
      rw [Hokp.1]
      wp_join iprop(d_ptr ↦ uaCls σ k c ∗ slS ↦* ((List.range nR).map σ.lastScan) ∗
          slP ↦* ((List.range nR).map σ.lastPut) ∗ r_ptr ↦ r ∗ q_ptr ↦ W64 (k : Int) ∗
          cmds_ptr ↦ cs ∗ i_ptr ↦ W64 (j : Int) ∗
          (sliceIndexRef state.Command (sint.Z (W64 (j : Int))) cs).[state.Command, go!"Op"] ↦{dq} c.op)
          with [d HlSs HlPs r Hq cmds Hi Op] as ⟨Hd, HlSs, HlPs, r, Hq, cmds, Hi, Op⟩
      · -- SCAN
        have hs : c.op = opSCAN := by unfold opSCAN; simpa using Hif
        simp only [hbP, _root_.and_self, ↓reduceIte]
        wp_apply wp_load_slice_index slP _ _ _ (σ.lastPut k) hbP.1 $$ [$HlPs] as HlPs
        · ipureintro; rw [hkk]; simp [hk]
        wp_join_done
        unfold uaCls; rw [if_pos hs]; iframe
      · have hs : ¬ c.op = opSCAN := by unfold opSCAN; simpa using Hif
        simp only [hb, _root_.and_self, ↓reduceIte]
        wp_auto
        wp_if_destruct
        · -- PUT
          have hp' : c.op = opPUT := by unfold opPUT; simpa using Hif
          simp only [hbS, _root_.and_self, ↓reduceIte]
          wp_apply wp_load_slice_index slS _ _ _ (σ.lastScan k) hbS.1 $$ [$HlSs] as HlSs
          · ipureintro; rw [hkk]; simp [hk]
          wp_join_done
          unfold uaCls; rw [if_neg hs, if_pos hp']; iframe
        · have hp' : ¬ c.op = opPUT := by unfold opPUT; simpa using Hif
          wp_join_done
          unfold uaCls; rw [if_neg hs, if_neg hp']; iframe
      -- the command is no longer read
      ihave Hv : sliceIndexRef state.Command (sint.Z (W64 (j : Int))) cs ↦{dq} v $$ [Op K V]
      · iapply typedPointsto_combine _ _ _ Hvnn
        simp only [TypedPointsto.typedPointstoDef]
        rw [Hokp.1, Hokp.2]
        iframe Op K V
      ihave Hcs := Hcsc $$ Hv
      rw [hjj, list_set_lookup_self _ _ _ hv]
      -- `if d > deps[q]`
      ihave %Hdl := ownSlice_len _ _ _ $$ Hdsl
      have hcl : acc'.2.1.length = nR := Hacc.2.1
      have hkc : k < acc'.2.1.length := by omega
      have hb3 : 0 ≤ sint.Z (W64 (k : Int)) ∧ sint.Z (W64 (k : Int)) < sint.Z dsl.len := by
        have := Hdl.1; rw [hcl] at this; unfold nR at *; constructor <;> word
      wp_join iprop(∃ acc2 : w32 × List w32 × Bool, seq_ptr ↦ acc2.1 ∗ dsl ↦* acc2.2.1 ∗
          changed_ptr ↦ acc2.2.2 ∗ repInstsP r P ∗ deps_ptr ↦ dsl ∗ q_ptr ↦ W64 (k : Int) ∗
          r_ptr ↦ r ∗
          ⌜acc2 = uaDS σ k acc' (uaCls σ k c) ∧ depsOk acc2.2.1⌝) at (if: _ then _ else _)
          with [Hseq Hdsl Hch Hins Hd deps Hq r] as ⟨%acc2, Hseq, Hdsl, Hch, Hins, deps, Hq, r, %Hacc2⟩
      · simp only [hb3, _root_.and_self, ↓reduceIte]
        wp_apply wp_load_slice_index dsl _ _ _ (acc'.2.1[k]'hkc) hb3.1
          $$ [$Hdsl] as Hdsl
        · ipureintro; rw [hkk]; exact List.getElem?_eq_getElem hkc
        rw [uaDS_eq _ _ _ _ hkc]
        wp_if_destruct
        · -- `d > deps[q]`
          have Hif' : sint.Z acc'.2.1[k] <
              sint.Z (uaCls σ k c) := Hif
          have hcur := Hacc.2.2 _ (List.getElem_mem hkc)
          have h0 : 0 ≤ sint.Z (uaCls σ k c) := by
            rcases hcur with h | h <;> omega
          obtain ⟨w, hw, hwn⟩ := ua_cls_target σ hconf hib k hk c h0
          rw [if_pos Hif']
          simp only [hb3, _root_.and_self, ↓reduceIte]
          wp_apply wp_store_slice_index $$ [$Hdsl] as Hdsl
          · ipureintro; exact ⟨hb3.1, by rw [hcl]; unfold nR at *; word⟩
          rw [hkk]
          icases repInstsP_acc r P ⟨k, toN (uaCls σ k c)⟩ hk
            (by simp only; omega) $$ Hins with
            ⟨%iss, %rows, %row, %ptrs, %pt, #Hiss, #Hrows, %Hrow, Hptrs, %Hptr, HPx, Hclose⟩
          icases hP _ _ _ hw $$ HPx with ⟨%y, Hy, %Hys, Hyc⟩
          wp_auto
          ihave %Hrlen := ownSlice_len _ _ _ $$ Hrows
          ihave %Hplen := ownSlice_len _ _ _ $$ Hptrs
          have h1 : 0 ≤ sint.Z (W64 (k : Int)) ∧ sint.Z (W64 (k : Int)) < sint.Z iss.len := by
            have hl := (List.getElem?_eq_some_iff.mp Hrow).1
            have := Hrlen.1; unfold nR at *; constructor <;> word
          have hdz : (sint.Z (uaCls σ k c)).toNat =
              toN (uaCls σ k c) := rfl
          have h2 : 0 ≤ sint.Z (W64 (sint.Z (uaCls σ k c))) ∧
              sint.Z (W64 (sint.Z (uaCls σ k c))) <
                sint.Z row.len := by
            have := Hptr.2; have := Hplen.1; simp only [toN] at *; unfold MAX_INSTANCE at *
            constructor <;> word
          have e2 : sint.Z (W64 (sint.Z (uaCls σ k c))) =
              sint.Z (uaCls σ k c) := by word
          simp only [h1, _root_.and_self, ↓reduceIte]
          wp_apply wp_load_slice_index iss _ rows _ row h1.1 $$ [$Hrows] as -
          · ipureintro; rw [hkk]; exact Hrow
          simp only [h2, _root_.and_self, ↓reduceIte]
          wp_apply wp_load_slice_index row _ ptrs _ pt h2.1 $$ [$Hptrs] as Hptrs
          · ipureintro; rw [e2, hdz]; exact Hptr.1
          ihave %Hynn := typedPointsto_not_null _ _ _ $$ Hy
          iStructNamed Hy
          rw [Hys]
          have hds : ((σ.inst ⟨k, toN (uaCls σ k c)⟩).map
              (·.seq)).getD (W32 0) = w.seq := by rw [hw]; rfl
          rw [hds]
          have hpset : ptrs.set (toN (uaCls σ k c)) pt = ptrs :=
            list_set_lookup_self _ _ _ Hptr.1
          have hdo' : depsOk (acc'.2.1.set k
              (uaCls σ k c)) :=
            depsOk_set _ _ _ Hacc.2 ⟨h0, hwn⟩
          wp_if_destruct
          · simp only [h1, _root_.and_self, ↓reduceIte]
            wp_apply wp_load_slice_index iss _ rows _ row h1.1 $$ [$Hrows] as -
            · ipureintro; rw [hkk]; exact Hrow
            simp only [h2, _root_.and_self, ↓reduceIte]
            wp_apply wp_load_slice_index row _ ptrs _ pt h2.1 $$ [$Hptrs] as Hptrs
            · ipureintro; rw [e2, hdz]; exact Hptr.1
            ihave Hy : pt ↦ y $$ [Cmds bal vbal Status Seq Deps lb Index Lowlink bfilter proposeTime id]
            · iapply typedPointsto_combine _ _ _ Hynn
              simp only [TypedPointsto.typedPointstoDef]
              rw [Hys]
              iframe
            ihave HPx := Hyc $$ Hy
            ihave Hins := Hclose $$ %pt %(P ⟨k, toN (uaCls σ k c)⟩) [Hptrs] HPx
            · rw [hpset]; iexact Hptrs
            rw [updP_self']
            wp_join_done
            iexists (w.seq + 1, acc'.2.1.set k
              (uaCls σ k c), true)
            iframe
            ipureintro
            refine ⟨?_, hdo'⟩
            rw [if_pos Hif]
          · ihave Hy : pt ↦ y $$ [Cmds bal vbal Status Seq Deps lb Index Lowlink bfilter proposeTime id]
            · iapply typedPointsto_combine _ _ _ Hynn
              simp only [TypedPointsto.typedPointstoDef]
              rw [Hys]
              iframe
            ihave HPx := Hyc $$ Hy
            ihave Hins := Hclose $$ %pt %(P ⟨k, toN (uaCls σ k c)⟩) [Hptrs] HPx
            · rw [hpset]; iexact Hptrs
            rw [updP_self']
            wp_join_done
            iexists (acc'.1, acc'.2.1.set k
              (uaCls σ k c), true)
            iframe
            ipureintro
            refine ⟨?_, hdo'⟩
            rw [if_neg Hif]
          done
        · rw [if_neg Hif]
          wp_join_done
          iexists acc'
          iframe; ipureintro; exact ⟨rfl, Hacc.2⟩
      obtain ⟨rfl, hdo⟩ := Hacc2
      wp_for_post
      ihave HlS : (∃ sl, efld r go!"lastScan" ↦□ sl ∗ sl ↦* ((List.range nR).map σ.lastScan))
        $$ [HlSs]
      · iexists slS; isplitr
        · iexact HslS
        · iexact HlSs
      ihave HlP : (∃ sl, efld r go!"lastPut" ↦□ sl ∗ sl ↦* ((List.range nR).map σ.lastPut))
        $$ [HlPs]
      · iexists slP; isplitr
        · iexact HslP
        · iexact HlPs
      iframe
      iexists j + 1
      have e : uaIn σ cmds seq deps k (j + 1) = uaDS σ k acc' (uaCls σ k c) := by
        rw [uaIn_succ _ _ _ _ _ _ _ hc, Hacc.1]; rfl
      rw [e, show W64 ((j + 1 : Nat) : Int) = W64 (j : Int) + W64 1 by word]
      iframe; ipureintro; exact ⟨by omega, hdo⟩
    · -- row `k` done
      have hjn : j = cmds.length := by
        have := Hcslen.1; have := Hj.1; rw [← Hvslen] at *; word
      have hd := Hj.2
      rw [hjn, uaIn_len] at hd
      rw [hjn, uaIn_len]
      wp_for_post
      iframe
      iexists k + 1
      rw [show W64 ((k + 1 : Nat) : Int) = W64 (k : Int) + W64 1 by word]
      iframe; ipureintro; exact ⟨by omega, hd⟩
  · -- the second loop
    have hkn : k = nR := by
      (try simp only [intoVal_eq_iff, decide_eq_true_eq] at Hif); unfold nR at *; word
    rw [hkn] at *
    ihave HJ : (∃ j : Nat, "Hi" ∷ i_ptr ↦ W64 j ∗
        "Hseq" ∷ seq_ptr ↦ ((cmds.take j).foldl (uaMsk σ) (uaAcc σ cmds seq deps nR)).1 ∗
        "Hch" ∷ changed_ptr ↦ ((cmds.take j).foldl (uaMsk σ) (uaAcc σ cmds seq deps nR)).2.2 ∗
        "%Hj" ∷ ⌜j ≤ cmds.length⌝ : IProp GF) $$ [«i» Hseq Hch]
    · iexists 0; simp only [List.take_zero, List.foldl_nil]; iframe
      ipureintro; exact Nat.zero_le _
    wp_for HJ
    wp_if_destruct
    · have hjl : j < cmds.length := by
        (try simp only [intoVal_eq_iff, decide_eq_true_eq] at Hif)
        have := Hcslen.1; rw [← Hvslen]; word
      obtain ⟨c, hc⟩ : ∃ c, cmds[j]? = some c := ⟨cmds[j], List.getElem?_eq_getElem hjl⟩
      obtain ⟨v, hv⟩ : ∃ v, vs[j]? = some v :=
        ⟨vs[j]'(by omega), List.getElem?_eq_getElem (by omega)⟩
      ihave ⟨%c', %hc', #Hok⟩ := BigSepL.bigSepL_lookup hv $$ Hcms
      rw [hc] at hc'; cases hc'
      unfold cmdOk
      icases Hok with ⟨%Hokp, #Hokv⟩
      have hjj : (sint.Z (W64 (j : Int))).toNat = j := by have := Hcslen.1; word
      have hb : 0 ≤ sint.Z (W64 (j : Int)) ∧ sint.Z (W64 (j : Int)) < sint.Z cs.len := by
        have := Hcslen.1; constructor <;> word
      icases ownSlice_elem_acc (sint.Z (W64 (j : Int))) v cs dq vs hb.1 (by rw [hjj]; exact hv)
        $$ Hcs with ⟨Hv, Hcsc⟩
      simp only [hb, _root_.and_self, ↓reduceIte]
      ihave %Hvnn := typedPointsto_not_null _ _ _ $$ Hv
      iStructNamed Hv
      wp_auto
      ihave Hv : sliceIndexRef state.Command (sint.Z (W64 (j : Int))) cs ↦{dq} v $$ [Op K V]
      · iapply typedPointsto_combine _ _ _ Hvnn
        simp only [TypedPointsto.typedPointstoDef]
        iframe Op K V
      ihave Hcs := Hcsc $$ Hv
      rw [hjj, list_set_lookup_self _ _ _ hv, Hokp.2]
      wp_apply wp_map_lookup2 $$ [$Hgm] as Hgm
      rw [show (gm !! c.key) = σ.maxSeqPerKey c.key from Hgmeq c.key]
      rcases hms : σ.maxSeqPerKey c.key with _ | ms
      · cleanup_bool_decide
        simp only [Option.isSome_none, Bool.false_eq_true, _root_.decide_false]
        wp_auto
        wp_for_post
        iframe
        iexists j + 1
        rw [take_succ_foldl _ _ _ _ _ hc,
          show W64 ((j + 1 : Nat) : Int) = W64 (j : Int) + W64 1 by word]
        have e : uaMsk σ ((cmds.take j).foldl (uaMsk σ) (uaAcc σ cmds seq deps nR)) c =
            (cmds.take j).foldl (uaMsk σ) (uaAcc σ cmds seq deps nR) := by
          rw [uaMsk_none _ _ _ hms]
        rw [e]
        iframe; ipureintro; omega
      · cleanup_bool_decide
        simp only [Option.isSome_some, _root_.decide_true, Option.getD_some]
        wp_auto
        wp_if_destruct
        · wp_for_post
          iframe
          iexists j + 1
          rw [take_succ_foldl _ _ _ _ _ hc,
            show W64 ((j + 1 : Nat) : Int) = W64 (j : Int) + W64 1 by word]
          have e : uaMsk σ ((cmds.take j).foldl (uaMsk σ) (uaAcc σ cmds seq deps nR)) c =
              (ms + 1, ((cmds.take j).foldl (uaMsk σ) (uaAcc σ cmds seq deps nR)).2.1, true) := by
            rw [uaMsk_some _ _ _ _ hms, if_pos Hif]
          rw [e]
          iframe; ipureintro; omega
        · wp_for_post
          iframe
          iexists j + 1
          rw [take_succ_foldl _ _ _ _ _ hc,
            show W64 ((j + 1 : Nat) : Int) = W64 (j : Int) + W64 1 by word]
          have e : uaMsk σ ((cmds.take j).foldl (uaMsk σ) (uaAcc σ cmds seq deps nR)) c =
              (cmds.take j).foldl (uaMsk σ) (uaAcc σ cmds seq deps nR) := by
            rw [uaMsk_some _ _ _ _ hms, if_neg Hif]
          rw [e]
          iframe; ipureintro; omega
    · have hjn : j = cmds.length := by
        (try simp only [intoVal_eq_iff, decide_eq_true_eq] at Hif)
        have := Hcslen.1; rw [← Hvslen] at *; word
      rw [hjn, List.take_length]
      iapply HΦ
      iframe
      rw [uaMsk_deps]
      iframe
      isplitr
      · iexists cfs; iframe Hcfs Hcms'; ipureintro; exact Hcmlen
      isplitr
      · iframe Hmm; ipureintro; exact Hgmeq
      iapply ownCmds_close _ _ _ vs; iframe Hcs Hcms; ipureintro; exact Hvslen

/-- `mergeAttributes(seq1, deps1, seq2, deps2)` on two distinct arrays (`deps1` written in
place). -/
theorem wp_mergeAttributes (γ : EpNames) (i : Nat) (r rr : Loc) (L : List GoString) (p : FwPtrs)
    (seq1 seq2 : w32) (d1 d2 : GoSlice) (deps1 deps2 : List w32) (dq : DFrac)
    (h1 : deps1.length = nR) (h2 : deps2.length = nR) :
    {{ pkgInit_epaxos (GF := GF) ∗ efld r go!"Replica" ↦□ rr ∗ fwRO γ rr i L p ∗ d1 ↦* deps1 ∗
        d2 ↦*{dq} deps2 }}
      (App (App (App (App (Val (r @!! go.GoType.PointerType epaxos.Replica.ty
        @!! go!"mergeAttributes")) (Val #seq1)) (Val #d1)) (Val #seq2)) (Val #d2))
    {{ RET (PairV (PairV #(mergeAttributes seq1 deps1 seq2 deps2).1 #d1)
          #(mergeAttributes seq1 deps1 seq2 deps2).2.2);
        d1 ↦* (mergeAttributes seq1 deps1 seq2 deps2).2.1 ∗ d2 ↦*{dq} deps2 }} := by
  wp_start as ⟨#Hrr, #Hfro, H1, H2⟩
  ihave ⟨#HN, -, -, -, -, -, -, -, -, -, -, -, -, %HLn⟩ := fwRO_fields _ _ _ _ _ $$ Hfro
  have hL5 : L.length = nR := HLn.1
  ihave %Hl1 := ownSlice_len _ _ _ $$ H1
  ihave %Hl2 := ownSlice_len _ _ _ $$ H2
  rw [mergeAttributes_eq]
  wp_auto
  wp_join iprop(seq1_ptr ↦ (if seq1 ≠ seq2 ∧ seq1.slt seq2 then seq2 else seq1) ∗
      equal_ptr ↦ (seq1 == seq2) ∗ seq2_ptr ↦ seq2) with [seq1 seq2 equal] as ⟨Hs1, He, Hs2⟩
  · rw [if_neg (by rw [not_and]; intro h; exact absurd Hif h), Hif, beq_self_eq_true]
    iframe
  · have Hne := Hif
    rw [show (seq1 == seq2) = false from beq_false_of_ne Hne]
    wp_if_destruct
    · rw [if_pos ⟨Hne, (slt_iff _ _).mpr Hif⟩]
      wp_join_done
    · rw [if_neg (by rw [not_and, slt_iff]; intro _; exact Hif)]
      wp_join_done
  ihave HI : (∃ k : Nat, "Hq" ∷ q_ptr ↦ W64 k ∗
      "H1" ∷ d1 ↦* ((List.range k).foldl (mstep deps2) (deps1, true)).1 ∗
      "Heq" ∷ equal_ptr ↦ ((seq1 == seq2) && ((List.range k).foldl (mstep deps2) (deps1, true)).2) ∗
      "%Hk" ∷ ⌜k ≤ nR⌝ : IProp GF) $$ [q H1 He]
  · iexists 0; iframe; simp only [List.range_zero, List.foldl_nil, Bool.and_true]; iframe
    ipureintro; exact Nat.zero_le _
  wp_for HI
  rw [hL5]
  wp_if_destruct
  · have hk : k < nR := by
      (try simp only [intoVal_eq_iff, decide_eq_true_eq] at Hif); unfold nR at *; word
    have hc1 : ((List.range k).foldl (mstep deps2) (deps1, true)).1.length = nR := by
      rw [mstep_len]; exact h1
    have hb1 : 0 ≤ sint.Z (W64 (k : Int)) ∧ sint.Z (W64 (k : Int)) < sint.Z d1.len := by
      have := Hl1.1; rw [h1] at this; unfold nR at *; constructor <;> word
    have hb2 : 0 ≤ sint.Z (W64 (k : Int)) ∧ sint.Z (W64 (k : Int)) < sint.Z d2.len := by
      have := Hl2.1; rw [h2] at this; unfold nR at *; constructor <;> word
    have hkk : (sint.Z (W64 (k : Int))).toNat = k := by unfold nR at *; word
    have hk1 : k < ((List.range k).foldl (mstep deps2) (deps1, true)).1.length := by omega
    have hk2 : k < deps2.length := by omega
    simp only [hb1, _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index d1 _ _ _ (((List.range k).foldl (mstep deps2) (deps1, true)).1[k]'hk1) hb1.1 $$ [$H1] as H1
    · ipureintro; rw [hkk]; exact List.getElem?_eq_getElem hk1
    simp only [hb2, _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index d2 _ deps2 _ (deps2[k]'hk2) hb2.1 $$ [$H2] as H2
    · ipureintro; rw [hkk]; exact List.getElem?_eq_getElem hk2
    wp_if_destruct
    · wp_for_post
      iframe
      iexists k + 1
      rw [mstep_range_succ, mstep_eq _ _ _ hk1 hk2 Hif,
        show W64 ((k + 1 : Nat) : Int) = W64 (k : Int) + W64 1 by word]
      iframe
      ipureintro; omega
    · simp only [hb2, _root_.and_self, ↓reduceIte]
      wp_apply wp_load_slice_index d2 _ deps2 _ (deps2[k]'hk2) hb2.1 $$ [$H2] as H2
      · ipureintro; rw [hkk]; exact List.getElem?_eq_getElem hk2
      simp only [hb1, _root_.and_self, ↓reduceIte]
      wp_apply wp_load_slice_index d1 _ _ _ (((List.range k).foldl (mstep deps2) (deps1, true)).1[k]'hk1) hb1.1 $$ [$H1] as H1
      · ipureintro; rw [hkk]; exact List.getElem?_eq_getElem hk1
      have Hne := Hif
      wp_if_destruct
      · simp only [hb2, _root_.and_self, ↓reduceIte]
        wp_apply wp_load_slice_index d2 _ deps2 _ (deps2[k]'hk2) hb2.1 $$ [$H2] as H2
        · ipureintro; rw [hkk]; exact List.getElem?_eq_getElem hk2
        simp only [hb1, _root_.and_self, ↓reduceIte]
        wp_apply wp_store_slice_index $$ [$H1] as H1
        · ipureintro; exact ⟨hb1.1, by omega⟩
        wp_for_post
        iframe
        iexists k + 1
        rw [mstep_range_succ, mstep_ne _ _ _ hk1 hk2 Hne, if_pos Hif, hkk,
          show W64 ((k + 1 : Nat) : Int) = W64 (k : Int) + W64 1 by word]
        simp only [Bool.and_false]
        iframe
        ipureintro; omega
      · wp_for_post
        iframe
        iexists k + 1
        rw [mstep_range_succ, mstep_ne _ _ _ hk1 hk2 Hne, if_neg Hif,
          show W64 ((k + 1 : Nat) : Int) = W64 (k : Int) + W64 1 by word]
        simp only [Bool.and_false]
        iframe
        ipureintro; omega
  · have hkn : k = nR := by
      (try simp only [intoVal_eq_iff, decide_eq_true_eq] at Hif); unfold nR at *; word
    rw [hkn]
    iapply HΦ; iframe

/-- `mergeAttributes(seq1, d, seq2, d)` on one array (`handlePreAcceptReply` after
`lb.deps = pareply.Deps`): nothing is written. -/
theorem wp_mergeAttributes_self (γ : EpNames) (i : Nat) (r rr : Loc) (L : List GoString)
    (p : FwPtrs) (seq1 seq2 : w32) (d : GoSlice) (deps : List w32) (dq : DFrac)
    (h1 : deps.length = nR) :
    {{ pkgInit_epaxos (GF := GF) ∗ efld r go!"Replica" ↦□ rr ∗ fwRO γ rr i L p ∗ d ↦*{dq} deps }}
      (App (App (App (App (Val (r @!! go.GoType.PointerType epaxos.Replica.ty
        @!! go!"mergeAttributes")) (Val #seq1)) (Val #d)) (Val #seq2)) (Val #d))
    {{ RET (PairV (PairV #(mergeAttributes seq1 deps seq2 deps).1 #d)
          #(mergeAttributes seq1 deps seq2 deps).2.2);
        d ↦*{dq} deps ∗ ⌜(mergeAttributes seq1 deps seq2 deps).2.1 = deps⌝ }} := by
  wp_start as ⟨#Hrr, #Hfro, H1⟩
  ihave ⟨#HN, -, -, -, -, -, -, -, -, -, -, -, -, %HLn⟩ := fwRO_fields _ _ _ _ _ $$ Hfro
  have hL5 : L.length = nR := HLn.1
  ihave %Hl1 := ownSlice_len _ _ _ $$ H1
  rw [mergeAttributes_eq, mstep_self]
  wp_auto
  wp_join iprop(seq1_ptr ↦ (if seq1 ≠ seq2 ∧ seq1.slt seq2 then seq2 else seq1) ∗
      equal_ptr ↦ (seq1 == seq2) ∗ seq2_ptr ↦ seq2) with [seq1 seq2 equal] as ⟨Hs1, He, Hs2⟩
  · rw [if_neg (by rw [not_and]; intro h; exact absurd Hif h), Hif, beq_self_eq_true]
    iframe
  · have Hne := Hif
    rw [show (seq1 == seq2) = false from beq_false_of_ne Hne]
    wp_if_destruct
    · rw [if_pos ⟨Hne, (slt_iff _ _).mpr Hif⟩]
      wp_join_done
    · rw [if_neg (by rw [not_and, slt_iff]; intro _; exact Hif)]
      wp_join_done
  ihave HI : (∃ k : Nat, "Hq" ∷ q_ptr ↦ W64 k ∗ "%Hk" ∷ ⌜k ≤ nR⌝ : IProp GF) $$ [q]
  · iexists 0; iframe; ipureintro; exact Nat.zero_le _
  wp_for HI
  rw [hL5]
  wp_if_destruct
  · have hk : k < nR := by
      (try simp only [intoVal_eq_iff, decide_eq_true_eq] at Hif); unfold nR at *; word
    have hb1 : 0 ≤ sint.Z (W64 (k : Int)) ∧ sint.Z (W64 (k : Int)) < sint.Z d.len := by
      have := Hl1.1; rw [h1] at this; unfold nR at *; constructor <;> word
    have hkk : (sint.Z (W64 (k : Int))).toNat = k := by unfold nR at *; word
    have hk1 : k < deps.length := by omega
    simp only [hb1, _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index d _ _ _ (deps[k]'hk1) hb1.1 $$ [$H1] as H1
    · ipureintro; rw [hkk]; exact List.getElem?_eq_getElem hk1
    simp only [hb1, _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index d _ _ _ (deps[k]'hk1) hb1.1 $$ [$H1] as H1
    · ipureintro; rw [hkk]; exact List.getElem?_eq_getElem hk1
    wp_for_post
    iframe
    iexists k + 1
    rw [show W64 ((k + 1 : Nat) : Int) = W64 (k : Int) + W64 1 by word]
    iframe
    ipureintro; omega
  · simp only [Bool.and_true]
    iapply HΦ; iframe

/-- `equal(deps1, deps2)`. -/
theorem wp_equal (d1 d2 : GoSlice) (deps1 deps2 : List w32) (dq1 dq2 : DFrac)
    (h : deps1.length ≤ deps2.length) :
    {{ pkgInit_epaxos (GF := GF) ∗ d1 ↦*{dq1} deps1 ∗ d2 ↦*{dq2} deps2 }}
      (App (App (Val (@! epaxos.equal)) (Val #d1)) (Val #d2))
    {{ RET #(depsEqual deps1 deps2); d1 ↦*{dq1} deps1 ∗ d2 ↦*{dq2} deps2 }} := by
  wp_start as ⟨H1, H2⟩
  ihave %Hl1 := ownSlice_len _ _ _ $$ H1
  ihave %Hl2 := ownSlice_len _ _ _ $$ H2
  wp_auto
  ihave HI : (∃ k : Nat, "Hi" ∷ i_ptr ↦ W64 k ∗
      "%Hk" ∷ ⌜k ≤ deps1.length ∧ ∀ j < k, deps1.getD j (W32 0) = deps2.getD j (W32 0)⌝ :
      IProp GF) $$ [«i»]
  · iexists 0; iframe «i»; ipureintro; exact ⟨Nat.zero_le _, fun j hj => absurd hj (Nat.not_lt_zero _)⟩
  wp_for HI
  wp_if_destruct
  · have hk : k < deps1.length := by have := Hl1.1; rw [this]; word
    have hk2 : k < deps2.length := by omega
    have hb : 0 ≤ sint.Z (W64 (k : Int)) ∧ sint.Z (W64 (k : Int)) < sint.Z d1.len := by
      constructor <;> word
    have hb2 : 0 ≤ sint.Z (W64 (k : Int)) ∧ sint.Z (W64 (k : Int)) < sint.Z d2.len := by
      have := Hl2.1; constructor <;> word
    have hkk : (sint.Z (W64 (k : Int))).toNat = k := by word
    simp only [hb, _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index d1 _ deps1 _ (deps1[k]) hb.1 $$ [$H1] as H1
    · ipureintro; rw [hkk]; exact List.getElem?_eq_getElem hk
    simp only [hb2, _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index d2 _ deps2 _ (deps2[k]'hk2) hb.1 $$ [$H2] as H2
    · ipureintro; rw [hkk]; exact List.getElem?_eq_getElem hk2
    wp_if_destruct
    · wp_for_post
      iframe
      iexists k + 1
      rw [show W64 ((k + 1 : Nat) : Int) = W64 (k : Int) + W64 1 by word]
      iframe
      ipureintro
      refine ⟨by omega, fun j hj => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · exact Hk.2 j hj
      · rw [getD_of_lt _ _ _ hk, getD_of_lt _ _ _ hk2, Hif]
    · wp_for_post
      rw [depsEqual_false_of _ _ k hk (by rw [getD_of_lt _ _ _ hk, getD_of_lt _ _ _ hk2]; exact Hif)]
      iapply HΦ; iframe
  · have hk : k = deps1.length := by have := Hl1.1; have := Hk.1; rw [Hl1.1] at this ⊢; word
    rw [depsEqual_true_of _ _ (fun j hj => Hk.2 j (by omega))]
    iapply HΦ; iframe

end heap

end Perennial.github_com.imdea_software.swiftpaxos_epaxos
