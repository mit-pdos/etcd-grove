/-
Lemmas on the replicas' list in the lock invariant: splitting the big separating conjunctions,
the replicas' roles under the list's changes (a replica disconnected, removed, appended), and
collecting the `connected` flags the goroutines of `updateAll` give back.
-/
module

public import Dsverify.Proof.github_com.despreston.go_craq.Craq.Coord.UpdateAll

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net

namespace github_com.despreston.go_craq

attribute [local instance] GooseGlobalGS.gooseInvGS

/-! ## Pure facts -/

theorem addrAt_eq_of_map {rs rs' : List Rep} (h : rs.map Rep.addr = rs'.map Rep.addr) (j : Nat) :
    addrAt rs j = addrAt rs' j := by
  unfold addrAt
  rw [← List.getElem?_map, ← List.getElem?_map, h]

theorem addrAt_of_getElem {rs : List Rep} {j : Nat} {r : Rep} (h : rs[j]? = some r) :
    addrAt rs j = r.addr := by
  simp [addrAt, h]

/-- `nextOk` under a change of the list that keeps replica `j`'s position from the end and
whose successor, if connected, was a connected successor with the same address. -/
theorem nextOk_mono {rs rs' : List Rep} {j : Nat} {x : GoString}
    (hlast : j + 1 = rs'.length ↔ j + 1 = rs.length)
    (hnext : ∀ r', rs'[j + 1]? = some r' → r'.conn = true →
      ∃ r0, rs[j + 1]? = some r0 ∧ r0.conn = true ∧ r0.addr = r'.addr)
    (h : nextOk rs j x) : nextOk rs' j x := by
  refine ⟨fun hl => h.1 (hlast.mp hl), fun r' hr' hc => ?_⟩
  obtain ⟨r0, h0, hc0, ha⟩ := hnext r' hr' hc
  rw [h.2 r0 h0 hc0, ha]

theorem set_hnext {rs : List Rep} {k : Nat} {r r' : Rep} (h : rs[k]? = some r)
    (hr' : r'.addr = r.addr ∧ (r'.conn = true → r.conn = true)) (j : Nat) :
    ∀ r'', (rs.set k r')[j + 1]? = some r'' → r''.conn = true →
      ∃ r0, rs[j + 1]? = some r0 ∧ r0.conn = true ∧ r0.addr = r''.addr := by
  intro r'' h1 hc
  rw [List.getElem?_set] at h1
  split at h1
  · rename_i hk
    subst hk
    have hl := (List.getElem?_eq_some_iff.mp h).1
    simp only [hl, ↓reduceIte, Option.some.injEq] at h1
    subst h1
    exact ⟨r, h, hr'.2 hc, hr'.1.symm⟩
  · exact ⟨r'', h1, hc, rfl⟩

theorem map_eraseIdx' {β : Type} (f : Rep → β) (l : List Rep) (i : Nat) :
    (l.map f).eraseIdx i = (l.eraseIdx i).map f := by
  rw [List.eraseIdx_eq_take_drop_succ, List.eraseIdx_eq_take_drop_succ, List.map_append,
    List.map_take, List.map_drop]

theorem take_succ_of_getElem? (l : List Rep) (n : Nat) (x : Rep) (h : l[n]? = some x) :
    l.take (n + 1) = l.take n ++ [x] := by
  rw [List.take_succ, h]; rfl

theorem map_set_eq {β : Type} (f : Rep → β) {rs : List Rep} {k : Nat} {r r' : Rep}
    (h : rs[k]? = some r) (hf : f r' = f r) : (rs.set k r').map f = rs.map f := by
  apply List.ext_getElem?
  intro n
  rw [List.getElem?_map, List.getElem?_map, List.getElem?_set]
  split
  · rename_i hn; subst hn
    have hl := (List.getElem?_eq_some_iff.mp h).1
    simp only [hl, ↓reduceIte, Option.map_some, h, hf]
  · rfl

theorem nextOk_mono2 {rs rs' : List Rep} {j j' : Nat} {x : GoString}
    (hlast : j' + 1 = rs'.length ↔ j + 1 = rs.length)
    (hnext : ∀ r', rs'[j' + 1]? = some r' → r'.conn = true →
      ∃ r0, rs[j + 1]? = some r0 ∧ r0.conn = true ∧ r0.addr = r'.addr)
    (h : nextOk rs j x) : nextOk rs' j' x := by
  refine ⟨fun hl => h.1 (hlast.mp hl), fun r' hr' hc => ?_⟩
  obtain ⟨r0, h0, hc0, ha⟩ := hnext r' hr' hc
  rw [h.2 r0 h0 hc0, ha]

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [log.Assumptions] [LogHyp GF] [examples.craqnet.Assumptions] [store.Assumptions] [store.kv.Assumptions] [transport.Assumptions] [transport.netrpc.Assumptions] [node.Assumptions] [coordinator.Assumptions]
variable [net.rpc.Assumptions] [π : NetProtoGS]

/-- A replica that is not the last, told its successor in `rsL`. -/
def toldRole (cfg : Cfg GF) (rsL : List Rep) (j : Nat) (r : Rep) : IProp GF :=
  iprop(structFieldRef coordinator.node go!"connected" r.loc ↦ r.conn ∗
    if r.conn then roleHalf cfg.γ r.addr ((false, addrAt rsL (j + 1)) : Role) else iprop(True))

end defs

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [log.Assumptions] [LogHyp GF] [examples.craqnet.Assumptions] [store.Assumptions] [store.kv.Assumptions] [transport.Assumptions] [transport.netrpc.Assumptions] [node.Assumptions] [coordinator.Assumptions]
variable [net.rpc.Assumptions] [π : NetProtoGS]

/-! ## Big separating conjunctions over the replicas -/

theorem bigSepL_split_at (Φ : Nat → Rep → IProp GF) (l : List Rep) (i : Nat) (x : Rep)
    (h : l[i]? = some x) :
    ([∗list] j ↦ y ∈ l, Φ j y) ⊣⊢
      ([∗list] j ↦ y ∈ l.take i, Φ j y) ∗ Φ i x ∗ [∗list] k ↦ y ∈ l.drop (i + 1), Φ (i + 1 + k) y := by
  obtain ⟨hi, rfl⟩ := List.getElem?_eq_some_iff.mp h
  conv => lhs; rw [← List.take_append_drop i l]
  refine BigSepL.bigSepL_append.trans (sep_congr .rfl ?_)
  rw [List.drop_eq_getElem_cons hi]
  refine BigSepL.bigSepL_cons.trans (sep_congr ?_ ?_)
  · simp only [List.length_take, Nat.min_eq_left (Nat.le_of_lt hi)]
    rw [Nat.zero_add]; exact BIBase.BiEntails.rfl
  · simp only [List.length_take, Nat.min_eq_left (Nat.le_of_lt hi)]
    refine ⟨BigSepL.bigSepL_mono_of_forall fun {k y} => ?_, BigSepL.bigSepL_mono_of_forall fun {k y} => ?_⟩
    · rw [show k + 1 + i = i + 1 + k by omega]
    · rw [show k + 1 + i = i + 1 + k by omega]

theorem bigSepL_eraseIdx (Φ : Nat → Rep → IProp GF) (l : List Rep) (i : Nat) :
    ([∗list] j ↦ y ∈ l.eraseIdx i, Φ j y) ⊣⊢
      ([∗list] j ↦ y ∈ l.take i, Φ j y) ∗ [∗list] k ↦ y ∈ l.drop (i + 1), Φ (i + k) y := by
  rw [List.eraseIdx_eq_take_drop_succ]
  by_cases hi : i ≤ l.length
  · refine BigSepL.bigSepL_append.trans (sep_congr .rfl ?_)
    simp only [List.length_take, Nat.min_eq_left hi]
    refine ⟨BigSepL.bigSepL_mono_of_forall fun {k y} => ?_, BigSepL.bigSepL_mono_of_forall fun {k y} => ?_⟩
    · rw [Nat.add_comm k i]
    · rw [Nat.add_comm k i]
  · have h1 : l.drop (i + 1) = [] := List.drop_of_length_le (by omega)
    rw [h1, List.append_nil]
    exact (sep_emp (PROP := IProp GF)).symm.trans (sep_congr .rfl BigSepL.bigSepL_nil.symm)

theorem bigSepL_set (Φ : Nat → Rep → IProp GF) (l : List Rep) (i : Nat) (x y : Rep)
    (h : l[i]? = some x) :
    ([∗list] j ↦ z ∈ l, Φ j z) ⊢ Φ i x ∗ (Φ i y -∗ [∗list] j ↦ z ∈ l.set i y, Φ j z) := by
  iintro H
  ihave ⟨Hx, Hrest⟩ := (BigSepL.bigSepL_lookup_acc (Φ := Φ) h).1 $$ H
  iframe Hx
  iintro Hy
  iapply Hrest $$ Hy

/-- Collecting the goroutines' `connected` flags into a list. -/
theorem reps_exists (Φ : Nat → Rep → IProp GF) (rs : List Rep) :
    ([∗list] j ↦ r ∈ rs, ∃ b : Bool, Φ j { r with conn := b }) ⊢
      ∃ rs' : List Rep, ⌜rs'.map Rep.loc = rs.map Rep.loc ∧ rs'.map Rep.addr = rs.map Rep.addr⌝ ∗
        [∗list] j ↦ r ∈ rs', Φ j r := by
  induction rs generalizing Φ with
  | nil =>
    iintro -
    iexists []
    isplitr
    · ipureintro; simp
    iapply BigSepL.bigSepL_nil.2; iempintro
  | cons r rs ih =>
    iintro H
    ihave ⟨⟨%b, Hr⟩, Hrs⟩ := BigSepL.bigSepL_cons.1 $$ H
    ihave ⟨%rs', %Hm, Hrs'⟩ := ih (fun j r => Φ (j + 1) r) $$ Hrs
    iexists { r with conn := b } :: rs'
    isplitr
    · ipureintro; simp [Hm.1, Hm.2]
    iapply BigSepL.bigSepL_cons.2
    iframe

/-! ## The roles -/

theorem connRole_mono (cfg : Cfg GF) {rs rs' : List Rep} {j : Nat} (r : Rep)
    (hlast : j + 1 = rs'.length ↔ j + 1 = rs.length)
    (hnext : ∀ r', rs'[j + 1]? = some r' → r'.conn = true →
      ∃ r0, rs[j + 1]? = some r0 ∧ r0.conn = true ∧ r0.addr = r'.addr) :
    connRole cfg rs j r ⊢ connRole cfg rs' j r := by
  unfold connRole roleRes
  iintro ⟨Hc, Hr⟩
  iframe Hc
  cases r.conn
  · simp only [Bool.false_eq_true, ↓reduceIte]; itrivial
  · simp only [↓reduceIte]
    icases Hr with ⟨%x, Hr, %Hok⟩
    iexists x
    have hd : decide (j + 1 = rs'.length) = decide (j + 1 = rs.length) :=
      decide_eq_decide.mpr hlast
    rw [hd]
    iframe Hr
    ipureintro; exact nextOk_mono hlast hnext Hok

/-- A disconnected replica has no role resource. -/
theorem connRole_disc (cfg : Cfg GF) (rs : List Rep) (j : Nat) (r : Rep) (h : r.conn = false) :
    structFieldRef coordinator.node go!"connected" r.loc ↦ r.conn ⊢ connRole (hG := hG) cfg rs j r := by
  iintro Hc
  unfold connRole roleRes
  iframe Hc
  rw [h]; simp only [Bool.false_eq_true, ↓reduceIte]; itrivial

/-- The last replica's role: the active tail, no successor. -/
theorem connRole_last (cfg : Cfg GF) (rs : List Rep) (j : Nat) (r : Rep) (h : j + 1 = rs.length) :
    connRole (hG := hG) cfg rs j r ⊣⊢
      structFieldRef coordinator.node go!"connected" r.loc ↦ r.conn ∗
        if r.conn then roleHalf cfg.γ r.addr ((true, go!"") : Role) else iprop(True) := by
  unfold connRole roleRes
  have hd : decide (j + 1 = rs.length) = true := decide_eq_true h
  rw [hd]
  constructor
  · iintro ⟨Hc, Hr⟩
    iframe Hc
    cases r.conn
    · simp only [Bool.false_eq_true, ↓reduceIte]; itrivial
    · simp only [↓reduceIte]
      icases Hr with ⟨%x, Hr, %Hok⟩
      obtain rfl := Hok.1 h
      iexact Hr
  · iintro ⟨Hc, Hr⟩
    iframe Hc
    cases r.conn
    · simp only [Bool.false_eq_true, ↓reduceIte]; itrivial
    · simp only [↓reduceIte]
      iexists go!""
      iframe Hr
      ipureintro
      refine ⟨fun _ => rfl, fun r' hr' _ => ?_⟩
      have : rs.length ≤ j + 1 := by omega
      simp [List.getElem?_eq_none this] at hr'

/-- A replica that is not the last: not the tail, its recorded successor. -/
theorem connRole_mid (cfg : Cfg GF) (rs : List Rep) (j : Nat) (r : Rep) (h : j + 1 ≠ rs.length) :
    connRole (hG := hG) cfg rs j r ⊢
      structFieldRef coordinator.node go!"connected" r.loc ↦ r.conn ∗
        if r.conn then iprop(∃ x : GoString, roleHalf cfg.γ r.addr ((false, x) : Role) ∗
          ⌜nextOk rs j x⌝) else iprop(True) := by
  unfold connRole roleRes
  have hd : decide (j + 1 = rs.length) = false := decide_eq_false h
  rw [hd]

/-- What a goroutine of `updateAll` takes from a replica that is not the last. -/
theorem connRole_updIn (cfg : Cfg GF) (rs : List Rep) (j : Nat) (r : Rep) (h : j + 1 ≠ rs.length) :
    connRole (hG := hG) cfg rs j r ⊢ updIn cfg r := by
  iintro H
  ihave ⟨Hc, Hr⟩ := connRole_mid cfg rs j r h $$ H
  unfold updIn
  iframe Hc
  cases r.conn
  · simp only [Bool.false_eq_true, ↓reduceIte]; itrivial
  · simp only [↓reduceIte]
    icases Hr with ⟨%x, Hr, -⟩
    iexists x; iexact Hr

/-- A replica that is not the last with its successor's address told. -/
theorem connRole_of_told (cfg : Cfg GF) (rs : List Rep) (j : Nat) (r : Rep)
    (h : j + 1 ≠ rs.length) :
    structFieldRef coordinator.node go!"connected" r.loc ↦ r.conn ∗
      (if r.conn then roleHalf cfg.γ r.addr ((false, addrAt rs (j + 1)) : Role) else iprop(True)) ⊢
    connRole (hG := hG) cfg rs j r := by
  iintro ⟨Hc, Hr⟩
  unfold connRole roleRes
  have hd : decide (j + 1 = rs.length) = false := decide_eq_false h
  rw [hd]
  iframe Hc
  cases r.conn
  · simp only [Bool.false_eq_true, ↓reduceIte]; itrivial
  · simp only [↓reduceIte]
    iexists addrAt rs (j + 1)
    iframe Hr
    ipureintro
    exact ⟨fun hl => absurd hl h, fun r' hr' _ => addrAt_of_getElem hr'⟩

/-! ## The chain addresses -/

theorem joinRes_sub (cfg : Cfg GF) (rs rs' : List Rep) (a : GoString)
    (h : ∀ b, b ∈ rs'.map Rep.addr → b ∈ rs.map Rep.addr) :
    joinRes (hG := hG) cfg rs a ⊢ joinRes cfg rs' a := by
  unfold joinRes
  iintro (Ht | ⟨%Hn, Hr⟩)
  · ileft; iexact Ht
  · iright; iframe Hr; ipureintro; exact fun hm => Hn (h a hm)

theorem joins_sub (cfg : Cfg GF) (rs rs' : List Rep)
    (h : ∀ b, b ∈ rs'.map Rep.addr → b ∈ rs.map Rep.addr) :
    ([∗list] a ∈ cfg.chain, joinRes (hG := hG) cfg rs a) ⊢ [∗list] a ∈ cfg.chain, joinRes cfg rs' a :=
  BigSepL.bigSepL_mono_of_forall fun {_ a} => joinRes_sub cfg rs rs' a h

theorem nodeFacts_of_map (cfg : Cfg GF) (rs rs' : List Rep)
    (hl : rs'.map Rep.loc = rs.map Rep.loc) (ha : rs'.map Rep.addr = rs.map Rep.addr) :
    ([∗list] r ∈ rs, nodeFacts (hG := hG) cfg r.loc r.addr) ⊢
      [∗list] r ∈ rs', nodeFacts cfg r.loc r.addr := by
  have hp : rs'.map (fun r => (r.loc, r.addr)) = rs.map (fun r => (r.loc, r.addr)) := by
    apply List.ext_getElem
    · simpa using congrArg List.length hl
    · intro n h1 h2
      simp only [List.getElem_map]
      have e1 := congrArg (·[n]?) hl
      have e2 := congrArg (·[n]?) ha
      simp only [List.getElem?_map] at e1 e2
      rw [List.getElem?_eq_getElem (by simpa using h1), List.getElem?_eq_getElem (by simpa using h2)] at e1 e2
      simp only [Option.map_some, Option.some.injEq] at e1 e2
      rw [e1, e2]
  have h1 := BigSepL.bigSepL_map (PROP := IProp GF) (fun r : Rep => (r.loc, r.addr))
    (Φ := fun _ p => nodeFacts (hG := hG) cfg p.1 p.2) (l := rs)
  have h2 := BigSepL.bigSepL_map (PROP := IProp GF) (fun r : Rep => (r.loc, r.addr))
    (Φ := fun _ p => nodeFacts (hG := hG) cfg p.1 p.2) (l := rs')
  rw [hp] at h2
  rw [← h1, ← h2]

/-- Replica `k` taken out, and put back changed (same address, connected only if it was). -/
theorem reps_set (cfg : Cfg GF) (rs : List Rep) (k : Nat) (r : Rep) (h : rs[k]? = some r) :
    ([∗list] j ↦ x ∈ rs, connRole cfg rs j x) ⊢ connRole cfg rs k r ∗
      ∀ r' : Rep, ⌜r'.addr = r.addr ∧ (r'.conn = true → r.conn = true)⌝ -∗
        connRole cfg (rs.set k r') k r' -∗
        [∗list] j ↦ x ∈ rs.set k r', connRole cfg (rs.set k r') j x := by
  iintro H
  ihave ⟨Hl, Hk, Hr⟩ := (bigSepL_split_at _ rs k r h).1 $$ H
  iframe Hk
  iintro %r' %Hr' Hk'
  have hl := (List.getElem?_eq_some_iff.mp h).1
  have h' : (rs.set k r')[k]? = some r' := by simp [hl]
  have hlen : (rs.set k r').length = rs.length := List.length_set
  iapply (bigSepL_split_at _ (rs.set k r') k r' h').2
  rw [List.take_set_of_le (Nat.le_refl k), List.drop_set_of_lt (Nat.lt_succ_self k)]
  iframe Hk'
  isplitl [Hl]
  · iapply BigSepL.bigSepL_mono_of_forall _ $$ Hl
    intro j x
    exact connRole_mono cfg x (by rw [hlen]) (set_hnext h Hr' j)
  · iapply BigSepL.bigSepL_mono_of_forall _ $$ Hr
    intro j x
    exact connRole_mono cfg x (by rw [hlen]) (set_hnext h Hr' _)

/-- The input of `updateAll` over `pre ++ [last]`: each of `pre` not the tail. -/
theorem reps_inF (cfg : Cfg GF) (pre : List Rep) (last : Rep) :
    ([∗list] r ∈ pre, updIn (hG := hG) cfg r) ⊢
      [∗list] j ↦ r ∈ pre ++ [last], inF cfg (pre ++ [last]) j r := by
  iintro H
  iapply BigSepL.bigSepL_snoc.2
  isplitl [H]
  · iapply BigSepL.bigSepL_mono _ $$ H
    intro j r hj
    have hl : j < pre.length := (List.getElem?_eq_some_iff.mp hj).1
    unfold inF
    rw [if_neg (by simp; omega)]
  · unfold inF
    rw [if_pos (by simp)]
    itrivial

/-- After `updateAll` over `pre ++ [last]`, with `last`'s role (the active tail, while
connected): the replicas' roles, with the flags the goroutines left. -/
theorem reps_final (cfg : Cfg GF) (pre : List Rep) (last : Rep) :
    ([∗list] j ↦ r ∈ pre ++ [last], outF (hG := hG) cfg (pre ++ [last]) j r) ∗
      structFieldRef coordinator.node go!"connected" last.loc ↦ last.conn ∗
      (if last.conn then roleHalf cfg.γ last.addr ((true, go!"") : Role) else iprop(True)) ⊢
    ∃ pre' : List Rep, ⌜pre'.map Rep.loc = pre.map Rep.loc ∧ pre'.map Rep.addr = pre.map Rep.addr⌝ ∗
      [∗list] j ↦ r ∈ pre' ++ [last], connRole cfg (pre' ++ [last]) j r := by
  iintro ⟨Hout, Hc, Hr⟩
  ihave ⟨Hpre, -⟩ := BigSepL.bigSepL_snoc.1 $$ Hout
  ihave Hpre : [∗list] j ↦ r ∈ pre, ∃ b : Bool,
      toldRole cfg (pre ++ [last]) j { r with conn := b } $$ [Hpre]
  · iapply BigSepL.bigSepL_mono _ $$ Hpre
    intro j r hj
    have hl : j < pre.length := (List.getElem?_eq_some_iff.mp hj).1
    unfold outF
    rw [if_neg (by simp; omega)]
    unfold updOut toldRole
    iintro ⟨%b, Hc, Hr⟩
    iexists b
    iframe
  ihave ⟨%pre', %Hm, Hpre'⟩ := reps_exists (toldRole cfg (pre ++ [last])) pre $$ Hpre
  iexists pre'
  isplitr
  · ipureintro; exact Hm
  have hlen : pre'.length = pre.length := by simpa using congrArg List.length Hm.1
  have ha : (pre' ++ [last]).map Rep.addr = (pre ++ [last]).map Rep.addr := by simp [Hm.2]
  iapply BigSepL.bigSepL_snoc.2
  isplitl [Hpre']
  · iapply BigSepL.bigSepL_mono _ $$ Hpre'
    intro j r hj
    have hl : j < pre'.length := (List.getElem?_eq_some_iff.mp hj).1
    unfold toldRole
    rw [← addrAt_eq_of_map ha]
    exact connRole_of_told cfg (pre' ++ [last]) j r (by simp; omega)
  · iapply (connRole_last cfg (pre' ++ [last]) pre'.length last (by simp)).2
    iframe

theorem nodeFacts_take (cfg : Cfg GF) (rs : List Rep) (n : Nat) :
    ([∗list] r ∈ rs, nodeFacts (hG := hG) cfg r.loc r.addr) ⊢
      [∗list] r ∈ rs.take n, nodeFacts cfg r.loc r.addr := by
  iintro #H
  ihave H2 := (BigSepL.bigSepL_take_drop (Φ := fun _ (r : Rep) => nodeFacts (hG := hG) cfg r.loc r.addr)
    (l := rs) (n := n)).1 $$ H
  icases H2 with ⟨H1, -⟩
  iexact H1

theorem reps_length_le (cfg : Cfg GF) (rs : List Rep) (h : repsWf cfg rs) :
    rs.length ≤ cfg.chain.length := by
  have := List.Nodup.length_le_of_subset h.1 (fun x hx => by
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hx; exact h.2 r hr)
  simpa using this

theorem repsWf_sub (cfg : Cfg GF) (rs rs' : List Rep) (h : repsWf cfg rs)
    (hs : (rs'.map Rep.addr).Sublist (rs.map Rep.addr)) : repsWf cfg rs' := by
  refine ⟨h.1.sublist hs, fun r hr => ?_⟩
  have : r.addr ∈ rs.map Rep.addr := hs.subset (List.mem_map_of_mem hr)
  obtain ⟨r0, hr0, he⟩ := List.mem_map.mp this
  rw [← he]; exact h.2 r0 hr0

/-- Replica `k` put back changed (same address, connected only if it was), from the rest. -/
theorem reps_put (cfg : Cfg GF) (rs : List Rep) (k : Nat) (r : Rep) (h : rs[k]? = some r) (r' : Rep)
    (hr' : r'.addr = r.addr ∧ (r'.conn = true → r.conn = true)) :
    ([∗list] j ↦ x ∈ rs.take k, connRole cfg rs j x) ∗
      ([∗list] j ↦ x ∈ rs.drop (k + 1), connRole cfg rs (k + 1 + j) x) ∗
      connRole cfg (rs.set k r') k r' ⊢
    [∗list] j ↦ x ∈ rs.set k r', connRole cfg (rs.set k r') j x := by
  iintro ⟨Hl, Hr, Hk'⟩
  have hl := (List.getElem?_eq_some_iff.mp h).1
  have h' : (rs.set k r')[k]? = some r' := by simp [hl]
  have hlen : (rs.set k r').length = rs.length := List.length_set
  iapply (bigSepL_split_at _ (rs.set k r') k r' h').2
  rw [List.take_set_of_le (Nat.le_refl k), List.drop_set_of_lt (Nat.lt_succ_self k)]
  iframe Hk'
  isplitl [Hl]
  · iapply BigSepL.bigSepL_mono_of_forall _ $$ Hl
    intro j x
    exact connRole_mono cfg x (by rw [hlen]) (set_hnext h hr' j)
  · iapply BigSepL.bigSepL_mono_of_forall _ $$ Hr
    intro j x
    exact connRole_mono cfg x (by rw [hlen]) (set_hnext h hr' _)

theorem connRole_mono2 (cfg : Cfg GF) {rs rs' : List Rep} {j j' : Nat} (r : Rep)
    (hlast : j' + 1 = rs'.length ↔ j + 1 = rs.length)
    (hnext : ∀ r', rs'[j' + 1]? = some r' → r'.conn = true →
      ∃ r0, rs[j + 1]? = some r0 ∧ r0.conn = true ∧ r0.addr = r'.addr) :
    connRole cfg rs j r ⊢ connRole cfg rs' j' r := by
  unfold connRole roleRes
  iintro ⟨Hc, Hr⟩
  iframe Hc
  cases r.conn
  · simp only [Bool.false_eq_true, ↓reduceIte]; itrivial
  · simp only [↓reduceIte]
    icases Hr with ⟨%x, Hr, %Hok⟩
    iexists x
    have hd : decide (j' + 1 = rs'.length) = decide (j + 1 = rs.length) :=
      decide_eq_decide.mpr hlast
    rw [hd]
    iframe Hr
    ipureintro; exact nextOk_mono2 hlast hnext Hok

/-- A list with one replica removed and its neighbors `mid` (in place of the old ones) changed:
the roles of the unchanged replicas before (`pre`, a prefix of `rs`) and after (`post`, a suffix)
carry over. -/
theorem reps_assemble (cfg : Cfg GF) (rs pre mid post : List Rep)
    (hpre : pre = rs.take pre.length)
    (hpost : post = rs.drop (pre.length + mid.length + 1))
    (hmid : mid ≠ [])
    (hlen : pre.length + mid.length + post.length + 1 = rs.length)
    (hmid0 : pre ≠ [] → ∀ r', mid[0]? = some r' → r'.conn = true →
      ∃ r0, rs[pre.length]? = some r0 ∧ r0.conn = true ∧ r0.addr = r'.addr) :
    ([∗list] j ↦ x ∈ pre, connRole cfg rs j x) ∗
      ([∗list] j ↦ x ∈ mid, connRole cfg (pre ++ mid ++ post) (pre.length + j) x) ∗
      ([∗list] k ↦ x ∈ post, connRole cfg rs (pre.length + mid.length + 1 + k) x) ⊢
    [∗list] j ↦ x ∈ pre ++ mid ++ post, connRole cfg (pre ++ mid ++ post) j x := by
  iintro ⟨Hpre, Hmid, Hpost⟩
  have hm : 0 < mid.length := List.length_pos_iff.mpr hmid
  iapply BigSepL.bigSepL_append.2
  isplitl [Hpre Hmid]
  · iapply BigSepL.bigSepL_append.2
    isplitl [Hpre]
    · iapply BigSepL.bigSepL_mono _ $$ Hpre
      intro j x hj
      have hjl : j < pre.length := (List.getElem?_eq_some_iff.mp hj).1
      apply connRole_mono2 cfg x
      · simp only [List.length_append]; constructor <;> intro h <;> omega
      · intro r' hr' hc
        by_cases hj1 : j + 1 < pre.length
        · refine ⟨r', ?_, hc, rfl⟩
          rw [List.getElem?_append_left (by simp; omega), List.getElem?_append_left hj1] at hr'
          rw [hpre, List.getElem?_take_of_lt hj1] at hr'
          exact hr'
        · have : j + 1 = pre.length := by omega
          rw [List.getElem?_append_left (by simp; omega), List.getElem?_append_right (by omega), this,
            Nat.sub_self] at hr'
          rw [← this] at hmid0
          exact hmid0 (by intro h; simp [h] at hjl) r' hr' hc
    · iapply BigSepL.bigSepL_mono _ $$ Hmid
      intro j x _
      rw [Nat.add_comm]
  · iapply BigSepL.bigSepL_mono _ $$ Hpost
    intro k x hk
    have hkl : k < post.length := (List.getElem?_eq_some_iff.mp hk).1
    apply connRole_mono2 cfg x
    · simp only [List.length_append]; constructor <;> intro h <;> omega
    · intro r' hr' hc
      refine ⟨r', ?_, hc, rfl⟩
      rw [List.getElem?_append_right (by simp; omega)] at hr'
      simp only [List.length_append] at hr'
      rw [show k + (pre.length + mid.length) + 1 - (pre.length + mid.length) = k + 1 by omega,
        hpost, List.getElem?_drop] at hr'
      rw [show pre.length + mid.length + 1 + k + 1 = pre.length + mid.length + 1 + (k + 1) by omega]
      exact hr'

/-- The lock invariant after the replicas changed to `rsF` (non-empty, their addresses a sublist
of the old ones'). -/
theorem coordLock_new (cfg : Cfg GF) (c : Loc) (sl : GoSlice) (rs rsF : List Rep) (ver : w64)
    (hd tl : Loc) (hwf : repsWf cfg rs) (hsub : (rsF.map Rep.addr).Sublist (rs.map Rep.addr))
    (hne : rsF ≠ []) :
    structFieldRef coordinator.Coordinator go!"replicas" c ↦ sl ∗
      sl ↦* rsF.map Rep.loc ∗ ownSliceCap Loc sl (DFrac.own 1) ∗
      structFieldRef coordinator.Coordinator go!"version" c ↦ ver ∗ nextHalf cfg.γ ver ∗
      structFieldRef coordinator.Coordinator go!"head" c ↦ hd ∗
      structFieldRef coordinator.Coordinator go!"tail" c ↦ tl ∗
      □ ([∗list] r ∈ rsF, nodeFacts cfg r.loc r.addr) ∗
      ([∗list] i ↦ r ∈ rsF, connRole cfg rsF i r) ∗
      ([∗list] a ∈ cfg.chain, joinRes cfg rs a) ⊢
    coordLock (hG := hG) cfg c := by
  iintro ⟨H1, H2, H3, H4, H5, H6, H7, #H8, H9, H10⟩
  iapply coordLock_pack cfg c sl rsF ver hd tl (repsWf_sub cfg rs rsF hwf hsub)
  iframe H1 H2 H3 H4 H5 H6 H7 H9
  isplitr
  · iexact H8
  isplitl [H10]
  · iapply joins_sub cfg rs rsF _ $$ H10
    intro b hb; exact hsub.subset hb
  rw [if_neg hne]
  itrivial

theorem connRole_split (cfg : Cfg GF) (rs : List Rep) (j : Nat) (r : Rep) :
    connRole (hG := hG) cfg rs j r ⊢
      structFieldRef coordinator.node go!"connected" r.loc ↦ r.conn ∗ roleRes cfg rs j r := by
  unfold connRole; exact .rfl

/-- A replica's role as what `sendMeta` needs to send it metadata that keeps it the tail or not
the tail. -/
theorem roleRes_sendPre (cfg : Cfg GF) (rs : List Rep) (j : Nat) (r : Rep) (m : MetaV)
    (hm : m.isTail = decide (j + 1 = rs.length)) :
    roleRes (hG := hG) cfg rs j r ⊢
      ∃ x : GoString, sendPre cfg r.addr r.conn ((decide (j + 1 = rs.length), x) : Role) m := by
  unfold roleRes sendPre
  cases r.conn
  · iintro -; iexists go!""; simp only [Bool.false_eq_true, ↓reduceIte]; itrivial
  · simp only [↓reduceIte]
    iintro ⟨%x, Hr, -⟩
    iexists x
    iframe Hr
    unfold updDep
    rw [hm]
    cases decide (j + 1 = rs.length) <;>
      simp only [Bool.false_eq_true, false_and, Bool.true_eq_false, and_false, ↓reduceIte] <;> itrivial

/-- A replica connected and told its metadata (`metaOf rsL i`): its role in a list with the same
addresses. -/
theorem connRole_of_meta (cfg : Cfg GF) (rsL rsL' : List Rep) (i : Nat) (r : Rep)
    (hlen : rsL'.length = rsL.length) (ha : rsL'.map Rep.addr = rsL.map Rep.addr)
    (hc : r.conn = true) :
    structFieldRef coordinator.node go!"connected" r.loc ↦ r.conn ∗
      roleHalf cfg.γ r.addr (((metaOf rsL i).isTail, (metaOf rsL i).next) : Role) ⊢
    connRole (hG := hG) cfg rsL' i r := by
  iintro ⟨Hc, Hr⟩
  unfold connRole roleRes
  iframe Hc
  rw [hc]
  simp only [↓reduceIte]
  iexists (metaOf rsL i).next
  have ht : (metaOf rsL i).isTail = decide (i + 1 = rsL'.length) := by
    simp only [metaOf, hlen]; exact decide_eq_decide.mpr ⟨Eq.symm, Eq.symm⟩
  rw [← ht]
  iframe Hr
  ipureintro
  constructor
  · intro hl
    simp only [metaOf]
    rw [if_neg (by omega)]
  · intro r' hr' _
    have hl : i + 1 < rsL'.length := (List.getElem?_eq_some_iff.mp hr').1
    simp only [metaOf]
    rw [if_pos ⟨by omega, by omega⟩, ← addrAt_eq_of_map ha]
    exact addrAt_of_getElem hr'

end lemmas

end github_com.despreston.go_craq

end Perennial
