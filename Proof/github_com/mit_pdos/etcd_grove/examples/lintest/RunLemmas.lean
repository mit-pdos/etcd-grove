/-
Lean-first (no Rocq counterpart).

# lintest: what `Run` concludes from the clients' results (2026-10-14)

After `wg.Wait()`, `Run` holds every client's trace `hs[c]` and ghost value `ps[c]`
(`ClientsOk`: client `c`'s records match its trace, `ops` of them). With the invariant's view
(`InvOk`, the ghost map agreeing with every `ps[c]`), the traces' concatenation, which `Run`
passes to porcupine, is linearizable (`final_linearizable`, through `LogOk.linearizable` of
`LinTheory.lean`) and satisfies porcupine's premise (`final_histOk`).

Also the heap lemmas `Run` uses: a slice as its elements' points-tos (`ownSlice_elems`), the
clients' initial ghost values (`initMap`, `initMap_alloc`), and the ghost map's agreement
with all of them (`toks_lookup`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lintest.InvLemmas

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace lintest

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.anishathalye.porcupine github_com.anishathalye.porcupine.Theory

section pure
variable [ext : FfiSyntax] {σ : Type}

/-- The clients' traces `hs` and ghost values `ps` (client `c`'s at index `c`): client `c`'s
records match its trace (`ClientOk`), and there are `m` of them. -/
def ClientsOk (m : Nat) (hs : List (List Operation)) (ps : List (Nat × ClientV)) : Prop :=
  hs.length = ps.length ∧ ∀ (c : Nat) (h : List Operation) (p : Nat × ClientV),
    hs[c]? = some h → ps[c]? = some p →
      p.1 = c ∧ (∃ cid, ClientOk cid h p.2.1) ∧ p.2.1.length = m

theorem ClientsOk.nil (m : Nat) : ClientsOk m [] [] :=
  ⟨rfl, fun c h p hh _ => by simp at hh⟩

theorem ClientsOk.snoc {m : Nat} {hs : List (List Operation)} {ps : List (Nat × ClientV)}
    (H : ClientsOk m hs ps) (cid : w64) (h : List Operation) (Lc : List (OpV × w64)) (lr : w64)
    (hok : ClientOk cid h Lc) (hl : Lc.length = m) :
    ClientsOk m (hs ++ [h]) (ps ++ [(hs.length, (Lc, lr))]) := by
  obtain ⟨hlen, hc⟩ := H
  refine ⟨by simp [hlen], ?_⟩
  intro c h' p hh hp
  rcases Nat.lt_or_ge c hs.length with hlt | hge
  · rw [List.getElem?_append_left hlt] at hh
    rw [List.getElem?_append_left (by omega)] at hp
    exact hc c h' p hh hp
  · rw [List.getElem?_append_right hge] at hh
    rw [List.getElem?_append_right (by omega)] at hp
    rcases Nat.lt_or_ge (c - hs.length) 1 with h1 | h1
    · rw [show c - hs.length = 0 by omega] at hh
      rw [show c - ps.length = 0 by omega] at hp
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hh hp
      subst hh hp
      exact ⟨by simp; omega, ⟨cid, hok⟩, hl⟩
    · rw [List.getElem?_eq_none (by simp; omega)] at hh
      cases hh

/-- The records of the clients, as `LinTheory`'s `Lcs`. -/
def recsList (ps : List (Nat × ClientV)) : List (List (OpV × Int)) :=
  ps.map fun p => p.2.1.map fun q => (q.1, sint.Z q.2)

theorem histOf_flatten (hs : List (List Operation)) :
    histOf hs.flatten = (hs.map histOf).flatten := by
  unfold histOf
  rw [List.map_flatten]

theorem final_logOk {M : SeqModel σ OpV} {n m : Nat} {s : σ} {t : w64} {L : List (LinRec OpV)}
    {Ls : GMap Nat ClientV} {hs : List (List Operation)} {ps : List (Nat × ClientV)}
    (H : InvOk M n s t L Ls) (hc : ClientsOk m hs ps) (hn : hs.length = n)
    (hlook : ∀ p ∈ ps, Ls.lookup p.1 = some p.2) :
    LogOk M m (hs.map histOf) (recsList ps) L where
  len := by simp [recsList, hc.1]
  hlen := by
    intro h' hh'
    obtain ⟨h, hh, rfl⟩ := List.mem_map.1 hh'
    obtain ⟨c, hc'⟩ := List.getElem?_of_mem hh
    have hcl : c < ps.length := by
      rw [← hc.1]; exact (List.getElem?_eq_some_iff.1 hc').1
    obtain ⟨p, hp⟩ : ∃ p, ps[c]? = some p := ⟨_, List.getElem?_eq_getElem hcl⟩
    obtain ⟨-, ⟨cid, hok⟩, hl⟩ := hc.2 c h p hc' hp
    simp only [histOf, List.length_map]
    rw [hok.1, hl]
  lclen := by
    intro Lc hLc
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hLc
    obtain ⟨c, hc'⟩ := List.getElem?_of_mem hp
    have hcl : c < hs.length := by
      rw [hc.1]; exact (List.getElem?_eq_some_iff.1 hc').1
    obtain ⟨h, hh⟩ : ∃ h, hs[c]? = some h := ⟨_, List.getElem?_eq_getElem hcl⟩
    obtain ⟨-, -, hl⟩ := hc.2 c h p hh hc'
    simp only [List.length_map]
    exact hl
  recs := by
    intro c h' Lc' hh' hLc' j o q' ho hq'
    rw [List.getElem?_map] at hh'
    unfold recsList at hLc'
    rw [List.getElem?_map] at hLc'
    cases hh : hs[c]? with
    | none => rw [hh] at hh'; cases hh'
    | some h =>
      cases hp : ps[c]? with
      | none => rw [hp] at hLc'; cases hLc'
      | some p =>
        rw [hh] at hh'
        rw [hp] at hLc'
        simp only [Option.map_some, Option.some.injEq] at hh' hLc'
        subst hh' hLc'
        obtain ⟨-, ⟨cid, hok⟩, -⟩ := hc.2 c h p hh hp
        simp only [histOf, List.getElem?_map] at ho
        rw [List.getElem?_map] at hq'
        cases hoj : h[j]? with
        | none => rw [hoj] at ho; cases ho
        | some op =>
          cases hqj : p.2.1[j]? with
          | none => rw [hqj] at hq'; cases hq'
          | some q =>
            rw [hoj] at ho
            rw [hqj] at hq'
            simp only [Option.map_some, Option.some.injEq] at ho hq'
            subst ho hq'
            obtain ⟨-, hio, hcall, hret⟩ := hok.2 j op q hoj hqj
            exact ⟨hio, hcall, hret⟩
  filt := by
    intro c
    rw [H.filt c]
    rcases Nat.lt_or_ge c ps.length with hlt | hge
    · obtain ⟨p, hp⟩ : ∃ p, ps[c]? = some p := ⟨_, List.getElem?_eq_getElem hlt⟩
      have hcl : c < hs.length := by rw [hc.1]; exact hlt
      obtain ⟨h, hh⟩ : ∃ h, hs[c]? = some h := ⟨_, List.getElem?_eq_getElem hcl⟩
      obtain ⟨hpc, -, -⟩ := hc.2 c h p hh hp
      have hl := hlook p (List.mem_of_getElem? hp)
      rw [hpc] at hl
      simp only [recsOf, hl, Option.map_some, Option.getD_some, toRecs, recsList,
        List.getD_eq_getElem?_getD, List.getElem?_map, hp]
    · have hnone : Ls.lookup c = none := by
        cases hl : Ls.lookup c with
        | none => rfl
        | some v =>
          have := H.dom c v hl
          rw [← hn, hc.1] at this
          omega
      have hg : (recsList ps).getD c [] = [] := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp [recsList]; omega)]
        rfl
      simp only [recsOf, hnone, Option.map_none, Option.getD_none, hg, toRecs, List.map_nil]
  sorted := H.sorted
  runs := by rw [H.runs]; rfl

/-- **The traced history is linearizable.** -/
theorem final_linearizable {M : SeqModel σ OpV} {n m : Nat} {s : σ} {t : w64}
    {L : List (LinRec OpV)} {Ls : GMap Nat ClientV} {hs : List (List Operation)}
    {ps : List (Nat × ClientV)}
    (H : InvOk M n s t L Ls) (hc : ClientsOk m hs ps) (hn : hs.length = n)
    (hlook : ∀ p ∈ ps, Ls.lookup p.1 = some p.2) :
    Linearizable M (histOf hs.flatten) := by
  rw [histOf_flatten]
  exact (final_logOk H hc hn hlook).linearizable

/-- **The traced history satisfies porcupine's premise.** -/
theorem final_histOk {n m : Nat} {hs : List (List Operation)} {ps : List (Nat × ClientV)}
    (hc : ClientsOk m hs ps) (hn : hs.length = n) (hb : ((n * m : Nat) : Int) < 2 ^ 60) :
    HistOk hs.flatten := by
  have hl : ∀ h ∈ hs, h.length = m := by
    intro h hh
    obtain ⟨c, hc'⟩ := List.getElem?_of_mem hh
    have hcl : c < ps.length := by
      rw [← hc.1]; exact (List.getElem?_eq_some_iff.1 hc').1
    obtain ⟨p, hp⟩ : ∃ p, ps[c]? = some p := ⟨_, List.getElem?_eq_getElem hcl⟩
    obtain ⟨-, ⟨cid, hok⟩, hl⟩ := hc.2 c h p hc' hp
    rw [hok.1, hl]
  refine ⟨?_, ?_⟩
  · rw [flatten_length hs m hl, hn]; exact hb
  · intro o ho
    obtain ⟨h, hh, hoh⟩ := List.mem_flatten.1 ho
    obtain ⟨c, hc'⟩ := List.getElem?_of_mem hh
    have hcl : c < ps.length := by
      rw [← hc.1]; exact (List.getElem?_eq_some_iff.1 hc').1
    obtain ⟨p, hp⟩ : ∃ p, ps[c]? = some p := ⟨_, List.getElem?_eq_getElem hcl⟩
    obtain ⟨-, ⟨cid, hok⟩, -⟩ := hc.2 c h p hc' hp
    obtain ⟨j, hj⟩ := List.getElem?_of_mem hoh
    have hjl : j < p.2.1.length := by
      rw [← hok.1]; exact (List.getElem?_eq_some_iff.1 hj).1
    obtain ⟨q, hq⟩ : ∃ q, p.2.1[j]? = some q := ⟨_, List.getElem?_eq_getElem hjl⟩
    obtain ⟨-, -, h1, h2⟩ := hok.2 j o q hj hq
    exact Int.le_trans h1 h2

/-- The clients' initial ghost values: `v0` for clients `0, ..., n - 1`. -/
def initMap (n : Nat) (v0 : ClientV) : GMap Nat ClientV :=
  match n with
  | 0 => ∅
  | k + 1 => (initMap k v0).insert k v0

theorem initMap_lookup (n c : Nat) (v0 : ClientV) :
    (initMap n v0).lookup c = if c < n then some v0 else none := by
  induction n with
  | zero => simp [initMap]
  | succ n ih =>
    simp only [initMap]
    rw [GMap.lookup_insert_eq_iff, ih]
    by_cases h : n = c
    · subst h; simp
    · simp only [h, ↓reduceIte]
      by_cases hc : c < n
      · simp [hc, show c < n + 1 by omega]
      · simp [hc, show ¬ c < n + 1 by omega]

theorem InvOk.init (M : SeqModel σ OpV) (n : Nat) (t0 : w64) :
    InvOk M n M.init t0 [] (initMap n ([], t0)) where
  runs := rfl
  sorted := List.Pairwise.nil
  le_t e he := by cases he
  lr_le c v hv := by
    rw [initMap_lookup] at hv
    split at hv
    · cases hv; exact Int.le_refl _
    · cases hv
  dom c v hv := by
    rw [initMap_lookup] at hv
    split at hv
    · assumption
    · cases hv
  filt c := by
    simp only [List.filter_nil, recsOf, initMap_lookup]
    split <;> rfl

end pure

section heap
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

theorem bigSepL_replicate_range {A : Type} (n : Nat) (v : A) (Φ : Nat → A → IProp GF) :
    ([∗list] k ↦ x ∈ List.replicate n v, Φ k x) ⊢ [∗list] k ∈ List.range n, Φ k v := by
  induction n with
  | zero =>
    simp only [List.replicate_zero, List.range_zero]
    iintro _
    iapply (BigSepL.bigSepL_nil (PROP := IProp GF)).2
    iempintro
  | succ n ih =>
    rw [List.replicate_succ', List.range_succ]
    iintro H
    icases BigSepL.bigSepL_snoc.1 $$ H with ⟨H1, H2⟩
    iapply BigSepL.bigSepL_snoc.2
    isplitl [H1]
    · iapply ih $$ H1
    · rw [List.length_replicate]; iexact H2

/-- A slice of `n` copies of `v` as its elements' points-tos. -/
theorem ownSlice_replicate_elems {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V]
    (s : GoSlice) (n : Nat) (v : V) (dq : DFrac) :
    (s ↦*{dq} List.replicate n v : IProp GF) ⊢
      [∗list] c ∈ List.range n, typedPointsto (sliceIndexRef V ((c : Nat) : Int) s) v dq := by
  rw [ownSlice_unseal]; unfold ownSliceDef
  iintro (%H | ⟨Hsl, %Hl⟩)
  · have hn : n = 0 := by
      have := H.2; rw [List.replicate_eq_nil_iff] at this; exact this
    subst hn
    simp only [List.range_zero]
    iapply (BigSepL.bigSepL_nil (PROP := IProp GF)).2
    iempintro
  · icases typedPointsto_split _ _ _ $$ Hsl with Hsl
    simp only [TypedPointsto.typedPointstoDef]
    icases Hsl with ⟨%Hlen, Hsl⟩
    unfold arrayElems
    unfold sliceIndexRef
    iapply bigSepL_replicate_range n v
      (fun (k : Nat) (x : V) => typedPointsto (GF := GF) (arrayIndexRef V (k : Int) s.ptr) x dq)
    iexact Hsl

theorem initMap_alloc_from (γ : GName) (n : Nat) (v0 : ClientV) :
    ghostMapAuth (GF := GF) γ 1 (∅ : GMap Nat ClientV) ⊢
      |==> (ghostMapAuth γ 1 (initMap n v0) ∗ [∗list] c ∈ List.range n, clientTok γ c v0) := by
  induction n with
  | zero =>
    iintro H
    imodintro
    simp only [initMap, List.range_zero]
    iframe
    iapply (BigSepL.bigSepL_nil (PROP := IProp GF)).2
    iempintro
  | succ n ih =>
    iintro H
    imod ih $$ H with ⟨H, Hs⟩
    have hnone : (initMap n v0).lookup n = none := by
      rw [initMap_lookup]; simp
    imod ghost_map_insert n v0 hnone $$ H with ⟨H, Hn⟩
    imodintro
    simp only [initMap, List.range_succ]
    iframe H
    iapply BigSepL.bigSepL_snoc.2
    iframe

theorem initMap_alloc (n : Nat) (v0 : ClientV) :
    ⊢ |==> ∃ γ, (ghostMapAuth (GF := GF) γ 1 (initMap n v0) ∗
      [∗list] c ∈ List.range n, clientTok γ c v0) := by
  imod ghost_map_alloc_empty (GF := GF) (K := Nat) (V := ClientV) with ⟨%γ, H⟩
  imod initMap_alloc_from γ n v0 $$ H with ⟨H, Hs⟩
  imodintro
  iexists γ
  iframe

/-- What client `c` hands back to `Run` (through the wait group): its trace `hc` in its cell of
`histories` (`hsl`), its ghost value, its records matching its trace, `m` of them, and what
porcupine's `Step` needs of the trace. -/
def clientDone {σ : Type} (S : ModelSpec GF σ) (γ : GName) (hsl : GoSlice) (m : Nat) (c : Nat) :
    IProp GF :=
  iprop(∃ (sl : GoSlice) (hc : List Operation) (Lc : List (OpV × w64)) (lr cid : w64),
    typedPointsto (sliceIndexRef GoSlice ((c : Nat) : Int) hsl) sl (DFrac.own 1) ∗ sl ↦* hc ∗
    clientTok γ c (Lc, lr) ∗ ⌜ClientOk cid hc Lc ∧ Lc.length = m⌝ ∗ opsIoOk S hc)

/-- The ghost map agrees with the clients' ghost values. -/
theorem toks_lookup (γ : GName) (q : Qp) (Ls : GMap Nat ClientV) :
    ∀ ps : List (Nat × ClientV), ghostMapAuth (GF := GF) γ q Ls ⊢
      ([∗list] p ∈ ps, clientTok γ p.1 p.2) -∗ ⌜∀ p ∈ ps, Ls.lookup p.1 = some p.2⌝
  | [] => by
    iintro _ _
    ipureintro
    intro p hp
    cases hp
  | p :: ps => by
    iintro Ha Hs
    icases BigSepL.bigSepL_cons.1 $$ Hs with ⟨Hp, Hs⟩
    icombine Ha Hp gives %H1
    ihave %H2 := toks_lookup γ q Ls ps $$ Ha Hs
    ipureintro
    intro p' hp'
    rcases List.mem_cons.1 hp' with h | h
    · subst h; exact H1
    · exact H2 p' h

end heap

end lintest
end EtcdGrove
end Perennial
