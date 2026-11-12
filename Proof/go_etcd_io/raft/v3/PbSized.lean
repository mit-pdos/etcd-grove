/-
**Entry objects at a content of bounded size** (out_size Scope §2.3, 2026-11-12).

`out_size` (`MsgOut.lean`) needs every entry object a `Ready` hands out to be at a content of bounded
size (`entSizeOk`). The locations of raft's log entries are existential inside `entsRO`, and `pbMsg`
has no agreement law, so a size fact kept elsewhere cannot be tied to them: the fact travels with
the locations.

- `entBytes`, `entSizeOk`: an entry content's measured bytes and their bound (moved from
  `MsgOut.lean`).
- `entRZ sz l e`: the frozen entry `l` holding `e`, at a content `c` (`entRoC l c`) that is
  `entSizeOk` when `sz` (persistent). `sz` is the node's flag (`LogState.sz`): `false` for a cluster
  with no bound on proposed data, where the conjunct is vacuous and `entRZ false l e ⊣⊢ entRO l e`.
- `entsPtsZ sz s dq es` (`entsROz` at `DFrac.discard`): `entsPts` with `entRZ sz` in place of
  `entRO`, and its slicing laws, mirroring `InvPbLog.lean`'s. (The Scope writes it with one list of
  contents, `∃ ls cs`; pointwise is the same, the conjuncts being persistent and pure.)
-/
module

public import Proof.go_etcd_io.raft.v3.PbContent

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section size
variable [GooseExts]

/-- **An entry's bytes**: its `Data` and its unknown fields. -/
def entBytes (e : EntryC) : Nat := (e.data.getD []).length + e.uf.length

/-- **An entry's content is of bounded size**. -/
def entSizeOk (e : EntryC) : Prop := entBytes e ≤ 2 ^ 31

end size

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **A frozen log entry at a content of bounded size when `sz`** (persistent). -/
def entRZ (sz : Bool) (l : Loc) (e : EntryM) : IProp GF :=
  iprop(∃ c : EntryC, entRoC l c ∗ ⌜c.model = e ∧ (sz = true → entSizeOk c)⌝)

instance entRZ_persistent (sz : Bool) (l : Loc) (e : EntryM) :
    Persistent (entRZ (GF := GF) sz l e) := by
  unfold entRZ; infer_instance

/-- **A `[]*pb.Entry` of entries at bounded contents when `sz`**: `entsPts` with `entRZ sz`. -/
def entsPtsZ (sz : Bool) (s : GoSlice) (dq : DFrac) (es : List EntryM) : IProp GF :=
  iprop(∃ (ls : List Loc), s ↦*{dq} ls ∗ [∗list] l;e ∈ ls;es, entRZ sz l e)

/-- A read-only `entsPtsZ` (persistent). -/
abbrev entsROz (sz : Bool) (s : GoSlice) (es : List EntryM) : IProp GF :=
  entsPtsZ sz s DFrac.discard es

instance entsROz_persistent (sz : Bool) (s : GoSlice) (es : List EntryM) :
    Persistent (entsROz (GF := GF) sz s es) := by
  unfold entsROz entsPtsZ; infer_instance

end defs

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-! ### One entry -/

theorem entRZ_entRO (sz : Bool) (l : Loc) (e : EntryM) : entRZ (GF := GF) sz l e ⊢ entRO l e := by
  unfold entRZ
  iintro ⟨%c, #Hc, %Hm⟩
  obtain ⟨rfl, -⟩ := Hm
  iapply entRoC_entRO $$ Hc

/-- With the flag off, a log entry is an `entRZ`. -/
theorem entRO_entRZ (l : Loc) (e : EntryM) : entRO (GF := GF) l e ⊢ entRZ false l e := by
  iintro #H
  icases entRO_entRoC l e $$ H with ⟨%c, #Hc, %Hm⟩
  unfold entRZ
  iexists c
  iframe Hc
  ipureintro
  exact ⟨Hm, fun h => absurd h (by simp)⟩

/-- An entry at a bounded content is an `entRZ` at any flag. -/
theorem entRoC_entRZ (sz : Bool) (l : Loc) (c : EntryC) (h : entSizeOk c) :
    entRoC (GF := GF) l c ⊢ entRZ sz l c.model := by
  iintro #H
  unfold entRZ
  iexists c
  iframe H
  ipureintro
  exact ⟨rfl, fun _ => h⟩

/-- `entRZ` at `true` is one at any flag. -/
theorem entRZ_true (sz : Bool) (l : Loc) (e : EntryM) :
    entRZ (GF := GF) true l e ⊢ entRZ sz l e := by
  unfold entRZ
  iintro ⟨%c, #Hc, %Hm⟩
  iexists c
  iframe Hc
  ipureintro
  exact ⟨Hm.1, fun _ => Hm.2 rfl⟩

/-! ### Lists of entries -/

theorem entsBigZ_length (sz : Bool) (ls : List Loc) (es : List EntryM) :
    ([∗list] l;e ∈ ls;es, entRZ (GF := GF) sz l e) ⊢ ⌜ls.length = es.length⌝ :=
  BigSepL2.bigSepL2_length

theorem entsBigZ_entsBig (sz : Bool) (ls : List Loc) (es : List EntryM) :
    ([∗list] l;e ∈ ls;es, entRZ (GF := GF) sz l e) ⊢ [∗list] l;e ∈ ls;es, entRO l e :=
  BigSepL2.bigSepL2_mono (fun _ _ => entRZ_entRO sz _ _)

theorem entsBig_entsBigZ (ls : List Loc) (es : List EntryM) :
    ([∗list] l;e ∈ ls;es, entRO (GF := GF) l e) ⊢ [∗list] l;e ∈ ls;es, entRZ false l e :=
  BigSepL2.bigSepL2_mono (fun _ _ => entRO_entRZ _ _)

theorem entsBigZ_true (sz : Bool) (ls : List Loc) (es : List EntryM) :
    ([∗list] l;e ∈ ls;es, entRZ (GF := GF) true l e) ⊢ [∗list] l;e ∈ ls;es, entRZ sz l e :=
  BigSepL2.bigSepL2_mono (fun _ _ => entRZ_true sz _ _)

theorem entsBigZ_nil (sz : Bool) :
    ⊢ ([∗list] l;e ∈ ([] : List Loc);([] : List EntryM), entRZ (GF := GF) sz l e) :=
  BigSepL2.bigSepL2_nil.2

theorem entsBigZ_app (sz : Bool) (ls1 ls2 : List Loc) (es1 es2 : List EntryM) :
    ([∗list] l;e ∈ ls1;es1, entRZ (GF := GF) sz l e) ∗ ([∗list] l;e ∈ ls2;es2, entRZ sz l e) ⊢
      [∗list] l;e ∈ ls1 ++ ls2;es1 ++ es2, entRZ sz l e := by
  iintro ⟨#H1, #H2⟩
  ihave %Hl := entsBigZ_length sz _ _ $$ H1
  iapply (BigSepL2.bigSepL2_app_same_length (.inl Hl)).2
  iframe H1 H2

theorem entsBigZ_take (sz : Bool) (n : Nat) (ls : List Loc) (es : List EntryM) :
    ([∗list] l;e ∈ ls;es, entRZ (GF := GF) sz l e) ⊢
      [∗list] l;e ∈ ls.take n;es.take n, entRZ sz l e := by
  iintro #H
  ihave %Hl := entsBigZ_length sz _ _ $$ H
  have Ht : (ls.take n).length = (es.take n).length := by simp [Hl]
  have Hd := (BigSepL2.bigSepL2_app_same_length (PROP := IProp GF)
    (Φ := fun _ l e => entRZ (GF := GF) sz l e) (l1a := ls.take n) (l1b := ls.drop n)
    (l2a := es.take n) (l2b := es.drop n) (.inl Ht)).1
  rw [List.take_append_drop, List.take_append_drop] at Hd
  ihave H' := Hd $$ H
  icases H' with ⟨H1, -⟩
  iexact H1

theorem entsBigZ_drop (sz : Bool) (n : Nat) (ls : List Loc) (es : List EntryM) :
    ([∗list] l;e ∈ ls;es, entRZ (GF := GF) sz l e) ⊢
      [∗list] l;e ∈ ls.drop n;es.drop n, entRZ sz l e := by
  iintro #H
  ihave %Hl := entsBigZ_length sz _ _ $$ H
  have Ht : (ls.take n).length = (es.take n).length := by simp [Hl]
  have Hd := (BigSepL2.bigSepL2_app_same_length (PROP := IProp GF)
    (Φ := fun _ l e => entRZ (GF := GF) sz l e) (l1a := ls.take n) (l1b := ls.drop n)
    (l2a := es.take n) (l2b := es.drop n) (.inl Ht)).1
  rw [List.take_append_drop, List.take_append_drop] at Hd
  ihave H' := Hd $$ H
  icases H' with ⟨-, H2⟩
  iexact H2

theorem entsBigZ_subslice (sz : Bool) (lo hi : Nat) (ls : List Loc) (es : List EntryM) :
    ([∗list] l;e ∈ ls;es, entRZ (GF := GF) sz l e) ⊢
      [∗list] l;e ∈ subslice lo hi ls;subslice lo hi es, entRZ sz l e := by
  iintro #H
  simp only [subslice]
  iapply entsBigZ_drop
  iapply entsBigZ_take
  iexact H

/-- The entry at a position of the slice. -/
theorem entsBigZ_lookup (sz : Bool) (ls : List Loc) (es : List EntryM) (i : Nat) (e : EntryM)
    (He : es[i]? = some e) :
    ([∗list] l;e ∈ ls;es, entRZ (GF := GF) sz l e) ⊢ ∃ l, ⌜ls[i]? = some l⌝ ∗ entRZ sz l e := by
  iintro #H
  ihave %Hl := entsBigZ_length sz _ _ $$ H
  have Hi : i < ls.length := by have := (List.getElem?_eq_some_iff.1 He).1; omega
  obtain ⟨l, Hl'⟩ : ∃ l, ls[i]? = some l := ⟨_, List.getElem?_eq_getElem Hi⟩
  iexists l
  isplitr
  · ipureintro; exact Hl'
  iapply (BigSepL2.bigSepL2_lookup Hl' He) $$ H

/-- The entry at a position of the slice, as a log entry. -/
theorem entsBigZ_lookup_RO (sz : Bool) (ls : List Loc) (es : List EntryM) (i : Nat) (e : EntryM)
    (He : es[i]? = some e) :
    ([∗list] l;e ∈ ls;es, entRZ (GF := GF) sz l e) ⊢ ∃ l, ⌜ls[i]? = some l⌝ ∗ entRO l e := by
  iintro #H
  icases entsBigZ_lookup sz ls es i e He $$ H with ⟨%l, %Hl, #Hz⟩
  iexists l
  isplitr
  · ipureintro; exact Hl
  iapply entRZ_entRO $$ Hz

/-! ### Slices -/

theorem entsPtsZ_entsPts (sz : Bool) (s : GoSlice) (dq : DFrac) (es : List EntryM) :
    entsPtsZ (GF := GF) sz s dq es ⊢ entsPts s dq es := by
  unfold entsPtsZ entsPts
  iintro ⟨%ls, Hs, #Hb⟩
  iexists ls
  iframe Hs
  iapply entsBigZ_entsBig $$ Hb

theorem entsPts_entsPtsZ (s : GoSlice) (dq : DFrac) (es : List EntryM) :
    entsPts (GF := GF) s dq es ⊢ entsPtsZ false s dq es := by
  unfold entsPtsZ entsPts
  iintro ⟨%ls, Hs, #Hb⟩
  iexists ls
  iframe Hs
  iapply entsBig_entsBigZ $$ Hb

theorem entsROz_entsRO (sz : Bool) (s : GoSlice) (es : List EntryM) :
    entsROz (GF := GF) sz s es ⊢ entsRO s es :=
  entsPtsZ_entsPts sz s DFrac.discard es

theorem entsRO_entsROz (s : GoSlice) (es : List EntryM) :
    entsRO (GF := GF) s es ⊢ entsROz false s es :=
  entsPts_entsPtsZ s DFrac.discard es

theorem entsPtsZ_true (sz : Bool) (s : GoSlice) (dq : DFrac) (es : List EntryM) :
    entsPtsZ (GF := GF) true s dq es ⊢ entsPtsZ sz s dq es := by
  unfold entsPtsZ
  iintro ⟨%ls, Hs, #Hb⟩
  iexists ls
  iframe Hs
  iapply entsBigZ_true $$ Hb

/-- With the flag off, `entsPtsZ` is `entsPts`. -/
theorem entsPtsZ_false (s : GoSlice) (dq : DFrac) (es : List EntryM) :
    entsPtsZ (GF := GF) false s dq es ⊣⊢ entsPts s dq es :=
  ⟨entsPtsZ_entsPts false s dq es, entsPts_entsPtsZ s dq es⟩

/-- A batch given back or not, with the flag off. -/
theorem ite_entsPtsZ_false (c : Prop) [Decidable c] (s : GoSlice) (dq : DFrac) (es : List EntryM) :
    (if c then iprop(True) else entsPtsZ (GF := GF) false s dq es) ⊢
      if c then iprop(True) else entsPts s dq es := by
  split
  · exact .rfl
  · exact entsPtsZ_entsPts false s dq es

/-- The length of an entry slice. -/
theorem entsPtsZ_len (sz : Bool) (s : GoSlice) (dq : DFrac) (es : List EntryM) :
    entsPtsZ (GF := GF) sz s dq es ⊢ ⌜es.length = sint.nat s.len ∧ 0 ≤ sint.Z s.len⌝ := by
  iintro H
  iunfold entsPtsZ at H
  icases H with ⟨%ls, Hs, Hb⟩
  ihave %H1 := ownSlice_len $$ Hs
  ihave %H2 := entsBigZ_length sz _ _ $$ Hb
  ipureintro; omega

theorem entsPtsZ_nil (sz : Bool) (dq : DFrac) : ⊢ entsPtsZ (GF := GF) sz slice.nil dq [] := by
  iunfold entsPtsZ
  iexists []
  isplitr
  · iapply ownSlice_nil
  · iapply BigSepL2.bigSepL2_nil.2; iempintro

/-- An entry slice, frozen read-only. -/
theorem entsPtsZ_persist (sz : Bool) (s : GoSlice) (dq : DFrac) (es : List EntryM) :
    entsPtsZ (GF := GF) sz s dq es ⊢ |==> entsROz sz s es := by
  iintro H
  iunfold entsPtsZ at H
  icases H with ⟨%ls, Hs, #Hb⟩
  imod (ownSlice_dfractional (GF := GF) _ _).dfractional_persist _ $$ Hs with #Hs
  imodintro
  unfold entsROz entsPtsZ
  iexists ls
  iframe Hs Hb

end lemmas

end EtcdGrove
end Perennial
