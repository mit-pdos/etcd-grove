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
- (out_size C2) `entsPtsC sz s dq cs`: the same at the list of contents `cs` (the storage contract's
  `Entries` post), and `entsCut maxSize cs`: one entry, or their protobuf sizes sum to at most
  `maxSize` (Go's `limitSize`).
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

/-- **The bound on an entry's bytes** (raft-entsize §1): what a sized entry's `Data` and unknown
fields total at most; the server's `maxData = 2^30` (`MaxRequestBytes`) is below it. -/
@[word_unfold] def entBytesMax : Nat := 2 ^ 31

/-- **An entry's content is of bounded size**. -/
def entSizeOk (e : EntryC) : Prop := entBytes e ≤ entBytesMax

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

/-- **A `[]*pb.Entry` at the contents `cs`** (out_size C2, the storage contract's list form): the
slice `s` at `dq` of frozen entry objects at the contents `cs`, each `entSizeOk` when `sz`. What the
storage contract's `Entries` returns (`isStorageP`), so that its cut (`entsCut`) can speak of the
contents' sizes. `entsPtsZ sz s dq (cs.map EntryC.model)` is the same ownership with the contents
hidden (`entsPtsC_entsPtsZ`, `entsPtsZ_entsPtsC`). -/
def entsPtsC (sz : Bool) (s : GoSlice) (dq : DFrac) (cs : List EntryC) : IProp GF :=
  iprop(∃ (ls : List Loc), s ↦*{dq} ls ∗ ([∗list] l;c ∈ ls;cs, entRoC l c) ∗
    ⌜sz = true → ∀ c ∈ cs, entSizeOk c⌝)

instance entsPtsC_persistent (sz : Bool) (s : GoSlice) (cs : List EntryC) :
    Persistent (entsPtsC (GF := GF) sz s DFrac.discard cs) := by
  unfold entsPtsC; infer_instance

end defs

section cut
variable [GooseExts]

/-- **A batch of entries cut at `maxSize`** (out_size C2; Go's `limitSize`, `util.go`): one entry,
or protobuf's sizes of the entries (`entrySize`, what `proto.Size` returns of each) sum to at most
`maxSize`. What `MemoryStorage.Entries` returns (its `limitSize`) and raft's `MsgApp` carries
(`raftLog.entries(next, maxMsgSize)`), whence the message's framed sum (`msgSizeOk`). -/
def entsCut (maxSize : w64) (cs : List EntryC) : Prop :=
  cs.length = 1 ∨ (cs.map entrySize).sum ≤ uint.nat maxSize

/-- **The largest `maxSize` a sized storage promises its cut at** (out_size C2): `Entries` cuts at
`maxSize` only up to it (`isStorageP`; Go's `limitSize` sums sizes in a `uint64`, which stays far
from wrapping only for a small `maxSize`), and raft's `MsgApp`s are cut at `MaxSizePerMsg`, which the
starters bound by it when the cluster bounds proposed data (etcd's `maxSizePerMsg = 1 MiB`,
`server/etcdserver/raft.go`). -/
@[word_unfold] def entsCutMax : Nat := 2 ^ 20

end cut

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

/-- An entry at a content bounded when `sz` is an `entRZ sz`. -/
theorem entRoC_entRZ_imp (sz : Bool) (l : Loc) (c : EntryC) (h : sz = true → entSizeOk c) :
    entRoC (GF := GF) l c ⊢ entRZ sz l c.model := by
  iintro #H
  unfold entRZ
  iexists c
  iframe H
  ipureintro
  exact ⟨rfl, h⟩

/-- `entRoC_entRZ_imp` at a model given up to equality. -/
theorem entRoC_entRZ_eq (sz : Bool) (l : Loc) (c : EntryC) (e : EntryM) (hm : c.model = e)
    (h : sz = true → entSizeOk c) : entRoC (GF := GF) l c ⊢ entRZ sz l e := by
  subst hm; exact entRoC_entRZ_imp sz l c h

/-- `entRZ` at `true` is one at any flag. -/
theorem entRZ_true (sz : Bool) (l : Loc) (e : EntryM) :
    entRZ (GF := GF) true l e ⊢ entRZ sz l e := by
  unfold entRZ
  iintro ⟨%c, #Hc, %Hm⟩
  iexists c
  iframe Hc
  ipureintro
  exact ⟨Hm.1, fun _ => Hm.2 rfl⟩

section alloc
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- (out_size C3) **A freshly allocated `*pb.Entry`**, as `entOwn_of_struct` takes it, frozen at the
content it was built with (no unknown fields, so its bytes are its `Data`'s): an `entRZ sz` when its
data is within the bound. -/
theorem entRZ_of_struct (sz : Bool) (l : Loc) (v : raftpb.Entry) (e : EntryM) (E : CoPset)
    (Hu : v.unknownFields' = slice.nil) (hd : sz = true → e.Data'.length ≤ entBytesMax) :
    (l ↦ v ∗ cellRO v.Term' e.Term' ∗ cellRO v.Index' e.Index' ∗ cellRO v.Type' e.Type' ∗
      v.Data' ↦*□ e.Data' : IProp GF) ⊢ |={E}=> entRZ sz l e := by
  iintro ⟨Hl, #cT, #cI, #cY, #Hd⟩
  ihave %Hnn := typedPointsto_not_null $$ Hl
  icases typedPointsto_split _ _ _ $$ Hl with Hl
  simp only [TypedPointsto.typedPointstoDef]
  icases Hl with ⟨state, Term, Index, Ty, Data, unknownFields, sizeCache, -⟩
  rw [Hu]
  ihave Hnil : (slice.nil ↦* ([] : List w8) : IProp GF) $$ []
  · iapply ownSlice_nil
  imod pbMsg_alloc raftpb.Entry l v.state' v.sizeCache' slice.nil [] E (ufWire_nil _)
    $$ [state sizeCache unknownFields Hnil] with #Hpb
  · iframe
  imod (typedPointsto_dfractional (GF := GF) _ _).dfractional_persist _ $$ Term with #HT
  imod (typedPointsto_dfractional (GF := GF) _ _).dfractional_persist _ $$ Index with #HI
  imod (typedPointsto_dfractional (GF := GF) _ _).dfractional_persist _ $$ Ty with #HY
  imod (typedPointsto_dfractional (GF := GF) _ _).dfractional_persist _ $$ Data with #HD
  ihave ⟨%oT, #oT', %hT⟩ := cellRO_optCell _ e.Term' $$ cT
  ihave ⟨%oI, #oI', %hI⟩ := cellRO_optCell _ e.Index' $$ cI
  ihave ⟨%oY, #oY', %hY⟩ := cellRO_optCell _ e.Type' $$ cY
  ihave ⟨%oD, #oD', %hD⟩ := ownSlice_bytesC _ e.Data' $$ Hd
  imodintro
  unfold entRZ
  iexists ⟨oT, oI, oY, oD, []⟩
  isplitl
  · unfold entRoC
    iexists v.Term', v.Index', v.Type', v.Data'
    iframe HT HI HY HD Hpb oT' oI' oY' oD'
    ipureintro; exact Hnn
  ipureintro
  refine ⟨?_, fun h => ?_⟩
  · obtain ⟨a, b, c, d⟩ := e
    simp only [EntryC.model] at *
    rw [hT, hI, hY, hD]
  · simp only [entSizeOk, entBytes, List.length_nil, Nat.add_zero]
    rw [hD]; exact hd h

end alloc

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

/-- (out_size C3) Read a sized batch's entries in today's form, its slice lent and given back. -/
theorem entsPtsZ_open (sz : Bool) (s : GoSlice) (dq : DFrac) (es : List EntryM) :
    entsPtsZ (GF := GF) sz s dq es ⊢
      ∃ ls : List Loc, s ↦*{dq} ls ∗ ([∗list] l;e ∈ ls;es, entRO l e) ∗
        (s ↦*{dq} ls -∗ entsPtsZ sz s dq es) := by
  unfold entsPtsZ
  iintro ⟨%ls, Hs, #Hb⟩
  iexists ls
  iframe Hs
  isplitr
  · iapply entsBigZ_entsBig $$ Hb
  iintro Hs
  iexists ls
  iframe Hs Hb

theorem entsPts_entsPtsZ (s : GoSlice) (dq : DFrac) (es : List EntryM) :
    entsPts (GF := GF) s dq es ⊢ entsPtsZ false s dq es := by
  unfold entsPtsZ entsPts
  iintro ⟨%ls, Hs, #Hb⟩
  iexists ls
  iframe Hs
  iapply entsBig_entsBigZ $$ Hb

/-- **TEMPORARY (out_size C3, branch only; gone before C3 lands).** Entries read in today's form at
contents of bounded size under any flag: the `sorry` is the size fact alone (`entSizeOk`), for the
entries of a received `MsgApp` that `handleAppendEntries` hands `maybeAppend` (P4: `msgInC`). Listed
in the handoff. -/
theorem entRZ_sized_TODO (sz : Bool) (l : Loc) (e : EntryM) :
    entRZ (GF := GF) false l e ⊢ entRZ sz l e := by
  unfold entRZ
  iintro ⟨%c, #Hc, %Hm⟩
  iexists c
  iframe Hc
  ipureintro
  exact ⟨Hm.1, fun _ => sorry⟩

/-- `entRZ_sized_TODO` over a slice (TEMPORARY, see there; also `appendEntry`'s clones, whose
sizes wait on the clone at contents). -/
theorem entsPtsZ_sized_TODO (sz : Bool) (s : GoSlice) (dq : DFrac) (es : List EntryM) :
    entsPts (GF := GF) s dq es ⊢ entsPtsZ sz s dq es := by
  iintro H
  ihave H := entsPts_entsPtsZ s dq es $$ H
  unfold entsPtsZ
  icases H with ⟨%ls, Hs, #Hb⟩
  iexists ls
  iframe Hs
  iapply (BigSepL2.bigSepL2_mono (fun _ _ => entRZ_sized_TODO sz _ _)) $$ Hb

/-- `entsPtsZ_sized_TODO` read-only (TEMPORARY). -/
theorem entsROz_sized_TODO (sz : Bool) (s : GoSlice) (es : List EntryM) :
    entsRO (GF := GF) s es ⊢ entsROz sz s es :=
  entsPtsZ_sized_TODO sz s DFrac.discard es

/-- An empty batch is sized under any flag. -/
theorem entsROz_of_nil (sz : Bool) (s : GoSlice) :
    entsRO (GF := GF) s [] ⊢ entsROz sz s [] := by
  unfold entsRO entsPts entsROz entsPtsZ
  iintro ⟨%ls, Hs, Hb⟩
  ihave %Hl := BigSepL2.bigSepL2_nil_inv_right $$ Hb
  subst Hl
  iexists []
  iframe Hs
  iapply BigSepL2.bigSepL2_nil.2; iempintro

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

/-! ### Lists of entries at contents (out_size C3: `limitSize`, `MemoryStorage.Entries`) -/

theorem entsBigC_length (ls : List Loc) (cs : List EntryC) :
    ([∗list] l;c ∈ ls;cs, entRoC (GF := GF) l c) ⊢ ⌜ls.length = cs.length⌝ :=
  BigSepL2.bigSepL2_length

theorem entsBigC_app (ls1 ls2 : List Loc) (cs1 cs2 : List EntryC) :
    ([∗list] l;c ∈ ls1;cs1, entRoC (GF := GF) l c) ∗ ([∗list] l;c ∈ ls2;cs2, entRoC l c) ⊢
      [∗list] l;c ∈ ls1 ++ ls2;cs1 ++ cs2, entRoC l c := by
  iintro ⟨#H1, #H2⟩
  ihave %Hl := entsBigC_length _ _ $$ H1
  iapply (BigSepL2.bigSepL2_app_same_length (.inl Hl)).2
  iframe H1 H2

theorem entsBigC_take_drop (n : Nat) (ls : List Loc) (cs : List EntryC) :
    ([∗list] l;c ∈ ls;cs, entRoC (GF := GF) l c) ⊢
      ([∗list] l;c ∈ ls.take n;cs.take n, entRoC l c) ∗
      ([∗list] l;c ∈ ls.drop n;cs.drop n, entRoC l c) := by
  iintro #H
  ihave %Hl := entsBigC_length _ _ $$ H
  have Ht : (ls.take n).length = (cs.take n).length := by simp [Hl]
  have Hd := (BigSepL2.bigSepL2_app_same_length (PROP := IProp GF)
    (Φ := fun _ l c => entRoC (GF := GF) l c) (l1a := ls.take n) (l1b := ls.drop n)
    (l2a := cs.take n) (l2b := cs.drop n) (.inl Ht)).1
  rw [List.take_append_drop, List.take_append_drop] at Hd
  iapply Hd $$ H

theorem entsBigC_take (n : Nat) (ls : List Loc) (cs : List EntryC) :
    ([∗list] l;c ∈ ls;cs, entRoC (GF := GF) l c) ⊢ [∗list] l;c ∈ ls.take n;cs.take n, entRoC l c := by
  iintro #H
  icases entsBigC_take_drop n ls cs $$ H with ⟨H1, -⟩
  iexact H1

theorem entsBigC_drop (n : Nat) (ls : List Loc) (cs : List EntryC) :
    ([∗list] l;c ∈ ls;cs, entRoC (GF := GF) l c) ⊢ [∗list] l;c ∈ ls.drop n;cs.drop n, entRoC l c := by
  iintro #H
  icases entsBigC_take_drop n ls cs $$ H with ⟨-, H2⟩
  iexact H2

theorem entsBigC_lookup (ls : List Loc) (cs : List EntryC) (i : Nat) (c : EntryC)
    (Hc : cs[i]? = some c) :
    ([∗list] l;c ∈ ls;cs, entRoC (GF := GF) l c) ⊢ ∃ l, ⌜ls[i]? = some l⌝ ∗ entRoC l c := by
  iintro #H
  ihave %Hl := entsBigC_length _ _ $$ H
  have Hi : i < ls.length := by have := (List.getElem?_eq_some_iff.1 Hc).1; omega
  obtain ⟨l, Hl'⟩ : ∃ l, ls[i]? = some l := ⟨_, List.getElem?_eq_getElem Hi⟩
  iexists l
  isplitr
  · ipureintro; exact Hl'
  iapply (BigSepL2.bigSepL2_lookup Hl' Hc) $$ H

theorem entsBigC_entsBigZ (sz : Bool) : ∀ (ls : List Loc) (cs : List EntryC),
    (sz = true → ∀ c ∈ cs, entSizeOk c) →
    ([∗list] l;c ∈ ls;cs, entRoC (GF := GF) l c) ⊢ [∗list] l;e ∈ ls;cs.map EntryC.model, entRZ sz l e
  | [], [], _ => by
    iintro -
    simp only [List.map_nil]
    iapply BigSepL2.bigSepL2_nil.2; iempintro
  | [], _ :: _, _ => false_elim
  | _ :: _, [], _ => false_elim
  | l :: ls, c :: cs, h => by
    iintro ⟨#H, #Hr⟩
    simp only [List.map_cons, BigSepL2.bigSepL2_cons]
    isplitl
    · unfold entRZ
      iexists c
      iframe H
      ipureintro
      exact ⟨rfl, fun hs => h hs c (by simp)⟩
    · iapply entsBigC_entsBigZ sz ls cs (fun hs c' hc' => h hs c' (by simp [hc'])) $$ Hr

theorem entsBigZ_entsBigC (sz : Bool) : ∀ (ls : List Loc) (es : List EntryM),
    ([∗list] l;e ∈ ls;es, entRZ (GF := GF) sz l e) ⊢
      ∃ cs : List EntryC, ([∗list] l;c ∈ ls;cs, entRoC l c) ∗
        ⌜cs.map EntryC.model = es ∧ (sz = true → ∀ c ∈ cs, entSizeOk c)⌝
  | [], [] => by
    iintro -; iexists []
    isplitl
    · iapply BigSepL2.bigSepL2_nil.2; iempintro
    · ipureintro; simp
  | [], _ :: _ => false_elim
  | _ :: _, [] => false_elim
  | l :: ls, e :: es => by
    iintro ⟨#H, #Hr⟩
    iunfold entRZ at H
    icases H with ⟨%c, #Hc, %hc⟩
    ihave ⟨%cs, #Hcs, %hcs⟩ := entsBigZ_entsBigC sz ls es $$ Hr
    iexists (c :: cs)
    simp only [BigSepL2.bigSepL2_cons, List.map_cons]
    iframe Hc Hcs
    ipureintro
    refine ⟨by rw [hc.1, hcs.1], fun hs c' hc' => ?_⟩
    rcases List.mem_cons.1 hc' with rfl | hc'
    · exact hc.2 hs
    · exact hcs.2 hs c' hc'

/-- (out_size C2) The list form hides its contents. -/
theorem entsPtsC_entsPtsZ (sz : Bool) (s : GoSlice) (dq : DFrac) (cs : List EntryC) :
    entsPtsC (GF := GF) sz s dq cs ⊢ entsPtsZ sz s dq (cs.map EntryC.model) := by
  unfold entsPtsC entsPtsZ
  iintro ⟨%ls, Hs, #Hb, %Hz⟩
  iexists ls
  iframe Hs
  iapply entsBigC_entsBigZ sz ls cs Hz $$ Hb

/-- (out_size C2) ... and recovers them. -/
theorem entsPtsZ_entsPtsC (sz : Bool) (s : GoSlice) (dq : DFrac) (es : List EntryM) :
    entsPtsZ (GF := GF) sz s dq es ⊢
      ∃ cs : List EntryC, entsPtsC sz s dq cs ∗ ⌜cs.map EntryC.model = es⌝ := by
  unfold entsPtsC entsPtsZ
  iintro ⟨%ls, Hs, #Hb⟩
  ihave ⟨%cs, #Hcs, %hcs⟩ := entsBigZ_entsBigC sz ls es $$ Hb
  iexists cs
  isplitl
  · iexists ls
    iframe Hs Hcs
    ipureintro; exact hcs.2
  · ipureintro; exact hcs.1

/-- (out_size C3) A model-level slice at some contents (unsized). -/
theorem entsPts_entsPtsC (s : GoSlice) (dq : DFrac) (es : List EntryM) :
    entsPts (GF := GF) s dq es ⊢
      ∃ cs : List EntryC, entsPtsC false s dq cs ∗ ⌜cs.map EntryC.model = es⌝ := by
  iintro H
  iapply entsPtsZ_entsPtsC
  iapply entsPts_entsPtsZ $$ H

/-- (out_size C3) The contents forgotten. -/
theorem entsPtsC_entsPts (sz : Bool) (s : GoSlice) (dq : DFrac) (cs : List EntryC)
    (es : List EntryM) (h : cs.map EntryC.model = es) :
    entsPtsC (GF := GF) sz s dq cs ⊢ entsPts s dq es := by
  iintro H
  subst h
  iapply entsPtsZ_entsPts
  iapply entsPtsC_entsPtsZ $$ H

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
