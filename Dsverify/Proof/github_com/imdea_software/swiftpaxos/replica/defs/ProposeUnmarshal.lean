/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/defs/ProposeUnmarshal.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
`state.Operation/Key/Value/Command.Unmarshal` and `replica.defs.Propose.Unmarshal`
(`Proof/replica/ClientSpecs.lean`'s spec), over an `io.Reader` given by its `Read` spec.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.replica.ClientSpecs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.replica.defs.ProposeDec
public import Perennial.Proof.encoding.binary

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section proofs

variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [github_com.imdea_software.swiftpaxos.SwiftNetPkgState GF] [github_com.imdea_software.swiftpaxos.SwiftHyps GF]
variable [replica.defs.Assumptions] [state.Assumptions] [io.Assumptions]
  [errors.Assumptions] [encoding.binary.Assumptions]

set_option goose.wp.extras true

set_option hygiene false in
/-- Load the 8 bytes `bs[0..7]` of the slice `Hsl`. -/
local macro "ld8" : tactic => `(tactic| (
  wp_apply wp_load_slice_index _ (sint.Z (W64 0)) _ _ _ (by decide) $$ [Hsl] as Hsl
  · iframe Hsl; ipureintro; rfl
  try wp_auto
  wp_apply wp_load_slice_index _ (sint.Z (W64 1)) _ _ _ (by decide) $$ [Hsl] as Hsl
  · iframe Hsl; ipureintro; rfl
  try wp_auto
  wp_apply wp_load_slice_index _ (sint.Z (W64 2)) _ _ _ (by decide) $$ [Hsl] as Hsl
  · iframe Hsl; ipureintro; rfl
  try wp_auto
  wp_apply wp_load_slice_index _ (sint.Z (W64 3)) _ _ _ (by decide) $$ [Hsl] as Hsl
  · iframe Hsl; ipureintro; rfl
  try wp_auto
  wp_apply wp_load_slice_index _ (sint.Z (W64 4)) _ _ _ (by decide) $$ [Hsl] as Hsl
  · iframe Hsl; ipureintro; rfl
  try wp_auto
  wp_apply wp_load_slice_index _ (sint.Z (W64 5)) _ _ _ (by decide) $$ [Hsl] as Hsl
  · iframe Hsl; ipureintro; rfl
  try wp_auto
  wp_apply wp_load_slice_index _ (sint.Z (W64 6)) _ _ _ (by decide) $$ [Hsl] as Hsl
  · iframe Hsl; ipureintro; rfl
  try wp_auto
  wp_apply wp_load_slice_index _ (sint.Z (W64 7)) _ _ _ (by decide) $$ [Hsl] as Hsl
  · iframe Hsl; ipureintro; rfl))


theorem wp_Operation_Unmarshal (t : Loc) (o : state.Operation) (rd : GoInterface)
    (I : List w8 → IProp GF) (R : List w8) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.io ∗ bufio.readsOk rd I ∗ I R ∗ t ↦ o }}
      (App (Val (t @!! go.GoType.PointerType state.Operation.ty @!! go!"Unmarshal")) (Val #rd))
    {{ (err : GoInterface), RET #err; ∃ data : List w8, I (R ++ data) ∗
        ((⌜err = interface.nil⌝ ∗ ∃ op : state.Operation, ⌜data = [op]⌝ ∗ t ↦ op) ∨
          (⌜err ≠ interface.nil⌝ ∗ ∃ o' : state.Operation, t ↦ o')) }} := by
  wp_start as ⟨#Hrd, HI, Ht⟩
  wp_auto
  wp_apply (wp_slice_make2 (V := w8) (W64 1)) as %sl ⟨Hsl, -⟩
  · ipureintro; decide
  try wp_auto
  wp_apply bufio.wp_ReadFull rd I R sl _ $$ [$Hpkg $Hrd $HI $Hsl] as %n %err ⟨%data, %Hd, Hsl, HI, #He⟩
  obtain ⟨hn, hdl, herr⟩ := Hd
  try wp_auto
  rcases err with e | _
  · try wp_auto
    iapply HΦ
    iexists data
    iframe HI
    iright
    isplitr
    · ipureintro; intro h; cases h
    iexists o; iexact Ht
  · have h1 : data.length = 1 := by simpa using herr.1 rfl
    obtain ⟨d0, rfl⟩ : ∃ d0, data = [d0] := by
      match data, h1 with
      | [d0], _ => exact ⟨d0, rfl⟩
    isimp only [List.length_cons, List.length_nil, List.drop_replicate, List.append_nil,
      Nat.reduceAdd, Nat.sub_self, List.replicate_zero] at Hsl
    try wp_auto
    ihave %Hsll := ownSlice_len _ _ _ $$ Hsl
    rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by decide, by
      have h1 : sint.nat sl.len = 1 := by simpa using Hsll.1.symm
      have e1 : sint.nat sl.len = (sint.Z sl.len).toNat := rfl
      have h0 : sint.Z (W64 0) = 0 := rfl
      omega⟩)]
    wp_apply wp_load_slice_index _ _ _ _ d0 (by decide) $$ [Hsl] as Hsl
    · iframe Hsl; ipureintro; rfl
    try wp_auto
    iapply HΦ
    iexists [d0]
    iframe HI
    ileft
    isplitr
    · ipureintro; rfl
    iexists d0
    iframe Ht
    ipureintro; rfl

theorem wp_Key_Unmarshal (t : Loc) (o : state.Key) (rd : GoInterface)
    (I : List w8 → IProp GF) (R : List w8) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.io ∗ isPkgInit (PROP := IProp GF) pkg_id.encoding.binary ∗
        bufio.readsOk rd I ∗ I R ∗ t ↦ o }}
      (App (Val (t @!! go.GoType.PointerType state.Key.ty @!! go!"Unmarshal")) (Val #rd))
    {{ (err : GoInterface), RET #err; ∃ data : List w8, I (R ++ data) ∗
        ((⌜err = interface.nil⌝ ∗ ∃ k : state.Key, ⌜data = sp.le64 k⌝ ∗ t ↦ k) ∨
          (⌜err ≠ interface.nil⌝ ∗ ∃ o' : state.Key, t ↦ o')) }} := by
  wp_start as ⟨#Hrd, HI, Ht⟩
  try wp_auto
  wp_apply (wp_slice_make2 (V := w8) (W64 8)) as %sl ⟨Hsl, -⟩
  · ipureintro; decide
  try wp_auto
  wp_apply bufio.wp_ReadFull rd I R sl _ $$ [$Hpkg $Hrd $HI $Hsl] as %n %err ⟨%data, %Hd, Hsl, HI, #He⟩
  obtain ⟨hn, hdl, herr⟩ := Hd
  try wp_auto
  rcases err with e | _
  · try wp_auto
    iapply HΦ
    iexists data
    iframe HI
    iright
    isplitr
    · ipureintro; intro h; cases h
    iexists o; iexact Ht
  · have h8 : data.length = 8 := by simpa using herr.1 rfl
    try wp_auto
    have hd : List.drop data.length (List.replicate 8 (zero_val w8)) = [] := by
      rw [h8]; rfl
    isimp only [hd] at Hsl
    wp_apply encoding.binary.wp_LittleEndian_Uint64 sl data _ [] h8 $$ [$Hsl] as Hsl
    try wp_auto
    iapply HΦ
    iexists data
    iframe HI
    ileft
    isplitr
    · ipureintro; rfl
    iexists _
    iframe Ht
    ipureintro
    unfold sp.le64
    rw [leToU64_le _ h8]

/-- `(*Value).Unmarshal(rd)`: two length bytes, two ignored bytes, then that many bytes, a
fresh slice. -/
abbrev state.Value.Unmarshal.spec : Prop :=
  ∀ (t : Loc) (o : state.Value) (rd : GoInterface) (I : List w8 → IProp GF) (R : List w8),
    {{ isPkgInit (PROP := IProp GF) pkg_id.io ∗ isPkgInit (PROP := IProp GF) pkg_id.encoding.binary ∗
        bufio.readsOk rd I ∗ I R ∗ t ↦ o }}
      (App (Val (t @!! go.GoType.PointerType state.Value.ty @!! go!"Unmarshal")) (Val #rd))
    {{ (err : GoInterface), RET #err; ∃ data : List w8, I (R ++ data) ∗
        ((⌜err = interface.nil⌝ ∗ ∃ (l0 l1 x y : w8) (v : List w8) (vs : GoSlice),
            ⌜data = sp.decValue l0 l1 x y v ∧ l0.toNat + 256 * l1.toNat = v.length⌝ ∗
            t ↦ vs ∗ vs ↦* v) ∨
          (⌜err ≠ interface.nil⌝ ∗ ∃ o' : state.Value, t ↦ o')) }}

theorem u16_of_bytes (d0 d1 : w8) :
    uint.Z (W16 (uint.Z d0) ||| W16 (uint.Z d1) <<< W64 8) = d0.toNat + 256 * d1.toNat := by
  have e : ∀ d : w8, W16 (uint.Z d) = d.setWidth 16 := by
    intro d; simp only [W16, uint.Z]; rw [BitVec.ofInt_natCast]
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_setWidth]
  rw [e, e]
  have hb : (d0.setWidth 16 ||| d1.setWidth 16 <<< W64 8) = d1 ++ d0 := by
    ext i hi
    rw [BitVec.getElem_append]
    simp [W64, BitVec.getElem_shiftLeft]
    by_cases h : i < 8 <;> simp [h]
    rw [BitVec.getLsbD_of_ge d0 i (by omega), BitVec.getLsbD_eq_getElem (by omega)]
  rw [hb]; simp only [uint.Z, BitVec.toNat_append]
  have h0 := d0.isLt
  rw [← Nat.shiftLeft_add_eq_or_of_lt h0, Nat.shiftLeft_eq]
  have : (2:Nat) ^ 8 = 256 := rfl
  rw [this]; omega

theorem state.Value.Unmarshal.wp_proof : state.Value.Unmarshal.spec (GF := GF) := by
  intro t o rd I R
  wp_start as ⟨#Hrd, HI, Ht⟩
  try wp_auto
  wp_apply (wp_slice_make2 (V := w8) (W64 4)) as %sl ⟨Hsl, -⟩
  · ipureintro; decide
  try wp_auto
  wp_apply bufio.wp_ReadFull rd I R sl _ $$ [$Hpkg $Hrd $HI $Hsl] as %n %err ⟨%data, %Hd, Hsl, HI, #He⟩
  obtain ⟨hn, hdl, herr⟩ := Hd
  try wp_auto
  rcases err with e | _
  · try wp_auto
    iapply HΦ
    iexists data
    iframe HI
    iright
    isplitr
    · ipureintro; intro h; cases h
    iexists o; iexact Ht
  · have h4 : data.length = 4 := by simpa using herr.1 rfl
    obtain ⟨d0, d1, d2, d3, rfl⟩ : ∃ d0 d1 d2 d3 : w8, data = [d0, d1, d2, d3] := by
      match data, h4 with
      | [d0, d1, d2, d3], _ => exact ⟨d0, d1, d2, d3, rfl⟩
    isimp only [List.length_cons, List.length_nil, List.drop_replicate, List.append_nil,
      Nat.reduceAdd, Nat.sub_self, List.replicate_zero] at Hsl
    try wp_auto
    ihave #Hpkgb : isPkgInit (PROP := IProp GF) pkg_id.encoding.binary $$ []
    · iPkgInit
    ihave #Hinit := encoding.binary.isInit_access $$ Hpkgb
    icases Hinit with ⟨#Hle, -⟩
    ihave %Hl := ownSlice_len _ _ _ $$ Hsl
    wp_method_call
    wp_call
    try wp_auto
    wp_method_call
    wp_call
    try wp_auto
    have hlen4 : sint.Z sl.len = 4 := by
      have h1 : sint.nat sl.len = 4 := by simpa using Hl.1.symm
      have e1 : sint.nat sl.len = (sint.Z sl.len).toNat := rfl
      omega
    rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by decide, by rw [hlen4]; decide⟩)]
    wp_apply wp_load_slice_index _ _ _ _ d1 (by decide) $$ [Hsl] as Hsl
    · iframe Hsl; ipureintro; rfl
    try wp_auto
    rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by decide, by rw [hlen4]; decide⟩)]
    wp_apply wp_load_slice_index _ _ _ _ d0 (by decide) $$ [Hsl] as Hsl
    · iframe Hsl; ipureintro; rfl
    try wp_auto
    rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by decide, by rw [hlen4]; decide⟩)]
    wp_apply wp_load_slice_index _ _ _ _ d1 (by decide) $$ [Hsl] as Hsl
    · iframe Hsl; ipureintro; rfl
    try wp_auto
    wp_func_call
    wp_call
    try wp_auto
    -- `make([]byte, int(len))` (fix3: the length converted to `int`)
    have hL := u16_of_bytes d0 d1
    have hLz : sint.Z (W64 (uint.Z (W16 (uint.Z d0) ||| W16 (uint.Z d1) <<< W64 8))) =
        (d0.toNat + 256 * d1.toNat : Nat) := by
      rw [hL]; have := d0.isLt; have := d1.isLt
      simp only [sint.Z, W64]; rw [BitVec.toInt_ofInt]
      exact Int.bmod_eq_of_le (by omega) (by omega)
    wp_apply (wp_slice_make3 (V := w8) (W64 (uint.Z (W16 (uint.Z d0) ||| W16 (uint.Z d1) <<< W64 8)))
      (W64 (uint.Z (W16 (uint.Z d0) ||| W16 (uint.Z d1) <<< W64 8))) (by rw [hLz]; omega))
      as %sl2 ⟨Hsl2, -, -⟩
    try wp_auto
    wp_apply bufio.wp_ReadFull rd I _ sl2 _ $$ [$Hpkg $Hrd $HI $Hsl2]
      as %n2 %err2 ⟨%data2, %Hd2, Hsl2, HI, #He2⟩
    obtain ⟨hn2, hdl2, herr2⟩ := Hd2
    try wp_auto
    rcases err2 with e2 | _
    · try wp_auto
      iapply HΦ
      iexists _
      rw [List.append_assoc]
      iframe HI
      iright
      isplitr
      · ipureintro; intro h; cases h
      iexists o; iexact Ht
    · have hlen2 : data2.length = d0.toNat + 256 * d1.toNat := by
        have := herr2.1 rfl
        simp only [List.length_replicate] at this
        rw [this]
        have e : sint.nat (W64 (uint.Z (W16 (uint.Z d0) ||| W16 (uint.Z d1) <<< W64 8))) =
            (sint.Z (W64 (uint.Z (W16 (uint.Z d0) ||| W16 (uint.Z d1) <<< W64 8)))).toNat := rfl
        rw [e, hLz]; omega
      try wp_auto
      iapply HΦ
      iexists ([d0, d1, d2, d3] ++ data2)
      rw [List.append_assoc]
      iframe HI
      ileft
      isplitr
      · ipureintro; rfl
      iexists d0, d1, d2, d3, data2, sl2
      isplitr
      · ipureintro; exact ⟨rfl, hlen2.symm⟩
      have hd : (List.replicate (sint.nat (W64 (uint.Z (W16 (uint.Z d0) ||| W16 (uint.Z d1) <<< W64 8))))
          (zero_val w8)).drop data2.length = [] := by
        apply List.drop_eq_nil_of_le
        have e : sint.nat (W64 (uint.Z (W16 (uint.Z d0) ||| W16 (uint.Z d1) <<< W64 8))) =
            (sint.Z (W64 (uint.Z (W16 (uint.Z d0) ||| W16 (uint.Z d1) <<< W64 8)))).toNat := rfl
        simp only [List.length_replicate]; rw [e, hLz]; omega
      isimp only [hd, List.append_nil] at Hsl2
      iframe Ht Hsl2

theorem wp_Command_Unmarshal (wp_ValueUnm : state.Value.Unmarshal.spec (GF := GF))
    (t : Loc) (cv : state.Command) (rd : GoInterface) (I : List w8 → IProp GF) (R : List w8) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.io ∗ isPkgInit (PROP := IProp GF) pkg_id.encoding.binary ∗
        bufio.readsOk rd I ∗ I R ∗ t ↦ cv }}
      (App (Val (t @!! go.GoType.PointerType state.Command.ty @!! go!"Unmarshal")) (Val #rd))
    {{ (err : GoInterface), RET #err; ∃ data : List w8, I (R ++ data) ∗
        ((⌜err = interface.nil⌝ ∗ ∃ (op : w8) (k : w64) (l0 l1 x y : w8) (v : List w8) (vs : GoSlice),
            ⌜data = [op] ++ sp.le64 k ++ sp.decValue l0 l1 x y v ∧
              l0.toNat + 256 * l1.toNat = v.length⌝ ∗
            t ↦ state.Command.mk op k vs ∗ vs ↦* v) ∨
          (⌜err ≠ interface.nil⌝ ∗ ∃ c' : state.Command, t ↦ c')) }} := by
  wp_start as ⟨#Hrd, HI, Ht⟩
  ihave %Htn := typedPointsto_not_null $$ Ht
  iStructNamed Ht
  try wp_auto
  wp_apply wp_Operation_Unmarshal _ _ rd I R $$ [$Hpkg $Hrd $HI $Op] as %e1 ⟨%d1, HI, Hr1⟩
  icases Hr1 with (⟨%He1, %op, %Hd1, Op⟩ | ⟨%He1, %o', Op⟩)
  rotate_left
  · rcases e1 with e1 | _
    · try wp_auto
      iapply HΦ; iexists d1; iframe HI; iright
      isplitr
      · ipureintro; intro h; cases h
      iexists (state.Command.mk o' cv.K' cv.V')
      iapply typedPointsto_combine _ _ _ Htn
      simp only [TypedPointsto.typedPointstoDef]
      iframe
    · exact absurd rfl He1
  subst He1 Hd1
  try wp_auto
  wp_apply wp_Key_Unmarshal _ _ rd I (R ++ [op]) $$ [$Hpkg $Hpkg2 $Hrd $HI $K] as %e2 ⟨%d2, HI, Hr2⟩
  icases Hr2 with (⟨%He2, %k, %Hd2, K⟩ | ⟨%He2, %k', K⟩)
  rotate_left
  · rcases e2 with e2 | _
    · try wp_auto
      iapply HΦ; iexists [op] ++ d2
      rw [← List.append_assoc]
      iframe HI; iright
      isplitr
      · ipureintro; intro h; cases h
      iexists (state.Command.mk op k' cv.V')
      iapply typedPointsto_combine _ _ _ Htn
      simp only [TypedPointsto.typedPointstoDef]
      iframe
    · exact absurd rfl He2
  subst He2 Hd2
  try wp_auto
  wp_apply wp_ValueUnm _ _ rd I (R ++ [op] ++ sp.le64 k) $$ [$Hpkg $Hpkg2 $Hrd $HI $V]
    as %e3 ⟨%d3, HI, Hr3⟩
  icases Hr3 with (⟨%He3, %l0, %l1, %x, %y, %v, %vs, %Hd3, V, Hvs⟩ | ⟨%He3, %v', V⟩)
  rotate_left
  · rcases e3 with e3 | _
    · try wp_auto
      iapply HΦ; iexists [op] ++ sp.le64 k ++ d3
      rw [← List.append_assoc, ← List.append_assoc]
      iframe HI; iright
      isplitr
      · ipureintro; intro h; cases h
      iexists (state.Command.mk op k v')
      iapply typedPointsto_combine _ _ _ Htn
      simp only [TypedPointsto.typedPointstoDef]
      iframe
    · exact absurd rfl He3
  subst He3
  obtain ⟨rfl, hl⟩ := Hd3
  try wp_auto
  iapply HΦ; iexists [op] ++ sp.le64 k ++ sp.decValue l0 l1 x y v
  rw [← List.append_assoc, ← List.append_assoc]
  iframe HI; ileft
  isplitr
  · ipureintro; rfl
  iexists op, k, l0, l1, x, y, v, vs
  iframe Hvs
  isplitr
  · ipureintro; exact ⟨rfl, hl⟩
  iapply typedPointsto_combine _ _ _ Htn
  simp only [TypedPointsto.typedPointstoDef]
  iframe

theorem replica.defs.Propose.Unmarshal.wp_proof
    (wp_ValueUnm : state.Value.Unmarshal.spec (GF := GF)) :
    replica.defs.Propose.Unmarshal.spec (GF := GF) := by
  intro t v rd I R
  wp_start as ⟨#Hrd, HI, Ht⟩
  ihave %Htn := typedPointsto_not_null $$ Ht
  iStructNamed Ht
  try wp_auto
  ihave Hsl := slice_array b_ptr 8 (Perennial.zero_val (GoArray w8 8)) (by decide) $$ b
  rw [show sint.Z (W64 0) = 0 from rfl, go.arrayIndexRef_0, show W64 8 - W64 0 = W64 8 from rfl]
  rw [show (Perennial.zero_val (GoArray w8 8)).arr = List.replicate 8 (W8 0) from rfl]
  wp_apply bufio.wp_ReadAtLeast rd I R _ (List.replicate 8 (W8 0)) (W64 8) ?_ $$
    [$Hpkg $Hrd $HI $Hsl] as %n %err ⟨%data, %Hd, Hsl, HI, #He⟩
  obtain ⟨hn, hdl, herr⟩ := Hd
  try wp_auto
  rcases err with e | _
  · try wp_auto
    iapply HΦ; iexists data; iframe HI; iright
    isplitr
    · ipureintro; intro h; cases h
    iexists v
    iapply typedPointsto_combine _ _ _ Htn
    simp only [TypedPointsto.typedPointstoDef]
    iframe
  have h8 : data.length = 8 := by
    have := herr.1 rfl; simp at hdl; have : sint.Z (W64 8) = 8 := rfl; omega
  obtain ⟨d0, d1, d2, d3, d4, d5, d6, d7, rfl⟩ : ∃ d0 d1 d2 d3 d4 d5 d6 d7 : w8,
      data = [d0, d1, d2, d3, d4, d5, d6, d7] := by
    match data, h8 with
    | [d0, d1, d2, d3, d4, d5, d6, d7], _ => exact ⟨d0, d1, d2, d3, d4, d5, d6, d7, rfl⟩
  isimp only [List.length_cons, List.length_nil, List.drop_replicate, List.append_nil,
    Nat.reduceAdd, Nat.sub_self, List.replicate_zero] at Hsl
  try wp_auto
  ld8
  try wp_auto
  have hseq := leToU32_le [d0, d1, d2, d3] rfl
  have hcl := leToU32_le [d4, d5, d6, d7] rfl
  wp_apply wp_Command_Unmarshal wp_ValueUnm _ _ rd I (R ++ [d0, d1, d2, d3, d4, d5, d6, d7]) $$
    [$Hpkg $Hpkg2 $Hrd $HI $Command] as %e2 ⟨%d2, HI, Hr2⟩
  icases Hr2 with (⟨%He2, %op, %k, %l0, %l1, %x, %y, %val, %vs, %Hd2, Command, Hvs⟩ | ⟨%He2, %c', Command⟩)
  rotate_left
  · -- R-F1 fixed (fix3): `Command.Unmarshal`'s error is returned
    rcases e2 with e2 | _
    rotate_left
    · exact absurd rfl He2
    try wp_auto
    rw [List.append_assoc]
    iapply HΦ; iexists _; iframe HI; iright
    isplitr
    · ipureintro; intro h; cases h
    iexists (replica.defs.Propose.mk _ _ c' v.Timestamp')
    iapply typedPointsto_combine _ _ _ Htn
    simp only [TypedPointsto.typedPointstoDef]
    iframe
  subst He2
  obtain ⟨rfl, hl⟩ := Hd2
  try wp_auto
  wp_apply bufio.wp_ReadAtLeast rd I _ _ _ (W64 8) ?_ $$ [$Hpkg $Hrd $HI $Hsl]
    as %n3 %err3 ⟨%data3, %Hd3, Hsl, HI, #He3⟩
  obtain ⟨hn3, hdl3, herr3⟩ := Hd3
  try wp_auto
  rcases err3 with e3 | _
  · try wp_auto
    iapply HΦ; iexists _
    rw [show R ++ [d0, d1, d2, d3, d4, d5, d6, d7] ++ ([op] ++ sp.le64 k ++ sp.decValue l0 l1 x y val)
      ++ data3 = R ++ ([d0, d1, d2, d3, d4, d5, d6, d7] ++ ([op] ++ sp.le64 k ++
        sp.decValue l0 l1 x y val) ++ data3) by simp]
    iframe HI; iright
    isplitr
    · ipureintro; intro h; cases h
    iexists (replica.defs.Propose.mk _ _ (state.Command.mk op k vs) v.Timestamp')
    iapply typedPointsto_combine _ _ _ Htn
    simp only [TypedPointsto.typedPointstoDef]
    iframe
  have h8' : data3.length = 8 := by
    have := herr3.1 rfl; simp at hdl3; have : sint.Z (W64 8) = 8 := rfl; omega
  obtain ⟨e0, e1, e2, e3, e4, e5, e6, e7, rfl⟩ : ∃ e0 e1 e2 e3 e4 e5 e6 e7 : w8,
      data3 = [e0, e1, e2, e3, e4, e5, e6, e7] := by
    match data3, h8' with
    | [e0, e1, e2, e3, e4, e5, e6, e7], _ => exact ⟨e0, e1, e2, e3, e4, e5, e6, e7, rfl⟩
  isimp only [List.length_cons, List.length_nil, List.drop, List.append_nil] at Hsl
  try wp_auto
  ld8
  try wp_auto
  have hts := leToU64_le [e0, e1, e2, e3, e4, e5, e6, e7] rfl
  have hv16 : val.length < 2 ^ 16 := by
    have := l0.isLt; have := l1.isLt; omega
  iapply HΦ; iexists _
  rw [show R ++ [d0, d1, d2, d3, d4, d5, d6, d7] ++ ([op] ++ sp.le64 k ++ sp.decValue l0 l1 x y val)
    ++ [e0, e1, e2, e3, e4, e5, e6, e7] = R ++ ([d0, d1, d2, d3, d4, d5, d6, d7] ++ ([op] ++
      sp.le64 k ++ sp.decValue l0 l1 x y val) ++ [e0, e1, e2, e3, e4, e5, e6, e7]) by simp]
  iframe HI; ileft
  isplitr
  · ipureintro; rfl
  iexists (leToU32 [d0, d1, d2, d3]), (leToU32 [d4, d5, d6, d7]), ⟨op, k, val⟩,
    (leToU64 [e0, e1, e2, e3, e4, e5, e6, e7]), vs
  iframe Hvs
  isplitr
  · ipureintro
    have := sp.propose_decodes (leToU32 [d0, d1, d2, d3]) (leToU32 [d4, d5, d6, d7]) op k
      l0 l1 x y val (leToU64 [e0, e1, e2, e3, e4, e5, e6, e7]) hv16 hl
    unfold sp.le32 sp.le64 at this
    rw [hseq, hcl, hts] at this
    simpa [List.append_assoc, sp.le64] using this
  rw [encoding.binary.leToU32_4, encoding.binary.leToU32_4, encoding.binary.leToU64_8]
  iapply typedPointsto_combine _ _ _ Htn
  simp only [TypedPointsto.typedPointstoDef]
  iframe

end proofs

end Perennial.github_com.imdea_software.swiftpaxos
