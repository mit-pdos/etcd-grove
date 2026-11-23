/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/Wire/Proof/Slices.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

# U1: the slice types (`PreAccept`, `EAccept`, `ECommit`, `TryPreAccept`, `PrepareReply`)
-/
module

public import Dsverify.Proof.gryff.Wire.Proof.Gryff1
public import Dsverify.Proof.gryff.Wire.Proof.VarintWp

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.wire

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode

namespace gryffproto

section pure
variable [GooseExts]

theorem PreAccept.enc_split (m : PreAccept.Msg) : PreAccept.enc m =
    (u32Le m.LeaderId ++ u32Le m.Replica ++ u32Le m.Instance ++ u32Le m.Ballot) ++
      varintEnc (sint.Z (W64 m.Command.length)) ++
      ((m.Command.flatMap state.Command.enc) ++ u32Le m.Seq ++ arrLe32 m.Deps ++
        gryffproto.ValTag.enc m.Base) := by
  simp only [PreAccept.enc, List.append_assoc]

theorem PreAccept.vok_of_next (F D : List w8) (hF : F.length = 16)
    (h : PreAccept.nextOk (F ++ D)) : vok D := by
  obtain ⟨m, hwf, hcmp⟩ := h
  rw [PreAccept.enc_split] at hcmp
  exact varint_vok (len := m.Command.length) hwf (by simp [hF, u32Le_length]) hcmp

theorem PreAccept.pin (F V P : List w8) (hF : F.length = 16) (hV : terminated V)
    (h : PreAccept.nextOk (F ++ (V ++ P))) :
    ∃ len : Nat, len < 2 ^ 63 ∧ V = uvarintEnc (2 * len) := by
  obtain ⟨m, hwf, hcmp⟩ := h
  rw [PreAccept.enc_split] at hcmp
  exact ⟨m.Command.length, hwf,
    varint_pin (len := m.Command.length) hwf (by simp [hF, u32Le_length]) hV hcmp⟩

theorem ECommit.enc_split (m : ECommit.Msg) : ECommit.enc m =
    (u32Le m.LeaderId ++ u32Le m.Replica ++ u32Le m.Instance) ++
      varintEnc (sint.Z (W64 m.Command.length)) ++
      ((m.Command.flatMap state.Command.enc) ++ u32Le m.Seq ++ arrLe32 m.Deps ++
        gryffproto.ValTag.enc m.Base) := by
  simp only [ECommit.enc, List.append_assoc]

theorem ECommit.vok_of_next (F D : List w8) (hF : F.length = 12)
    (h : ECommit.nextOk (F ++ D)) : vok D := by
  obtain ⟨m, hwf, hcmp⟩ := h
  rw [ECommit.enc_split] at hcmp
  exact varint_vok (len := m.Command.length) hwf (by simp [hF, u32Le_length]) hcmp

theorem ECommit.pin (F V P : List w8) (hF : F.length = 12) (hV : terminated V)
    (h : ECommit.nextOk (F ++ (V ++ P))) :
    ∃ len : Nat, len < 2 ^ 63 ∧ V = uvarintEnc (2 * len) := by
  obtain ⟨m, hwf, hcmp⟩ := h
  rw [ECommit.enc_split] at hcmp
  exact ⟨m.Command.length, hwf,
    varint_pin (len := m.Command.length) hwf (by simp [hF, u32Le_length]) hV hcmp⟩

theorem EAccept.enc_split (m : EAccept.Msg) : EAccept.enc m =
    (u32Le m.LeaderId ++ u32Le m.Replica ++ u32Le m.Instance ++ u32Le m.Ballot ++ u32Le m.Count ++
      u32Le m.Seq ++ arrLe32 m.Deps) ++
      varintEnc (sint.Z (W64 m.Command.length)) ++
      ((m.Command.flatMap state.Command.enc) ++ gryffproto.ValTag.enc m.Base) := by
  simp only [EAccept.enc, List.append_assoc]

theorem EAccept.vok_of_next (F D : List w8) (hF : F.length = 44)
    (h : EAccept.nextOk (F ++ D)) : vok D := by
  obtain ⟨m, hwf, hcmp⟩ := h
  rw [EAccept.enc_split] at hcmp
  exact varint_vok (len := m.Command.length) hwf
    (by simp [hF, u32Le_length, arrLe32, List.range_succ]) hcmp

theorem EAccept.pin (F V P : List w8) (hF : F.length = 44) (hV : terminated V)
    (h : EAccept.nextOk (F ++ (V ++ P))) :
    ∃ len : Nat, len < 2 ^ 63 ∧ V = uvarintEnc (2 * len) := by
  obtain ⟨m, hwf, hcmp⟩ := h
  rw [EAccept.enc_split] at hcmp
  exact ⟨m.Command.length, hwf,
    varint_pin (len := m.Command.length) hwf
      (by simp [hF, u32Le_length, arrLe32, List.range_succ]) hV hcmp⟩

theorem TryPreAccept.enc_split (m : TryPreAccept.Msg) : TryPreAccept.enc m =
    (u32Le m.LeaderId ++ u32Le m.Replica ++ u32Le m.Instance ++ u32Le m.Ballot) ++
      varintEnc (sint.Z (W64 m.Command.length)) ++
      ((m.Command.flatMap state.Command.enc) ++ u32Le m.Seq ++ arrLe32 m.Deps ++
        gryffproto.ValTag.enc m.Base) := by
  simp only [TryPreAccept.enc, List.append_assoc]

theorem TryPreAccept.vok_of_next (F D : List w8) (hF : F.length = 16)
    (h : TryPreAccept.nextOk (F ++ D)) : vok D := by
  obtain ⟨m, hwf, hcmp⟩ := h
  rw [TryPreAccept.enc_split] at hcmp
  exact varint_vok (len := m.Command.length) hwf (by simp [hF, u32Le_length]) hcmp

theorem TryPreAccept.pin (F V P : List w8) (hF : F.length = 16) (hV : terminated V)
    (h : TryPreAccept.nextOk (F ++ (V ++ P))) :
    ∃ len : Nat, len < 2 ^ 63 ∧ V = uvarintEnc (2 * len) := by
  obtain ⟨m, hwf, hcmp⟩ := h
  rw [TryPreAccept.enc_split] at hcmp
  exact ⟨m.Command.length, hwf,
    varint_pin (len := m.Command.length) hwf (by simp [hF, u32Le_length]) hV hcmp⟩

theorem PrepareReply.enc_split (m : PrepareReply.Msg) : PrepareReply.enc m =
    (u32Le m.AcceptorId ++ u32Le m.Replica ++ u32Le m.Instance ++ [m.OK] ++ u32Le m.Ballot ++
      u32Le m.VBallot ++ [m.Status]) ++
      varintEnc (sint.Z (W64 m.Command.length)) ++
      ((m.Command.flatMap state.Command.enc) ++ u32Le m.Seq ++ arrLe32 m.Deps ++
        gryffproto.ValTag.enc m.Base) := by
  simp only [PrepareReply.enc, List.append_assoc]

theorem PrepareReply.vok_of_next (F D : List w8) (hF : F.length = 22)
    (h : PrepareReply.nextOk (F ++ D)) : vok D := by
  obtain ⟨m, hwf, hcmp⟩ := h
  rw [PrepareReply.enc_split] at hcmp
  exact varint_vok (len := m.Command.length) hwf (by simp [hF, u32Le_length]) hcmp

theorem PrepareReply.pin (F V P : List w8) (hF : F.length = 22) (hV : terminated V)
    (h : PrepareReply.nextOk (F ++ (V ++ P))) :
    ∃ len : Nat, len < 2 ^ 63 ∧ V = uvarintEnc (2 * len) := by
  obtain ⟨m, hwf, hcmp⟩ := h
  rw [PrepareReply.enc_split] at hcmp
  exact ⟨m.Command.length, hwf,
    varint_pin (len := m.Command.length) hwf (by simp [hF, u32Le_length]) hV hcmp⟩

end pure

end gryffproto

section uproofs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [bufio.Assumptions] [io.Assumptions] [encoding.binary.Assumptions] [wire.BufioSpecs GF]
variable [src.state.Assumptions] [src.gryffproto.Assumptions] [src.epaxosproto.Assumptions]
variable [src.clientproto.Assumptions] [src.genericsmrproto.Assumptions]
variable [BinaryVarintHyps GF]

namespace gryffproto

set_option maxHeartbeats 4000000 in
theorem PreAccept.wp_Unmarshal_proof (t : Loc) (v0 : src.gryffproto.PreAccept) (br : Loc) (rd : RSt GF)
    (I : List w8 → IProp GF) (R : List w8) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ isPkgInit (PROP := IProp GF) pkg_id.io ∗
        readerOk rd I ∗ readNext br rd I R PreAccept.nextOk ∗
        ownReader br rd I R ∗ t ↦ v0 }}
      (App (Val (t @!! go.GoType.PointerType src.gryffproto.PreAccept.ty @!! go!"Unmarshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Reader.ty) #br)))
    {{ (err : GoInterface), RET #err;
        (⌜err = interface.nil⌝ ∗ ∃ m : PreAccept.Msg, ⌜PreAccept.wf m⌝ ∗
          PreAccept.own t (DFrac.own 1) m ∗ ownReader br rd I (R ++ PreAccept.enc m)) ∨
        (⌜err ≠ interface.nil⌝ ∗ rdErr rd err ∗ ∃ (v : src.gryffproto.PreAccept) (R' : List w8),
          t ↦ v ∗ ownReader br rd I (R ++ R')) }} := by
  wp_start as ⟨#Hrd, #Hnext, Hown, Ht⟩
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Ht
  iStructNamed Ht
  irename : ("_" ∷ True : IProp GF) => Htrue
  iclear Htrue
  wp_auto
  have hts : go.typeSetContains (go.GoType.PointerType bufio.Reader.ty)
      src.gryffproto.byteReader.ty = true := by go_type_set
  simp only [hts, ↓reduceIte]
  wp_auto
  rw [show sint.Z (W64 0) = 0 from rfl, go.arrayIndexRef_0, show W64 16 - W64 0 = W64 16 from rfl,
    show W64 24 - W64 0 = W64 24 from rfl]
  ihave ⟨Hb, Hrest⟩ := array_prefix_slice (GF := GF) b_ptr (W64 16) (W64 24) 24
    (zero_val (GoArray w8 24)).arr (by decide) (by decide) $$ b
  wp_apply wp_wire_ReadAtLeast $$ [$Hrd $Hown $Hb] as %nr %err ⟨%data, Hown, Hr⟩
  icases Hr with (⟨⟨%Hnil, %Hlen⟩, Hb⟩ | ⟨%Hne, #Ha, %vs', Hb⟩)
  rotate_left
  · u1_ret_err (src.gryffproto.PreAccept.mk _ _ _ _ _ _ _ _)
  subst Hnil
  have hl : data.length = 16 := by simpa using Hlen
  wp_auto
  repeat u1_wload
  ihave #Hvok := readNext_shift br rd I R data _ $$ Hnext
  ihave #Hvok := readNext_mono br rd I (R ++ data) _ vok
    (fun D Hn => PreAccept.vok_of_next data D hl Hn) $$ Hvok
  wp_apply wp_ReadVarint br rd I (R ++ data) $$ [$Hrd $Hvok $Hown] as %x %err ⟨%V, Hown, Hr⟩
  · iexact Hpkg3
  icases Hr with (%Hok | #Ha)
  rotate_left
  · ihave %Hne := rdErr_ne _ _ $$ Ha
    u1_ret_err (src.gryffproto.PreAccept.mk _ _ _ _ _ _ _ _)
  obtain ⟨rfl, ux, hV, rfl⟩ := Hok
  rw [List.append_assoc]
  imod ownReader_peek PreAccept.nextOk br rd I R (data ++ V) $$ [Hnext Hown] with ⟨Hown, %Hpk⟩
  · iframe Hnext Hown
  obtain ⟨pend, Hpk⟩ := Hpk
  obtain ⟨len, hlen, hVlen⟩ := PreAccept.pin data V pend hl
    (by rw [hV]; exact uvarintEnc_terminated _) (by simpa [List.append_assoc] using Hpk)
  have hux : uint.nat ux = 2 * len := uvarintEnc_inj (hV.symm.trans hVlen)
  have hx : (if ux &&& W64 1 = W64 0 then ux >>> W64 1 else ~~~(ux >>> W64 1)) = W64 len := by
    have h1 : ux &&& W64 1 = W64 0 := by
      apply BitVec.eq_of_toNat_eq
      simp only [uint.nat] at hux
      simp [BitVec.toNat_and, hux]
    rw [if_pos h1]
    apply BitVec.eq_of_toNat_eq
    simp only [uint.nat] at hux
    simp [hux]
    omega
  rw [hx]
  wp_auto
  have hlenZ : sint.Z (W64 (len : Int)) = len := encoding.binary.sint_W64_lit _ ⟨by omega, by omega⟩
  wp_apply (wp_slice_make2 (V := src.state.Command) (W64 (len : Int))) as %sl ⟨Hsl, -⟩
  · ipureintro; omega
  have hlenN : sint.nat (W64 (len : Int)) = len := by
    simp only [sint.nat, hlenZ]; simp
  rw [hlenN]
  ihave HL : (∃ (iv : w64) (cs : List src.state.Command),
      "i" ∷ i_ptr ↦ iv ∗
      "Hsl" ∷ sl ↦* (cs ++ List.replicate (len - cs.length) (zero_val src.state.Command)) ∗
      "Hown" ∷ ownReader br rd I (R ++ (data ++ V) ++ cs.flatMap state.Command.enc) ∗
      "%Hc" ∷ ⌜sint.Z iv = cs.length ∧ cs.length ≤ len⌝ : IProp GF) $$ [i Hsl Hown]
  · iexists W64 0, []
    simp only [List.length_nil, Nat.sub_zero, List.nil_append, List.flatMap_nil, List.append_nil]
    iframe
    ipureintro; exact ⟨rfl, Nat.zero_le _⟩
  wp_for HL
  obtain ⟨hiv, hcl⟩ := Hc
  ihave %Hsll := ownSlice_len _ _ _ $$ Hsl
  have hsl : sint.Z sl.len = len := by
    have h1 := Hsll.1
    simp only [List.length_append, List.length_replicate] at h1
    have h3 : ((sint.nat sl.len : Nat) : Int) = sint.Z sl.len := Int.toNat_of_nonneg Hsll.2
    omega
  wp_if_destruct
  · have hlt : cs.length < len := by rw [hlenZ, hiv] at Hif; omega
    rw [if_pos ⟨by omega, by omega⟩]
    have hlook : (cs ++ List.replicate (len - cs.length) (zero_val src.state.Command))[
        (sint.Z iv).toNat]? = some (zero_val src.state.Command) := by
      rw [hiv, Int.toNat_natCast, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self,
        List.getElem?_replicate]
      simp; omega
    icases ownSlice_elem_acc (sint.Z iv) (zero_val _) sl (DFrac.own 1) _ (by omega) hlook $$ Hsl
      with ⟨He, Hback⟩
    wp_auto
    wp_apply state.Command.wp_Unmarshal_proof $$ [$Hrd $Hown $He] as %err
      (⟨%Hnil, %mc, -, Hm, Hown⟩ | ⟨%Hne, #Ha, %vv, %R1, He, Hown⟩)
    · iapply readNext_true; intro; trivial
    · subst Hnil
      wp_auto
      wp_for_post
      iframe
      iexists iv + W64 1, cs ++ [mc]
      ihave Hsl := Hback $$ %mc Hm
      rw [hiv, Int.toNat_natCast, list_fill_step _ _ _ _ hlt, List.flatMap_append,
        List.flatMap_singleton]
      simp only [List.append_assoc]
      iframe
      ipureintro
      refine ⟨?_, by simp; omega⟩
      have : sint.Z (iv + W64 1) = sint.Z iv + 1 := by word
      rw [this, hiv]; simp
    · u1_ret_err (src.gryffproto.PreAccept.mk _ _ _ _ _ _ _ _)
  -- after the loop: all `len` commands read
  have hcs : cs.length = len := by rw [hlenZ, hiv] at Hif; omega
  rw [hcs, Nat.sub_self, List.replicate_zero, List.append_nil]
  rw [show sint.Z (W64 0) = 0 from rfl, go.arrayIndexRef_0, show W64 24 - W64 0 = W64 24 from rfl]
  ihave Hb := array_of_prefix_slice (GF := GF) b_ptr (W64 16) (W64 24) _ data _ $$ [$Hb $Hrest]
  rw [show sint.Z (W64 16) + (24 - sint.Z (W64 16)) = (24 : Int) from rfl]
  ihave Hb := slice_array (GF := GF) b_ptr _ _ (by simp [hl, zero_arr_w8]; decide) $$ Hb
  wp_apply wp_wire_ReadAtLeast $$ [$Hrd $Hown $Hb] as %nr2 %err ⟨%data2, Hown, Hr⟩
  icases Hr with (⟨⟨%Hnil, %Hlen2⟩, Hb⟩ | ⟨%Hne, #Ha, %vs', Hb⟩)
  rotate_left
  · u1_ret_err (src.gryffproto.PreAccept.mk _ _ _ _ _ _ _ _)
  subst Hnil
  have hl2 : data2.length = 24 := by simpa [hl] using Hlen2
  wp_auto
  repeat (first | u1_wload | u1_wstore_deps)
  wp_apply ValTag.wp_Unmarshal_proof $$ [$Hrd $Hown $Base] as %err
    (⟨%Hnil, %mb, -, HBase, Hown⟩ | ⟨%Hne, #Ha, %vb, %R2, Base, Hown⟩)
  · iapply readNext_true; intro; trivial
  rotate_left
  · u1_ret_err (src.gryffproto.PreAccept.mk _ _ _ _ _ _ _ _)
  subst Hnil
  wp_auto
  ihave %Hdl := array_len _ _ _ _ $$ Deps
  icases pt_name _ _ _ $$ LeaderId with ⟨%lid, LeaderId, %hlid⟩
  icases pt_name _ _ _ $$ Replica with ⟨%rep, Replica, %hrep⟩
  icases pt_name _ _ _ $$ Instance with ⟨%ins, Instance, %hins⟩
  icases pt_name _ _ _ $$ Ballot with ⟨%bal, Ballot, %hbal⟩
  icases pt_name _ _ _ $$ Seq with ⟨%seq, Seq, %hseq⟩
  icases pt_name _ _ _ $$ Deps with ⟨%deps, Deps, %hdeps⟩
  have e1 : data = u32Le lid ++ u32Le rep ++ u32Le ins ++ u32Le bal := by
    subst hlid hrep hins hbal
    conv => lhs; rw [list_getD_eq data 16 hl]
    simp only [List.range_succ, List.range_zero, List.map_append, List.map_cons, List.map_nil,
      List.nil_append, List.cons_append, List.singleton_append, u32Le_dec, List.append_assoc]
  have e2 : data2 = u32Le seq ++ arrLe32 deps := by
    simp only [List.length_set] at Hdl
    subst hseq hdeps
    rw [set5 v0.Deps'.arr (by omega), arrLe32_5]
    conv => lhs; rw [list_getD_eq data2 24 hl2]
    simp only [List.range_succ, List.range_zero, List.map_append, List.map_cons, List.map_nil,
      List.nil_append, List.cons_append, List.singleton_append, u32Le_dec, List.append_assoc]
  iapply HΦ
  ileft
  isplitr
  · ipureintro; rfl
  iexists (PreAccept.Msg.mk lid rep ins bal cs seq deps mb)
  isplitr
  · ipureintro; show cs.length < 2 ^ 63; omega
  isplitl [LeaderId Replica Instance Ballot Command Hsl Seq Deps HBase]
  · iunfold PreAccept.own
    iexists sl
    iframe Hsl
    iapply typedPointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typedPointstoDef, PreAccept.goVal]
    iframe
  iapply ownReader_eq _ _ _ _ _ ?_ $$ Hown
  rw [PreAccept.enc, e1, e2, hVlen, hcs]
  simp only [varintEnc_len _ hlen, List.append_assoc]

set_option maxHeartbeats 4000000 in
theorem EAccept.wp_Unmarshal_proof (t : Loc) (v0 : src.gryffproto.EAccept) (br : Loc) (rd : RSt GF)
    (I : List w8 → IProp GF) (R : List w8) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ isPkgInit (PROP := IProp GF) pkg_id.io ∗
        readerOk rd I ∗ readNext br rd I R EAccept.nextOk ∗
        ownReader br rd I R ∗ t ↦ v0 }}
      (App (Val (t @!! go.GoType.PointerType src.gryffproto.EAccept.ty @!! go!"Unmarshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Reader.ty) #br)))
    {{ (err : GoInterface), RET #err;
        (⌜err = interface.nil⌝ ∗ ∃ m : EAccept.Msg, ⌜EAccept.wf m⌝ ∗
          EAccept.own t (DFrac.own 1) m ∗ ownReader br rd I (R ++ EAccept.enc m)) ∨
        (⌜err ≠ interface.nil⌝ ∗ rdErr rd err ∗ ∃ (v : src.gryffproto.EAccept) (R' : List w8),
          t ↦ v ∗ ownReader br rd I (R ++ R')) }} := by
  wp_start as ⟨#Hrd, #Hnext, Hown, Ht⟩
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Ht
  iStructNamed Ht
  irename : ("_" ∷ True : IProp GF) => Htrue
  iclear Htrue
  wp_auto
  have hts : go.typeSetContains (go.GoType.PointerType bufio.Reader.ty)
      src.gryffproto.byteReader.ty = true := by go_type_set
  simp only [hts, ↓reduceIte]
  wp_auto
  rw [show sint.Z (W64 0) = 0 from rfl, go.arrayIndexRef_0, show W64 44 - W64 0 = W64 44 from rfl]
  ihave ⟨Hb, Hrest⟩ := array_prefix_slice (GF := GF) b_ptr (W64 44) (W64 44) 44
    (zero_val (GoArray w8 44)).arr (by decide) (by decide) $$ b
  wp_apply wp_wire_ReadAtLeast $$ [$Hrd $Hown $Hb] as %nr %err ⟨%data, Hown, Hr⟩
  icases Hr with (⟨⟨%Hnil, %Hlen⟩, Hb⟩ | ⟨%Hne, #Ha, %vs', Hb⟩)
  rotate_left
  · u1_ret_err (src.gryffproto.EAccept.mk _ _ _ _ _ _ _ _ _)
  subst Hnil
  have hl : data.length = 44 := by simpa using Hlen
  wp_auto
  repeat (first | u1_wload | u1_wstore_deps)
  ihave #Hvok := readNext_shift br rd I R data _ $$ Hnext
  ihave #Hvok := readNext_mono br rd I (R ++ data) _ vok
    (fun D Hn => EAccept.vok_of_next data D hl Hn) $$ Hvok
  wp_apply wp_ReadVarint br rd I (R ++ data) $$ [$Hrd $Hvok $Hown] as %x %err ⟨%V, Hown, Hr⟩
  · iexact Hpkg3
  icases Hr with (%Hok | #Ha)
  rotate_left
  · ihave %Hne := rdErr_ne _ _ $$ Ha
    u1_ret_err (src.gryffproto.EAccept.mk _ _ _ _ _ _ _ _ _)
  obtain ⟨rfl, ux, hV, rfl⟩ := Hok
  rw [List.append_assoc]
  imod ownReader_peek EAccept.nextOk br rd I R (data ++ V) $$ [Hnext Hown] with ⟨Hown, %Hpk⟩
  · iframe Hnext Hown
  obtain ⟨pend, Hpk⟩ := Hpk
  obtain ⟨len, hlen, hVlen⟩ := EAccept.pin data V pend hl
    (by rw [hV]; exact uvarintEnc_terminated _) (by simpa [List.append_assoc] using Hpk)
  have hux : uint.nat ux = 2 * len := uvarintEnc_inj (hV.symm.trans hVlen)
  have hx : (if ux &&& W64 1 = W64 0 then ux >>> W64 1 else ~~~(ux >>> W64 1)) = W64 len := by
    have h1 : ux &&& W64 1 = W64 0 := by
      apply BitVec.eq_of_toNat_eq
      simp only [uint.nat] at hux
      simp [BitVec.toNat_and, hux]
    rw [if_pos h1]
    apply BitVec.eq_of_toNat_eq
    simp only [uint.nat] at hux
    simp [hux]
    omega
  rw [hx]
  wp_auto
  have hlenZ : sint.Z (W64 (len : Int)) = len := encoding.binary.sint_W64_lit _ ⟨by omega, by omega⟩
  wp_apply (wp_slice_make2 (V := src.state.Command) (W64 (len : Int))) as %sl ⟨Hsl, -⟩
  · ipureintro; omega
  have hlenN : sint.nat (W64 (len : Int)) = len := by
    simp only [sint.nat, hlenZ]; simp
  rw [hlenN]
  ihave HL : (∃ (iv : w64) (cs : List src.state.Command),
      "i" ∷ i_ptr ↦ iv ∗
      "Hsl" ∷ sl ↦* (cs ++ List.replicate (len - cs.length) (zero_val src.state.Command)) ∗
      "Hown" ∷ ownReader br rd I (R ++ (data ++ V) ++ cs.flatMap state.Command.enc) ∗
      "%Hc" ∷ ⌜sint.Z iv = cs.length ∧ cs.length ≤ len⌝ : IProp GF) $$ [i Hsl Hown]
  · iexists W64 0, []
    simp only [List.length_nil, Nat.sub_zero, List.nil_append, List.flatMap_nil, List.append_nil]
    iframe
    ipureintro; exact ⟨rfl, Nat.zero_le _⟩
  wp_for HL
  obtain ⟨hiv, hcl⟩ := Hc
  ihave %Hsll := ownSlice_len _ _ _ $$ Hsl
  have hsl : sint.Z sl.len = len := by
    have h1 := Hsll.1
    simp only [List.length_append, List.length_replicate] at h1
    have h3 : ((sint.nat sl.len : Nat) : Int) = sint.Z sl.len := Int.toNat_of_nonneg Hsll.2
    omega
  wp_if_destruct
  · have hlt : cs.length < len := by rw [hlenZ, hiv] at Hif; omega
    rw [if_pos ⟨by omega, by omega⟩]
    have hlook : (cs ++ List.replicate (len - cs.length) (zero_val src.state.Command))[
        (sint.Z iv).toNat]? = some (zero_val src.state.Command) := by
      rw [hiv, Int.toNat_natCast, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self,
        List.getElem?_replicate]
      simp; omega
    icases ownSlice_elem_acc (sint.Z iv) (zero_val _) sl (DFrac.own 1) _ (by omega) hlook $$ Hsl
      with ⟨He, Hback⟩
    wp_auto
    wp_apply state.Command.wp_Unmarshal_proof $$ [$Hrd $Hown $He] as %err
      (⟨%Hnil, %mc, -, Hm, Hown⟩ | ⟨%Hne, #Ha, %vv, %R1, He, Hown⟩)
    · iapply readNext_true; intro; trivial
    · subst Hnil
      wp_auto
      wp_for_post
      iframe
      iexists iv + W64 1, cs ++ [mc]
      ihave Hsl := Hback $$ %mc Hm
      rw [hiv, Int.toNat_natCast, list_fill_step _ _ _ _ hlt, List.flatMap_append,
        List.flatMap_singleton]
      simp only [List.append_assoc]
      iframe
      ipureintro
      refine ⟨?_, by simp; omega⟩
      have : sint.Z (iv + W64 1) = sint.Z iv + 1 := by word
      rw [this, hiv]; simp
    · u1_ret_err (src.gryffproto.EAccept.mk _ _ _ _ _ _ _ _ _)
  -- after the loop: all `len` commands read
  have hcs : cs.length = len := by rw [hlenZ, hiv] at Hif; omega
  rw [hcs, Nat.sub_self, List.replicate_zero, List.append_nil]
  wp_apply ValTag.wp_Unmarshal_proof $$ [$Hrd $Hown $Base] as %err
    (⟨%Hnil, %mb, -, HBase, Hown⟩ | ⟨%Hne, #Ha, %vb, %R2, Base, Hown⟩)
  · iapply readNext_true; intro; trivial
  rotate_left
  · u1_ret_err (src.gryffproto.EAccept.mk _ _ _ _ _ _ _ _ _)
  subst Hnil
  wp_auto
  ihave %Hdl := array_len _ _ _ _ $$ Deps
  icases pt_name _ _ _ $$ LeaderId with ⟨%lid, LeaderId, %hlid⟩
  icases pt_name _ _ _ $$ Replica with ⟨%rep, Replica, %hrep⟩
  icases pt_name _ _ _ $$ Instance with ⟨%ins, Instance, %hins⟩
  icases pt_name _ _ _ $$ Ballot with ⟨%bal, Ballot, %hbal⟩
  icases pt_name _ _ _ $$ Count with ⟨%cnt, Count, %hcnt⟩
  icases pt_name _ _ _ $$ Seq with ⟨%seq, Seq, %hseq⟩
  icases pt_name _ _ _ $$ Deps with ⟨%deps, Deps, %hdeps⟩
  have e1 : data = u32Le lid ++ u32Le rep ++ u32Le ins ++ u32Le bal ++ u32Le cnt ++ u32Le seq ++
      arrLe32 deps := by
    simp only [List.length_set] at Hdl
    subst hlid hrep hins hbal hcnt hseq hdeps
    rw [set5 v0.Deps'.arr (by omega), arrLe32_5]
    conv => lhs; rw [list_getD_eq data 44 hl]
    simp only [List.range_succ, List.range_zero, List.map_append, List.map_cons, List.map_nil,
      List.nil_append, List.cons_append, List.singleton_append, u32Le_dec, List.append_assoc]
  iapply HΦ
  ileft
  isplitr
  · ipureintro; rfl
  iexists (EAccept.Msg.mk lid rep ins bal cnt seq deps cs mb)
  isplitr
  · ipureintro; show cs.length < 2 ^ 63; omega
  isplitl [LeaderId Replica Instance Ballot Count Seq Deps Command Hsl HBase]
  · iunfold EAccept.own
    iexists sl
    iframe Hsl
    iapply typedPointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typedPointstoDef, EAccept.goVal]
    iframe
  iapply ownReader_eq _ _ _ _ _ ?_ $$ Hown
  rw [EAccept.enc, e1, hVlen, hcs]
  simp only [varintEnc_len _ hlen, List.append_assoc]

set_option maxHeartbeats 4000000 in
theorem ECommit.wp_Unmarshal_proof (t : Loc) (v0 : src.gryffproto.ECommit) (br : Loc) (rd : RSt GF)
    (I : List w8 → IProp GF) (R : List w8) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ isPkgInit (PROP := IProp GF) pkg_id.io ∗
        readerOk rd I ∗ readNext br rd I R ECommit.nextOk ∗
        ownReader br rd I R ∗ t ↦ v0 }}
      (App (Val (t @!! go.GoType.PointerType src.gryffproto.ECommit.ty @!! go!"Unmarshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Reader.ty) #br)))
    {{ (err : GoInterface), RET #err;
        (⌜err = interface.nil⌝ ∗ ∃ m : ECommit.Msg, ⌜ECommit.wf m⌝ ∗
          ECommit.own t (DFrac.own 1) m ∗ ownReader br rd I (R ++ ECommit.enc m)) ∨
        (⌜err ≠ interface.nil⌝ ∗ rdErr rd err ∗ ∃ (v : src.gryffproto.ECommit) (R' : List w8),
          t ↦ v ∗ ownReader br rd I (R ++ R')) }} := by
  wp_start as ⟨#Hrd, #Hnext, Hown, Ht⟩
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Ht
  iStructNamed Ht
  irename : ("_" ∷ True : IProp GF) => Htrue
  iclear Htrue
  wp_auto
  have hts : go.typeSetContains (go.GoType.PointerType bufio.Reader.ty)
      src.gryffproto.byteReader.ty = true := by go_type_set
  simp only [hts, ↓reduceIte]
  wp_auto
  rw [show sint.Z (W64 0) = 0 from rfl, go.arrayIndexRef_0, show W64 12 - W64 0 = W64 12 from rfl,
    show W64 24 - W64 0 = W64 24 from rfl]
  ihave ⟨Hb, Hrest⟩ := array_prefix_slice (GF := GF) b_ptr (W64 12) (W64 24) 24
    (zero_val (GoArray w8 24)).arr (by decide) (by decide) $$ b
  wp_apply wp_wire_ReadAtLeast $$ [$Hrd $Hown $Hb] as %nr %err ⟨%data, Hown, Hr⟩
  icases Hr with (⟨⟨%Hnil, %Hlen⟩, Hb⟩ | ⟨%Hne, #Ha, %vs', Hb⟩)
  rotate_left
  · u1_ret_err (src.gryffproto.ECommit.mk _ _ _ _ _ _ _)
  subst Hnil
  have hl : data.length = 12 := by simpa using Hlen
  wp_auto
  repeat u1_wload
  ihave #Hvok := readNext_shift br rd I R data _ $$ Hnext
  ihave #Hvok := readNext_mono br rd I (R ++ data) _ vok
    (fun D Hn => ECommit.vok_of_next data D hl Hn) $$ Hvok
  wp_apply wp_ReadVarint br rd I (R ++ data) $$ [$Hrd $Hvok $Hown] as %x %err ⟨%V, Hown, Hr⟩
  · iexact Hpkg3
  icases Hr with (%Hok | #Ha)
  rotate_left
  · ihave %Hne := rdErr_ne _ _ $$ Ha
    u1_ret_err (src.gryffproto.ECommit.mk _ _ _ _ _ _ _)
  obtain ⟨rfl, ux, hV, rfl⟩ := Hok
  rw [List.append_assoc]
  imod ownReader_peek ECommit.nextOk br rd I R (data ++ V) $$ [Hnext Hown] with ⟨Hown, %Hpk⟩
  · iframe Hnext Hown
  obtain ⟨pend, Hpk⟩ := Hpk
  obtain ⟨len, hlen, hVlen⟩ := ECommit.pin data V pend hl
    (by rw [hV]; exact uvarintEnc_terminated _) (by simpa [List.append_assoc] using Hpk)
  have hux : uint.nat ux = 2 * len := uvarintEnc_inj (hV.symm.trans hVlen)
  have hx : (if ux &&& W64 1 = W64 0 then ux >>> W64 1 else ~~~(ux >>> W64 1)) = W64 len := by
    have h1 : ux &&& W64 1 = W64 0 := by
      apply BitVec.eq_of_toNat_eq
      simp only [uint.nat] at hux
      simp [BitVec.toNat_and, hux]
    rw [if_pos h1]
    apply BitVec.eq_of_toNat_eq
    simp only [uint.nat] at hux
    simp [hux]
    omega
  rw [hx]
  wp_auto
  have hlenZ : sint.Z (W64 (len : Int)) = len := encoding.binary.sint_W64_lit _ ⟨by omega, by omega⟩
  wp_apply (wp_slice_make2 (V := src.state.Command) (W64 (len : Int))) as %sl ⟨Hsl, -⟩
  · ipureintro; omega
  have hlenN : sint.nat (W64 (len : Int)) = len := by
    simp only [sint.nat, hlenZ]; simp
  rw [hlenN]
  ihave HL : (∃ (iv : w64) (cs : List src.state.Command),
      "i" ∷ i_ptr ↦ iv ∗
      "Hsl" ∷ sl ↦* (cs ++ List.replicate (len - cs.length) (zero_val src.state.Command)) ∗
      "Hown" ∷ ownReader br rd I (R ++ (data ++ V) ++ cs.flatMap state.Command.enc) ∗
      "%Hc" ∷ ⌜sint.Z iv = cs.length ∧ cs.length ≤ len⌝ : IProp GF) $$ [i Hsl Hown]
  · iexists W64 0, []
    simp only [List.length_nil, Nat.sub_zero, List.nil_append, List.flatMap_nil, List.append_nil]
    iframe
    ipureintro; exact ⟨rfl, Nat.zero_le _⟩
  wp_for HL
  obtain ⟨hiv, hcl⟩ := Hc
  ihave %Hsll := ownSlice_len _ _ _ $$ Hsl
  have hsl : sint.Z sl.len = len := by
    have h1 := Hsll.1
    simp only [List.length_append, List.length_replicate] at h1
    have h3 : ((sint.nat sl.len : Nat) : Int) = sint.Z sl.len := Int.toNat_of_nonneg Hsll.2
    omega
  wp_if_destruct
  · have hlt : cs.length < len := by rw [hlenZ, hiv] at Hif; omega
    rw [if_pos ⟨by omega, by omega⟩]
    have hlook : (cs ++ List.replicate (len - cs.length) (zero_val src.state.Command))[
        (sint.Z iv).toNat]? = some (zero_val src.state.Command) := by
      rw [hiv, Int.toNat_natCast, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self,
        List.getElem?_replicate]
      simp; omega
    icases ownSlice_elem_acc (sint.Z iv) (zero_val _) sl (DFrac.own 1) _ (by omega) hlook $$ Hsl
      with ⟨He, Hback⟩
    wp_auto
    wp_apply state.Command.wp_Unmarshal_proof $$ [$Hrd $Hown $He] as %err
      (⟨%Hnil, %mc, -, Hm, Hown⟩ | ⟨%Hne, #Ha, %vv, %R1, He, Hown⟩)
    · iapply readNext_true; intro; trivial
    · subst Hnil
      wp_auto
      wp_for_post
      iframe
      iexists iv + W64 1, cs ++ [mc]
      ihave Hsl := Hback $$ %mc Hm
      rw [hiv, Int.toNat_natCast, list_fill_step _ _ _ _ hlt, List.flatMap_append,
        List.flatMap_singleton]
      simp only [List.append_assoc]
      iframe
      ipureintro
      refine ⟨?_, by simp; omega⟩
      have : sint.Z (iv + W64 1) = sint.Z iv + 1 := by word
      rw [this, hiv]; simp
    · u1_ret_err (src.gryffproto.ECommit.mk _ _ _ _ _ _ _)
  -- after the loop: all `len` commands read
  have hcs : cs.length = len := by rw [hlenZ, hiv] at Hif; omega
  rw [hcs, Nat.sub_self, List.replicate_zero, List.append_nil]
  rw [show sint.Z (W64 0) = 0 from rfl, go.arrayIndexRef_0, show W64 24 - W64 0 = W64 24 from rfl]
  ihave Hb := array_of_prefix_slice (GF := GF) b_ptr (W64 12) (W64 24) _ data _ $$ [$Hb $Hrest]
  rw [show sint.Z (W64 12) + (24 - sint.Z (W64 12)) = (24 : Int) from rfl]
  ihave Hb := slice_array (GF := GF) b_ptr _ _ (by simp [hl, zero_arr_w8]; decide) $$ Hb
  wp_apply wp_wire_ReadAtLeast $$ [$Hrd $Hown $Hb] as %nr2 %err ⟨%data2, Hown, Hr⟩
  icases Hr with (⟨⟨%Hnil, %Hlen2⟩, Hb⟩ | ⟨%Hne, #Ha, %vs', Hb⟩)
  rotate_left
  · u1_ret_err (src.gryffproto.ECommit.mk _ _ _ _ _ _ _)
  subst Hnil
  have hl2 : data2.length = 24 := by simpa [hl] using Hlen2
  wp_auto
  repeat (first | u1_wload | u1_wstore_deps)
  wp_apply ValTag.wp_Unmarshal_proof $$ [$Hrd $Hown $Base] as %err
    (⟨%Hnil, %mb, -, HBase, Hown⟩ | ⟨%Hne, #Ha, %vb, %R2, Base, Hown⟩)
  · iapply readNext_true; intro; trivial
  rotate_left
  · u1_ret_err (src.gryffproto.ECommit.mk _ _ _ _ _ _ _)
  subst Hnil
  wp_auto
  ihave %Hdl := array_len _ _ _ _ $$ Deps
  icases pt_name _ _ _ $$ LeaderId with ⟨%xLeaderId, LeaderId, %hxLeaderId⟩
  icases pt_name _ _ _ $$ Replica with ⟨%xReplica, Replica, %hxReplica⟩
  icases pt_name _ _ _ $$ Instance with ⟨%xInstance, Instance, %hxInstance⟩
  icases pt_name _ _ _ $$ Seq with ⟨%seq, Seq, %hseq⟩
  icases pt_name _ _ _ $$ Deps with ⟨%deps, Deps, %hdeps⟩
  have e1 : data = u32Le xLeaderId ++ u32Le xReplica ++ u32Le xInstance := by
    subst hxLeaderId hxReplica hxInstance
    conv => lhs; rw [list_getD_eq data 12 hl]
    simp only [List.range_succ, List.range_zero, List.map_append, List.map_cons, List.map_nil,
      List.nil_append, List.cons_append, List.singleton_append, u32Le_dec, List.append_assoc]
  have e2 : data2 = u32Le seq ++ arrLe32 deps := by
    simp only [List.length_set] at Hdl
    subst hseq hdeps
    rw [set5 v0.Deps'.arr (by omega), arrLe32_5]
    conv => lhs; rw [list_getD_eq data2 24 hl2]
    simp only [List.range_succ, List.range_zero, List.map_append, List.map_cons, List.map_nil,
      List.nil_append, List.cons_append, List.singleton_append, u32Le_dec, List.append_assoc]
  iapply HΦ
  ileft
  isplitr
  · ipureintro; rfl
  iexists (ECommit.Msg.mk xLeaderId xReplica xInstance cs seq deps mb)
  isplitr
  · ipureintro; show cs.length < 2 ^ 63; omega
  isplitl [LeaderId Replica Instance Command Seq Deps Hsl HBase]
  · iunfold ECommit.own
    iexists sl
    iframe Hsl
    iapply typedPointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typedPointstoDef, ECommit.goVal]
    iframe
  iapply ownReader_eq _ _ _ _ _ ?_ $$ Hown
  rw [ECommit.enc, e1, e2, hVlen, hcs]
  simp only [varintEnc_len _ hlen, List.append_assoc]

set_option maxHeartbeats 4000000 in
theorem TryPreAccept.wp_Unmarshal_proof (t : Loc) (v0 : src.gryffproto.TryPreAccept) (br : Loc) (rd : RSt GF)
    (I : List w8 → IProp GF) (R : List w8) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ isPkgInit (PROP := IProp GF) pkg_id.io ∗
        readerOk rd I ∗ readNext br rd I R TryPreAccept.nextOk ∗
        ownReader br rd I R ∗ t ↦ v0 }}
      (App (Val (t @!! go.GoType.PointerType src.gryffproto.TryPreAccept.ty @!! go!"Unmarshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Reader.ty) #br)))
    {{ (err : GoInterface), RET #err;
        (⌜err = interface.nil⌝ ∗ ∃ m : TryPreAccept.Msg, ⌜TryPreAccept.wf m⌝ ∗
          TryPreAccept.own t (DFrac.own 1) m ∗ ownReader br rd I (R ++ TryPreAccept.enc m)) ∨
        (⌜err ≠ interface.nil⌝ ∗ rdErr rd err ∗ ∃ (v : src.gryffproto.TryPreAccept) (R' : List w8),
          t ↦ v ∗ ownReader br rd I (R ++ R')) }} := by
  wp_start as ⟨#Hrd, #Hnext, Hown, Ht⟩
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Ht
  iStructNamed Ht
  irename : ("_" ∷ True : IProp GF) => Htrue
  iclear Htrue
  wp_auto
  have hts : go.typeSetContains (go.GoType.PointerType bufio.Reader.ty)
      src.gryffproto.byteReader.ty = true := by go_type_set
  simp only [hts, ↓reduceIte]
  wp_auto
  rw [show sint.Z (W64 0) = 0 from rfl, go.arrayIndexRef_0, show W64 16 - W64 0 = W64 16 from rfl,
    show W64 24 - W64 0 = W64 24 from rfl]
  ihave ⟨Hb, Hrest⟩ := array_prefix_slice (GF := GF) b_ptr (W64 16) (W64 24) 24
    (zero_val (GoArray w8 24)).arr (by decide) (by decide) $$ b
  wp_apply wp_wire_ReadAtLeast $$ [$Hrd $Hown $Hb] as %nr %err ⟨%data, Hown, Hr⟩
  icases Hr with (⟨⟨%Hnil, %Hlen⟩, Hb⟩ | ⟨%Hne, #Ha, %vs', Hb⟩)
  rotate_left
  · u1_ret_err (src.gryffproto.TryPreAccept.mk _ _ _ _ _ _ _ _)
  subst Hnil
  have hl : data.length = 16 := by simpa using Hlen
  wp_auto
  repeat u1_wload
  ihave #Hvok := readNext_shift br rd I R data _ $$ Hnext
  ihave #Hvok := readNext_mono br rd I (R ++ data) _ vok
    (fun D Hn => TryPreAccept.vok_of_next data D hl Hn) $$ Hvok
  wp_apply wp_ReadVarint br rd I (R ++ data) $$ [$Hrd $Hvok $Hown] as %x %err ⟨%V, Hown, Hr⟩
  · iexact Hpkg3
  icases Hr with (%Hok | #Ha)
  rotate_left
  · ihave %Hne := rdErr_ne _ _ $$ Ha
    u1_ret_err (src.gryffproto.TryPreAccept.mk _ _ _ _ _ _ _ _)
  obtain ⟨rfl, ux, hV, rfl⟩ := Hok
  rw [List.append_assoc]
  imod ownReader_peek TryPreAccept.nextOk br rd I R (data ++ V) $$ [Hnext Hown] with ⟨Hown, %Hpk⟩
  · iframe Hnext Hown
  obtain ⟨pend, Hpk⟩ := Hpk
  obtain ⟨len, hlen, hVlen⟩ := TryPreAccept.pin data V pend hl
    (by rw [hV]; exact uvarintEnc_terminated _) (by simpa [List.append_assoc] using Hpk)
  have hux : uint.nat ux = 2 * len := uvarintEnc_inj (hV.symm.trans hVlen)
  have hx : (if ux &&& W64 1 = W64 0 then ux >>> W64 1 else ~~~(ux >>> W64 1)) = W64 len := by
    have h1 : ux &&& W64 1 = W64 0 := by
      apply BitVec.eq_of_toNat_eq
      simp only [uint.nat] at hux
      simp [BitVec.toNat_and, hux]
    rw [if_pos h1]
    apply BitVec.eq_of_toNat_eq
    simp only [uint.nat] at hux
    simp [hux]
    omega
  rw [hx]
  wp_auto
  have hlenZ : sint.Z (W64 (len : Int)) = len := encoding.binary.sint_W64_lit _ ⟨by omega, by omega⟩
  wp_apply (wp_slice_make2 (V := src.state.Command) (W64 (len : Int))) as %sl ⟨Hsl, -⟩
  · ipureintro; omega
  have hlenN : sint.nat (W64 (len : Int)) = len := by
    simp only [sint.nat, hlenZ]; simp
  rw [hlenN]
  ihave HL : (∃ (iv : w64) (cs : List src.state.Command),
      "i" ∷ i_ptr ↦ iv ∗
      "Hsl" ∷ sl ↦* (cs ++ List.replicate (len - cs.length) (zero_val src.state.Command)) ∗
      "Hown" ∷ ownReader br rd I (R ++ (data ++ V) ++ cs.flatMap state.Command.enc) ∗
      "%Hc" ∷ ⌜sint.Z iv = cs.length ∧ cs.length ≤ len⌝ : IProp GF) $$ [i Hsl Hown]
  · iexists W64 0, []
    simp only [List.length_nil, Nat.sub_zero, List.nil_append, List.flatMap_nil, List.append_nil]
    iframe
    ipureintro; exact ⟨rfl, Nat.zero_le _⟩
  wp_for HL
  obtain ⟨hiv, hcl⟩ := Hc
  ihave %Hsll := ownSlice_len _ _ _ $$ Hsl
  have hsl : sint.Z sl.len = len := by
    have h1 := Hsll.1
    simp only [List.length_append, List.length_replicate] at h1
    have h3 : ((sint.nat sl.len : Nat) : Int) = sint.Z sl.len := Int.toNat_of_nonneg Hsll.2
    omega
  wp_if_destruct
  · have hlt : cs.length < len := by rw [hlenZ, hiv] at Hif; omega
    rw [if_pos ⟨by omega, by omega⟩]
    have hlook : (cs ++ List.replicate (len - cs.length) (zero_val src.state.Command))[
        (sint.Z iv).toNat]? = some (zero_val src.state.Command) := by
      rw [hiv, Int.toNat_natCast, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self,
        List.getElem?_replicate]
      simp; omega
    icases ownSlice_elem_acc (sint.Z iv) (zero_val _) sl (DFrac.own 1) _ (by omega) hlook $$ Hsl
      with ⟨He, Hback⟩
    wp_auto
    wp_apply state.Command.wp_Unmarshal_proof $$ [$Hrd $Hown $He] as %err
      (⟨%Hnil, %mc, -, Hm, Hown⟩ | ⟨%Hne, #Ha, %vv, %R1, He, Hown⟩)
    · iapply readNext_true; intro; trivial
    · subst Hnil
      wp_auto
      wp_for_post
      iframe
      iexists iv + W64 1, cs ++ [mc]
      ihave Hsl := Hback $$ %mc Hm
      rw [hiv, Int.toNat_natCast, list_fill_step _ _ _ _ hlt, List.flatMap_append,
        List.flatMap_singleton]
      simp only [List.append_assoc]
      iframe
      ipureintro
      refine ⟨?_, by simp; omega⟩
      have : sint.Z (iv + W64 1) = sint.Z iv + 1 := by word
      rw [this, hiv]; simp
    · u1_ret_err (src.gryffproto.TryPreAccept.mk _ _ _ _ _ _ _ _)
  -- after the loop: all `len` commands read
  have hcs : cs.length = len := by rw [hlenZ, hiv] at Hif; omega
  rw [hcs, Nat.sub_self, List.replicate_zero, List.append_nil]
  rw [show sint.Z (W64 0) = 0 from rfl, go.arrayIndexRef_0, show W64 24 - W64 0 = W64 24 from rfl]
  ihave Hb := array_of_prefix_slice (GF := GF) b_ptr (W64 16) (W64 24) _ data _ $$ [$Hb $Hrest]
  rw [show sint.Z (W64 16) + (24 - sint.Z (W64 16)) = (24 : Int) from rfl]
  ihave Hb := slice_array (GF := GF) b_ptr _ _ (by simp [hl, zero_arr_w8]; decide) $$ Hb
  wp_apply wp_wire_ReadAtLeast $$ [$Hrd $Hown $Hb] as %nr2 %err ⟨%data2, Hown, Hr⟩
  icases Hr with (⟨⟨%Hnil, %Hlen2⟩, Hb⟩ | ⟨%Hne, #Ha, %vs', Hb⟩)
  rotate_left
  · u1_ret_err (src.gryffproto.TryPreAccept.mk _ _ _ _ _ _ _ _)
  subst Hnil
  have hl2 : data2.length = 24 := by simpa [hl] using Hlen2
  wp_auto
  repeat (first | u1_wload | u1_wstore_deps)
  wp_apply ValTag.wp_Unmarshal_proof $$ [$Hrd $Hown $Base] as %err
    (⟨%Hnil, %mb, -, HBase, Hown⟩ | ⟨%Hne, #Ha, %vb, %R2, Base, Hown⟩)
  · iapply readNext_true; intro; trivial
  rotate_left
  · u1_ret_err (src.gryffproto.TryPreAccept.mk _ _ _ _ _ _ _ _)
  subst Hnil
  wp_auto
  ihave %Hdl := array_len _ _ _ _ $$ Deps
  icases pt_name _ _ _ $$ LeaderId with ⟨%xLeaderId, LeaderId, %hxLeaderId⟩
  icases pt_name _ _ _ $$ Replica with ⟨%xReplica, Replica, %hxReplica⟩
  icases pt_name _ _ _ $$ Instance with ⟨%xInstance, Instance, %hxInstance⟩
  icases pt_name _ _ _ $$ Ballot with ⟨%xBallot, Ballot, %hxBallot⟩
  icases pt_name _ _ _ $$ Seq with ⟨%seq, Seq, %hseq⟩
  icases pt_name _ _ _ $$ Deps with ⟨%deps, Deps, %hdeps⟩
  have e1 : data = u32Le xLeaderId ++ u32Le xReplica ++ u32Le xInstance ++ u32Le xBallot := by
    subst hxLeaderId hxReplica hxInstance hxBallot
    conv => lhs; rw [list_getD_eq data 16 hl]
    simp only [List.range_succ, List.range_zero, List.map_append, List.map_cons, List.map_nil,
      List.nil_append, List.cons_append, List.singleton_append, u32Le_dec, List.append_assoc]
  have e2 : data2 = u32Le seq ++ arrLe32 deps := by
    simp only [List.length_set] at Hdl
    subst hseq hdeps
    rw [set5 v0.Deps'.arr (by omega), arrLe32_5]
    conv => lhs; rw [list_getD_eq data2 24 hl2]
    simp only [List.range_succ, List.range_zero, List.map_append, List.map_cons, List.map_nil,
      List.nil_append, List.cons_append, List.singleton_append, u32Le_dec, List.append_assoc]
  iapply HΦ
  ileft
  isplitr
  · ipureintro; rfl
  iexists (TryPreAccept.Msg.mk xLeaderId xReplica xInstance xBallot cs seq deps mb)
  isplitr
  · ipureintro; show cs.length < 2 ^ 63; omega
  isplitl [LeaderId Replica Instance Ballot Command Seq Deps Hsl HBase]
  · iunfold TryPreAccept.own
    iexists sl
    iframe Hsl
    iapply typedPointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typedPointstoDef, TryPreAccept.goVal]
    iframe
  iapply ownReader_eq _ _ _ _ _ ?_ $$ Hown
  rw [TryPreAccept.enc, e1, e2, hVlen, hcs]
  simp only [varintEnc_len _ hlen, List.append_assoc]

set_option maxHeartbeats 4000000 in
theorem PrepareReply.wp_Unmarshal_proof (t : Loc) (v0 : src.gryffproto.PrepareReply) (br : Loc) (rd : RSt GF)
    (I : List w8 → IProp GF) (R : List w8) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ isPkgInit (PROP := IProp GF) pkg_id.io ∗
        readerOk rd I ∗ readNext br rd I R PrepareReply.nextOk ∗
        ownReader br rd I R ∗ t ↦ v0 }}
      (App (Val (t @!! go.GoType.PointerType src.gryffproto.PrepareReply.ty @!! go!"Unmarshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Reader.ty) #br)))
    {{ (err : GoInterface), RET #err;
        (⌜err = interface.nil⌝ ∗ ∃ m : PrepareReply.Msg, ⌜PrepareReply.wf m⌝ ∗
          PrepareReply.own t (DFrac.own 1) m ∗ ownReader br rd I (R ++ PrepareReply.enc m)) ∨
        (⌜err ≠ interface.nil⌝ ∗ rdErr rd err ∗ ∃ (v : src.gryffproto.PrepareReply) (R' : List w8),
          t ↦ v ∗ ownReader br rd I (R ++ R')) }} := by
  wp_start as ⟨#Hrd, #Hnext, Hown, Ht⟩
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Ht
  iStructNamed Ht
  irename : ("_" ∷ True : IProp GF) => Htrue
  iclear Htrue
  wp_auto
  have hts : go.typeSetContains (go.GoType.PointerType bufio.Reader.ty)
      src.gryffproto.byteReader.ty = true := by go_type_set
  simp only [hts, ↓reduceIte]
  wp_auto
  rw [show sint.Z (W64 0) = 0 from rfl, go.arrayIndexRef_0, show W64 22 - W64 0 = W64 22 from rfl,
    show W64 24 - W64 0 = W64 24 from rfl]
  ihave ⟨Hb, Hrest⟩ := array_prefix_slice (GF := GF) b_ptr (W64 22) (W64 24) 24
    (zero_val (GoArray w8 24)).arr (by decide) (by decide) $$ b
  wp_apply wp_wire_ReadAtLeast $$ [$Hrd $Hown $Hb] as %nr %err ⟨%data, Hown, Hr⟩
  icases Hr with (⟨⟨%Hnil, %Hlen⟩, Hb⟩ | ⟨%Hne, #Ha, %vs', Hb⟩)
  rotate_left
  · u1_ret_err (src.gryffproto.PrepareReply.mk _ _ _ _ _ _ _ _ _ _ _)
  subst Hnil
  have hl : data.length = 22 := by simpa using Hlen
  wp_auto
  repeat u1_wload
  ihave #Hvok := readNext_shift br rd I R data _ $$ Hnext
  ihave #Hvok := readNext_mono br rd I (R ++ data) _ vok
    (fun D Hn => PrepareReply.vok_of_next data D hl Hn) $$ Hvok
  wp_apply wp_ReadVarint br rd I (R ++ data) $$ [$Hrd $Hvok $Hown] as %x %err ⟨%V, Hown, Hr⟩
  · iexact Hpkg3
  icases Hr with (%Hok | #Ha)
  rotate_left
  · ihave %Hne := rdErr_ne _ _ $$ Ha
    u1_ret_err (src.gryffproto.PrepareReply.mk _ _ _ _ _ _ _ _ _ _ _)
  obtain ⟨rfl, ux, hV, rfl⟩ := Hok
  rw [List.append_assoc]
  imod ownReader_peek PrepareReply.nextOk br rd I R (data ++ V) $$ [Hnext Hown] with ⟨Hown, %Hpk⟩
  · iframe Hnext Hown
  obtain ⟨pend, Hpk⟩ := Hpk
  obtain ⟨len, hlen, hVlen⟩ := PrepareReply.pin data V pend hl
    (by rw [hV]; exact uvarintEnc_terminated _) (by simpa [List.append_assoc] using Hpk)
  have hux : uint.nat ux = 2 * len := uvarintEnc_inj (hV.symm.trans hVlen)
  have hx : (if ux &&& W64 1 = W64 0 then ux >>> W64 1 else ~~~(ux >>> W64 1)) = W64 len := by
    have h1 : ux &&& W64 1 = W64 0 := by
      apply BitVec.eq_of_toNat_eq
      simp only [uint.nat] at hux
      simp [BitVec.toNat_and, hux]
    rw [if_pos h1]
    apply BitVec.eq_of_toNat_eq
    simp only [uint.nat] at hux
    simp [hux]
    omega
  rw [hx]
  wp_auto
  have hlenZ : sint.Z (W64 (len : Int)) = len := encoding.binary.sint_W64_lit _ ⟨by omega, by omega⟩
  wp_apply (wp_slice_make2 (V := src.state.Command) (W64 (len : Int))) as %sl ⟨Hsl, -⟩
  · ipureintro; omega
  have hlenN : sint.nat (W64 (len : Int)) = len := by
    simp only [sint.nat, hlenZ]; simp
  rw [hlenN]
  ihave HL : (∃ (iv : w64) (cs : List src.state.Command),
      "i" ∷ i_ptr ↦ iv ∗
      "Hsl" ∷ sl ↦* (cs ++ List.replicate (len - cs.length) (zero_val src.state.Command)) ∗
      "Hown" ∷ ownReader br rd I (R ++ (data ++ V) ++ cs.flatMap state.Command.enc) ∗
      "%Hc" ∷ ⌜sint.Z iv = cs.length ∧ cs.length ≤ len⌝ : IProp GF) $$ [i Hsl Hown]
  · iexists W64 0, []
    simp only [List.length_nil, Nat.sub_zero, List.nil_append, List.flatMap_nil, List.append_nil]
    iframe
    ipureintro; exact ⟨rfl, Nat.zero_le _⟩
  wp_for HL
  obtain ⟨hiv, hcl⟩ := Hc
  ihave %Hsll := ownSlice_len _ _ _ $$ Hsl
  have hsl : sint.Z sl.len = len := by
    have h1 := Hsll.1
    simp only [List.length_append, List.length_replicate] at h1
    have h3 : ((sint.nat sl.len : Nat) : Int) = sint.Z sl.len := Int.toNat_of_nonneg Hsll.2
    omega
  wp_if_destruct
  · have hlt : cs.length < len := by rw [hlenZ, hiv] at Hif; omega
    rw [if_pos ⟨by omega, by omega⟩]
    have hlook : (cs ++ List.replicate (len - cs.length) (zero_val src.state.Command))[
        (sint.Z iv).toNat]? = some (zero_val src.state.Command) := by
      rw [hiv, Int.toNat_natCast, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self,
        List.getElem?_replicate]
      simp; omega
    icases ownSlice_elem_acc (sint.Z iv) (zero_val _) sl (DFrac.own 1) _ (by omega) hlook $$ Hsl
      with ⟨He, Hback⟩
    wp_auto
    wp_apply state.Command.wp_Unmarshal_proof $$ [$Hrd $Hown $He] as %err
      (⟨%Hnil, %mc, -, Hm, Hown⟩ | ⟨%Hne, #Ha, %vv, %R1, He, Hown⟩)
    · iapply readNext_true; intro; trivial
    · subst Hnil
      wp_auto
      wp_for_post
      iframe
      iexists iv + W64 1, cs ++ [mc]
      ihave Hsl := Hback $$ %mc Hm
      rw [hiv, Int.toNat_natCast, list_fill_step _ _ _ _ hlt, List.flatMap_append,
        List.flatMap_singleton]
      simp only [List.append_assoc]
      iframe
      ipureintro
      refine ⟨?_, by simp; omega⟩
      have : sint.Z (iv + W64 1) = sint.Z iv + 1 := by word
      rw [this, hiv]; simp
    · u1_ret_err (src.gryffproto.PrepareReply.mk _ _ _ _ _ _ _ _ _ _ _)
  -- after the loop: all `len` commands read
  have hcs : cs.length = len := by rw [hlenZ, hiv] at Hif; omega
  rw [hcs, Nat.sub_self, List.replicate_zero, List.append_nil]
  rw [show sint.Z (W64 0) = 0 from rfl, go.arrayIndexRef_0, show W64 24 - W64 0 = W64 24 from rfl]
  ihave Hb := array_of_prefix_slice (GF := GF) b_ptr (W64 22) (W64 24) _ data _ $$ [$Hb $Hrest]
  rw [show sint.Z (W64 22) + (24 - sint.Z (W64 22)) = (24 : Int) from rfl]
  ihave Hb := slice_array (GF := GF) b_ptr _ _ (by simp [hl, zero_arr_w8]; decide) $$ Hb
  wp_apply wp_wire_ReadAtLeast $$ [$Hrd $Hown $Hb] as %nr2 %err ⟨%data2, Hown, Hr⟩
  icases Hr with (⟨⟨%Hnil, %Hlen2⟩, Hb⟩ | ⟨%Hne, #Ha, %vs', Hb⟩)
  rotate_left
  · u1_ret_err (src.gryffproto.PrepareReply.mk _ _ _ _ _ _ _ _ _ _ _)
  subst Hnil
  have hl2 : data2.length = 24 := by simpa [hl] using Hlen2
  wp_auto
  repeat (first | u1_wload | u1_wstore_deps)
  wp_apply ValTag.wp_Unmarshal_proof $$ [$Hrd $Hown $Base] as %err
    (⟨%Hnil, %mb, -, HBase, Hown⟩ | ⟨%Hne, #Ha, %vb, %R2, Base, Hown⟩)
  · iapply readNext_true; intro; trivial
  rotate_left
  · u1_ret_err (src.gryffproto.PrepareReply.mk _ _ _ _ _ _ _ _ _ _ _)
  subst Hnil
  wp_auto
  ihave %Hdl := array_len _ _ _ _ $$ Deps
  icases pt_name _ _ _ $$ AcceptorId with ⟨%xAcceptorId, AcceptorId, %hxAcceptorId⟩
  icases pt_name _ _ _ $$ Replica with ⟨%xReplica, Replica, %hxReplica⟩
  icases pt_name _ _ _ $$ Instance with ⟨%xInstance, Instance, %hxInstance⟩
  icases pt_name _ _ _ $$ OK with ⟨%xOK, OK, %hxOK⟩
  icases pt_name _ _ _ $$ Ballot with ⟨%xBallot, Ballot, %hxBallot⟩
  icases pt_name _ _ _ $$ VBallot with ⟨%xVBallot, VBallot, %hxVBallot⟩
  icases pt_name _ _ _ $$ Status with ⟨%xStatus, Status, %hxStatus⟩
  icases pt_name _ _ _ $$ Seq with ⟨%seq, Seq, %hseq⟩
  icases pt_name _ _ _ $$ Deps with ⟨%deps, Deps, %hdeps⟩
  have e1 : data = u32Le xAcceptorId ++ u32Le xReplica ++ u32Le xInstance ++ [xOK] ++ u32Le xBallot ++
      u32Le xVBallot ++ [xStatus] := by
    subst hxAcceptorId hxReplica hxInstance hxOK hxBallot hxVBallot hxStatus
    conv => lhs; rw [list_getD_eq data 22 hl]
    simp only [List.range_succ, List.range_zero, List.map_append, List.map_cons, List.map_nil,
      List.nil_append, List.cons_append, List.singleton_append, u32Le_dec, List.append_assoc]
  have e2 : data2 = u32Le seq ++ arrLe32 deps := by
    simp only [List.length_set] at Hdl
    subst hseq hdeps
    rw [set5 v0.Deps'.arr (by omega), arrLe32_5]
    conv => lhs; rw [list_getD_eq data2 24 hl2]
    simp only [List.range_succ, List.range_zero, List.map_append, List.map_cons, List.map_nil,
      List.nil_append, List.cons_append, List.singleton_append, u32Le_dec, List.append_assoc]
  iapply HΦ
  ileft
  isplitr
  · ipureintro; rfl
  iexists (PrepareReply.Msg.mk xAcceptorId xReplica xInstance xOK xBallot xVBallot xStatus cs seq deps mb)
  isplitr
  · ipureintro; show cs.length < 2 ^ 63; omega
  isplitl [AcceptorId Replica Instance OK Ballot VBallot Status Command Seq Deps Hsl HBase]
  · iunfold PrepareReply.own
    iexists sl
    iframe Hsl
    iapply typedPointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typedPointstoDef, PrepareReply.goVal]
    iframe
  iapply ownReader_eq _ _ _ _ _ ?_ $$ Hown
  rw [PrepareReply.enc, e1, e2, hVlen, hcs]
  simp only [varintEnc_len _ hlen, List.append_assoc]

end gryffproto
end uproofs
end Perennial.gryff.wire
