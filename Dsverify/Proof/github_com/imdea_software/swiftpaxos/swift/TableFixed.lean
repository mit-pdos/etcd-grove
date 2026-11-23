/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/TableFixed.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
The swift table's fixed-size entries and the entries no peer sends:

* `MNewLeader.Unmarshal` (8 bytes, over any reader with `readsOk`);
* `unmarshalOk`/`newOk` of `MLightSlowAck` (12, the client's `MLightSlowAck.Unmarshal` proof),
  `MNewLeader` (16), and of `MSlowAck` (11), `MPing` (19), `MPingRep` (20), `MCollect` (21),
  `MAccept` (22) (vacuous: no well-formed message has their type).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.TableBase

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

namespace swift.tbl

section specs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics]

/-- `(*MNewLeader).Unmarshal(rd)`: the next 8 bytes. -/
abbrev MNewLeader.Unmarshal.specI : Prop :=
  ∀ (t : Loc) (v : swift.MNewLeader) (rd : GoInterface) (I : List w8 → IProp netDistGF)
    (R : List w8),
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.io ∗ bufio.readsOk rd I ∗ I R ∗ t ↦ v }}
    (App (Val (t @!! go.GoType.PointerType swift.MNewLeader.ty @!! go!"Unmarshal")) (Val #rd))
  {{ (err : GoInterface), RET #err; ∃ data : List w8, I (R ++ data) ∗
      ((⌜err = interface.nil⌝ ∗ ∃ r b : w32, ⌜data = sp.le32 r ++ sp.le32 b⌝ ∗
          t ↦ swift.MNewLeader.mk r b) ∨
        (⌜err ≠ interface.nil⌝ ∗ ∃ v' : swift.MNewLeader, t ↦ v')) }}

end specs

section proofs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics]
variable [swift.Assumptions] [io.Assumptions] [errors.Assumptions]
  [bufio.Assumptions]

set_option goose.wp.extras true

set_option hygiene false in
/-- Load `bs[0..7]` of the slice `Hsl`. -/
macro "rd_ld8" : tactic => `(tactic| (
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
  · iframe Hsl; ipureintro; rfl
  try wp_auto))

theorem MNewLeader.Unmarshal.wp_proof : MNewLeader.Unmarshal.specI (hG := hG) := by
  intro t v rd I R
  wp_start as ⟨#Hrd, HI, Ht⟩
  try wp_auto
  ihave Hsl := slice_array b_ptr 8 (Perennial.zero_val (GoArray w8 8)) (by decide) $$ b
  rw [show sint.Z (W64 0) = 0 from rfl, go.arrayIndexRef_0, show W64 8 - W64 0 = W64 8 from rfl]
  rw [show (Perennial.zero_val (GoArray w8 8)).arr = List.replicate 8 (W8 0) from rfl]
  wp_apply bufio.wp_ReadAtLeast rd I R _ (List.replicate 8 (W8 0)) (W64 8) ?_ $$
    [$Hpkg $Hrd $HI $Hsl] as %n %err ⟨%data, %Hd, Hsl, HI, #He⟩
  obtain ⟨hn, hdl, herr⟩ := Hd
  rcases err with e | _
  · wp_auto
    iapply HΦ
    iexists data
    iframe HI
    iright
    isplitr
    · ipureintro; intro h; cases h
    iexists v
    iexact Ht
  · have h8 : data.length = 8 := by
      have := herr.1 rfl; simp at hdl; have : sint.Z (W64 8) = 8 := rfl; omega
    obtain ⟨d0, d1, d2, d3, d4, d5, d6, d7, rfl⟩ :
        ∃ d0 d1 d2 d3 d4 d5 d6 d7 : w8, data = [d0, d1, d2, d3, d4, d5, d6, d7] := by
      match data, h8 with
      | [d0, d1, d2, d3, d4, d5, d6, d7], _ => exact ⟨d0, d1, d2, d3, d4, d5, d6, d7, rfl⟩
    isimp only [List.length_cons, List.length_nil, List.drop_replicate, List.append_nil,
      Nat.reduceAdd, Nat.sub_self, List.replicate_zero] at Hsl
    wp_auto
    rd_ld8
    iapply HΦ
    iexists _
    iframe HI
    ileft
    isplitr
    · ipureintro; rfl
    iexists leToU32 [d0, d1, d2, d3], leToU32 [d4, d5, d6, d7]
    isplitr
    · ipureintro
      simp only [sp.le32]
      rw [leToU32_le _ rfl, leToU32_le _ rfl]
      rfl
    iExactEq Ht
    simp only [encoding.binary.leToU32_4]

/-! ## The entries -/

theorem wp_New_MNewLeader (o : Loc) :
    {{ (True : IProp netDistGF) }}
      (App (Val (o @!! go.GoType.PointerType swift.MNewLeader.ty @!! go!"New")) (Val #()))
    {{ (l : Loc), RET #(interface.mkOk (go.GoType.PointerType swift.MNewLeader.ty) #l);
        l ↦ (zero_val swift.MNewLeader) }} := by
  wp_start
  wp_auto
  wp_alloc_auto
  wp_auto
  iapply HΦ; iframe

theorem wp_New_MLightSlowAck (o : Loc) :
    {{ (True : IProp netDistGF) }}
      (App (Val (o @!! go.GoType.PointerType swift.MLightSlowAck.ty @!! go!"New")) (Val #()))
    {{ (l : Loc), RET #(interface.mkOk (go.GoType.PointerType swift.MLightSlowAck.ty) #l);
        l ↦ (zero_val swift.MLightSlowAck) }} := by
  wp_start
  wp_auto
  wp_alloc_auto
  wp_auto
  iapply HΦ; iframe

/-- The persistent facts the fixed-size entries' `Unmarshal`s use. -/
def ctxIO : IProp netDistGF :=
  iprop(isPkgInit (PROP := IProp netDistGF) pkg_id.io ∗
    isPkgInit (PROP := IProp netDistGF) pkg_id.bufio)

instance ctxIO_persistent : Persistent (ctxIO (hG := hG)) := by
  unfold ctxIO; infer_instance

theorem unmarshalOk_lightSlowAck (l : Loc) (v : swift.MLightSlowAck) :
    ctxIO ∗ l ↦ v ⊢ sp.unmarshalOk (W8 12) (swift.msgRep (W8 12))
      (interface.mkOk (go.GoType.PointerType swift.MLightSlowAck.ty) #l) := by
  unfold ctxIO
  iintro ⟨⟨#Hio, #Hbuf⟩, Hl⟩
  unfold sp.unmarshalOk
  iexists _
  isplitr
  · ipureintro; rfl
  iintro %br %rd %I %R %Φ #Hrd - Hown HΦ
  ihave #Hrs := bufio.bufioReadsOk br rd I $$ [$Hbuf $Hrd]
  wp_apply swift.rd.MLightSlowAck.Unmarshal.wp_proof l v _ (bufio.ownReader br rd I) R $$
    [$Hio $Hrs $Hown $Hl] as %err ⟨%data, Hown, Hres⟩
  icases Hres with (⟨%He, %s, %Hd, Hl⟩ | ⟨%He, -⟩)
  · iapply HΦ $$ Hown
    ileft
    isplitr
    · ipureintro; exact He
    iexists .lightSlowAck s
    isplitr
    · ipureintro; subst Hd; exact sp.decodes_of_body rfl trivial
    unfold swift.msgRep swift.msgRepM
    iexists l, _
    iframe Hl
    ipureintro
    exact ⟨rfl, rfl, rfl, rfl⟩
  · iapply HΦ $$ Hown
    iright
    ipureintro; exact He

theorem unmarshalOk_newLeader (l : Loc) (v : swift.MNewLeader) :
    ctxIO ∗ l ↦ v ⊢ sp.unmarshalOk (W8 16) (swift.msgRep (W8 16))
      (interface.mkOk (go.GoType.PointerType swift.MNewLeader.ty) #l) := by
  unfold ctxIO
  iintro ⟨⟨#Hio, #Hbuf⟩, Hl⟩
  unfold sp.unmarshalOk
  iexists _
  isplitr
  · ipureintro; rfl
  iintro %br %rd %I %R %Φ #Hrd - Hown HΦ
  ihave #Hrs := bufio.bufioReadsOk br rd I $$ [$Hbuf $Hrd]
  wp_apply MNewLeader.Unmarshal.wp_proof l v _ (bufio.ownReader br rd I) R $$
    [$Hio $Hrs $Hown $Hl] as %err ⟨%data, Hown, Hres⟩
  icases Hres with (⟨%He, %r, %b, %Hd, Hl⟩ | ⟨%He, -⟩)
  · iapply HΦ $$ Hown
    ileft
    isplitr
    · ipureintro; exact He
    iexists .newLeader r b
    isplitr
    · ipureintro; subst Hd; exact sp.decodes_of_body rfl trivial
    unfold swift.msgRep swift.msgRepM
    iexists l
    iframe Hl
    ipureintro; rfl
  · iapply HΦ $$ Hown
    iright
    ipureintro; exact He

theorem newOk_lightSlowAck (o : Loc) :
    ctxIO ⊢ sp.newOk (W8 12) (swift.msgRep (W8 12))
      (interface.mkOk (go.GoType.PointerType swift.MLightSlowAck.ty) #o) := by
  apply newOk_of _ _ _ o ctxIO (fun l => iprop(l ↦ (zero_val swift.MLightSlowAck)))
  · iintro %Φ - HΦ
    iapply wp_New_MLightSlowAck o $$ [] HΦ
    itrivial
  · intro l; exact unmarshalOk_lightSlowAck l _

theorem newOk_newLeader (o : Loc) :
    ctxIO ⊢ sp.newOk (W8 16) (swift.msgRep (W8 16))
      (interface.mkOk (go.GoType.PointerType swift.MNewLeader.ty) #o) := by
  apply newOk_of _ _ _ o ctxIO (fun l => iprop(l ↦ (zero_val swift.MNewLeader)))
  · iintro %Φ - HΦ
    iapply wp_New_MNewLeader o $$ [] HΦ
    itrivial
  · intro l; exact unmarshalOk_newLeader l _

/-- The entry of a type no peer sends: `New` returns some object, whose `Unmarshal` is never
reached. -/
theorem newOk_unused (c : w8) (hc : ∀ m : sp.Msg, m.code ≠ c) (ty : go.GoType) (o : Loc)
    (hnew : {{ (True : IProp netDistGF) }}
      (App (Val (o @!! go.GoType.PointerType ty @!! go!"New")) (Val #()))
      {{ (l : Loc), RET #(interface.mkOk (go.GoType.PointerType ty) #l); True }}) :
    ⊢ sp.newOk c (swift.msgRep c) (interface.mkOk (go.GoType.PointerType ty) #o) := by
  iapply newOk_of c _ ty o iprop(True) (fun _ => iprop(True))
  · iintro %Φ - HΦ
    iapply hnew $$ [] HΦ
    itrivial
  · intro l
    iintro -
    iapply unmarshalOk_vacuous c hc
  · itrivial

theorem code_ne_11 : ∀ m : sp.Msg, m.code ≠ W8 11 := by
  intro m; cases m <;> simp [sp.Msg.code, sp.rpcTable]
theorem code_ne_19 : ∀ m : sp.Msg, m.code ≠ W8 19 := by
  intro m; cases m <;> simp [sp.Msg.code, sp.rpcTable]
theorem code_ne_20 : ∀ m : sp.Msg, m.code ≠ W8 20 := by
  intro m; cases m <;> simp [sp.Msg.code, sp.rpcTable]
theorem code_ne_21 : ∀ m : sp.Msg, m.code ≠ W8 21 := by
  intro m; cases m <;> simp [sp.Msg.code, sp.rpcTable]
theorem code_ne_22 : ∀ m : sp.Msg, m.code ≠ W8 22 := by
  intro m; cases m <;> simp [sp.Msg.code, sp.rpcTable]

theorem newOk_MSlowAck (o : Loc) :
    ⊢ sp.newOk (W8 11) (swift.msgRep (W8 11))
      (interface.mkOk (go.GoType.PointerType swift.MSlowAck.ty) #o) := by
  apply newOk_unused _ code_ne_11 _ o
  wp_start
  wp_auto
  wp_alloc_auto
  wp_auto
  iapply HΦ; itrivial

theorem newOk_MPing (o : Loc) :
    ⊢ sp.newOk (W8 19) (swift.msgRep (W8 19))
      (interface.mkOk (go.GoType.PointerType swift.MPing.ty) #o) := by
  apply newOk_unused _ code_ne_19 _ o
  wp_start
  wp_auto
  wp_alloc_auto
  wp_auto
  iapply HΦ; itrivial

theorem newOk_MPingRep (o : Loc) :
    ⊢ sp.newOk (W8 20) (swift.msgRep (W8 20))
      (interface.mkOk (go.GoType.PointerType swift.MPingRep.ty) #o) := by
  apply newOk_unused _ code_ne_20 _ o
  wp_start
  wp_auto
  wp_alloc_auto
  wp_auto
  iapply HΦ; itrivial

theorem newOk_MCollect (o : Loc) :
    ⊢ sp.newOk (W8 21) (swift.msgRep (W8 21))
      (interface.mkOk (go.GoType.PointerType swift.MCollect.ty) #o) := by
  apply newOk_unused _ code_ne_21 _ o
  wp_start
  wp_auto
  wp_alloc_auto
  wp_auto
  iapply HΦ; itrivial

theorem newOk_MAccept (o : Loc) :
    ⊢ sp.newOk (W8 22) (swift.msgRep (W8 22))
      (interface.mkOk (go.GoType.PointerType swift.MAccept.ty) #o) := by
  apply newOk_unused _ code_ne_22 _ o
  wp_start
  wp_auto
  wp_alloc_auto
  wp_auto
  iapply HΦ; itrivial

end proofs

end swift.tbl

end Perennial.github_com.imdea_software.swiftpaxos
