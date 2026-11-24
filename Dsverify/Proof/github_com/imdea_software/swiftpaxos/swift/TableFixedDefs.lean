/-
The definitions, specs and lemmas of `TableFixed.lean` that its proofs do not need (split out for the import tiers, CLAUDE.md "Import tiers": its importers that are not linking modules import this module, and see no proof).
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
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF]

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
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF] [SwiftKitDeps]
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
