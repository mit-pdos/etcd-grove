/-
**`raftpb.HardState` as a registered protobuf message type at its wire content** (wal-fsfix2 item 3,
option (a), approved by the user 2026-11-20 via etcd-grove-03: the pattern of `walpb.Snapshot`'s
`PbSnapshot.lean`), so that `proto.MarshalPb.spec` covers `pbutil.MustMarshalMessage` of a hard state
(`WalPbIn.MarshalHsLaw`, `RaftModel/LawsHsMarshal.lean`).

- The wire content is `WalHsC` (`RaftModel/Codec.lean`): `Term`, `Vote`, `Commit` nil or set, the
  unknown fields; its model `WalHsC.model` (what the getters read).
- `hsRoC l c` (`RaftModel/Pb.lean`): a frozen `*raftpb.HardState` holding exactly `c`, its hidden fields
  in raft's `protobuf` invariant (`pbMsg`, at `pbSchemaOf raftpb.HardState.ty = hsSchema`).
- `hsDecC l c`: the decoded object, owned whole (`hsOwnC`), its unknown fields valid at `hsSchema`.
- **The encoder is a transparent Lean function** (`hsEnc`, `RaftModel/Codec.lean`), the decoder
  `hsDecode` opaque, the size `hsSize c` the encoding's length.

**Trusted** (as for every registered type):
- `hsSchema` (`PbSchema.lean`, `raft.proto:101-105`: `term` 1, `vote` 2, `commit` 3, varints), in
  `pbSchemaOf`'s table;
- `hsEncC_ok`: protobuf-go decodes `hsEnc c` back to `c`'s model when the unknown fields are valid at
  `hsSchema`. Measured: `examples/stdlib/walpb/hardstate_test.go` (`TestHardStateEncoder`: 200,000
  random contents, `proto.Marshal`/`proto.Size` against `hsEnc` and its length, `proto.Unmarshal(hsEnc c)`
  giving back exactly `c`, its getters `WalHsC.model`, the unknown fields from `genUFAt`: numbers 1-40,
  minimal tags, no groups; `TestHardStateSchema`: the descriptor against `hsSchema`;
  `hardstate_adv_test.go`, from the independent attack: `TestHardStateEncoderAllUf`, the same at unknown
  fields that are any `ufWire`-valid bytes, groups and large numbers included, and `TestHardStateD1`, the
  decoder's post D1 of `UnmarshalPb.lean` at `HardState` on 1,000,000 adversarial inputs); the descriptor
  check `etc/pbschema-check.py` reads `hsSchema` as a root's, with its negative tests;
- `pbHsC_reg`: the registration, of the exact shape `pbModelOf GF raftpb.HardState.ty = some …`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.wal.RaftModel.Pb
public import Proof.google_golang_org.protobuf.proto.Store

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3 WalEnc

/-- **The size of a hard state's encoding**: its length (`proto.Size`, tested against it). -/
def hsSize [GooseExts] (c : WalHsC) : Nat := (hsEnc c).length

/-- **Decoding a `raftpb.HardState`'s bytes** (opaque: `proto.Unmarshal`): the model, or `none`. -/
opaque hsDecode [GooseExts] (bs : List w8) : Option HardStateM

/-- **The trust boundary: `raftpb.HardState`'s encoding** (see the file header). -/
axiom hsEncC_ok [GooseExts] (c : WalHsC) : ufWire hsSchema c.uf → hsSize c < 2 ^ 63 →
    hsDecode (hsEnc c) = some c.model

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- A frozen hard state's unknown fields are valid at `hsSchema`. -/
theorem hsRoC_uf (l : Loc) (c : WalHsC) : hsRoC (GF := GF) l c ⊢ ⌜ufWire hsSchema c.uf⌝ := by
  unfold hsRoC
  iintro ⟨-, Hpb⟩
  ihave %H := pbMsg_ufWire (GF := GF) raftpb.HardState l c.uf $$ Hpb
  ipureintro
  rwa [show PbGoType.goTy raftpb.HardState = raftpb.HardState.ty from rfl, pbSchemaOf_hardState] at H

/-- **A decoded `*raftpb.HardState` at `l` holding exactly `c`, owned whole** (as `snapOwnC`: the
decoded message is fresh, and protobuf-go keeps no reference to it after `Unmarshal` returns), its
unknown fields valid at `hsSchema`. -/
def hsDecC (l : Loc) (c : WalHsC) : IProp GF :=
  iprop(hsOwnC l c ∗ ⌜ufWire hsSchema c.uf⌝)

/-- **The store of a hard state** (each scalar `nil` if zero). -/
def hsTree (m : HardStateM) : VTree :=
  .strct raftpb.HardState.ty
    [(go!"Term", go.GoType.PointerType go.uint64), (go!"Vote", go.GoType.PointerType go.uint64),
     (go!"Commit", go.GoType.PointerType go.uint64)]
    [cellTree go.uint64 m.Term', cellTree go.uint64 m.Vote', cellTree go.uint64 m.Commit']

/-- **`raftpb.HardState` at its wire content: the data** (no axiom). -/
def pbHsM : PbModelC GF where
  ty := raftpb.HardState.ty
  M := HardStateM
  ro l m := iprop(∃ c, hsRoC l c ∗ ⌜c.model = m⌝)
  ro_persistent _ _ := inferInstance
  marshals _ := True
  wire m bs := hsDecode bs = some m
  eqv m m' := m = m'
  blank l := iprop(l ↦ (zero_val raftpb.HardState))
  dec l m := iprop(∃ c, hsDecC l c ∗ ⌜c.model = m⌝)
  C := WalHsC
  roC := hsRoC
  roC_persistent _ _ := inferInstance
  modelOf := WalHsC.model
  levels c := [(hsSchema, c.uf)]
  size := hsSize
  tree := hsTree
  decOk _ := True
  ro_iff _ _ := .rfl
  roC_ufValid l c := by
    iintro #H
    ihave %Hu := hsRoC_uf l c $$ H
    ipureintro
    intro p hp
    rw [List.mem_singleton] at hp
    subst hp
    exact Hu
  decC l c := hsDecC l c
  decC_dec l c _ := by
    iintro H
    iexists c
    iframe H
    ipureintro; rfl

/-- **`raftpb.HardState` at its wire content** (the registered instance): the data and the encoder
`hsEnc`, whose `enc_ok` is `hsEncC_ok`. -/
def pbHsC : PbTypeC GF where
  data := pbHsM
  encd := { enc := hsEnc
            enc_ok := fun c _ hu hs => ⟨hsEncC_ok c (hu _ (List.mem_singleton.2 rfl)) hs, rfl⟩ }

@[simp] theorem pbEncC_pbHsC (c : WalHsC) : pbEncC (pbHsC (GF := GF)) c = hsEnc c := rfl
@[simp] theorem pbHsC_ty : (pbHsC (GF := GF)).data.ty = raftpb.HardState.ty := rfl
@[simp] theorem pbHsC_roC : (pbHsC (GF := GF)).data.roC = hsRoC := rfl
@[simp] theorem pbHsC_C : (pbHsC (GF := GF)).data.C = WalHsC := rfl
@[simp] theorem pbHsC_modelOf : (pbHsC (GF := GF)).data.modelOf = WalHsC.model := rfl
@[simp] theorem pbHsC_size : (pbHsC (GF := GF)).data.size = hsSize := rfl
@[simp] theorem pbHsC_marshals (m : HardStateM) : (pbHsC (GF := GF)).data.marshals m = True := rfl
@[simp] theorem pbHsC_decC (l : Loc) (c : WalHsC) : (pbHsC (GF := GF)).data.decC l c = hsDecC l c := rfl

end defs

/-- **The registration** of `pbHsC` (exact shape). -/
axiom pbHsC_reg [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext]
    {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [go.Semantics] :
    pbModelOf GF raftpb.HardState.ty = some (pbHsC (GF := GF))

/-! ## `Sat` (the model-param gate's rule 7) -/

section sat
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.raftpb.Assumptions]
variable [package_sem' : go_etcd_io.raft.v3.Assumptions]

/-- **A hard state's struct literal**: its value, which, stored anywhere, is a decoded hard state at
some wire content with the model `m`. -/
theorem treeWp_hsTree (m : HardStateM) (Φ : val → IProp GF) :
    (∀ x : raftpb.HardState, (∀ p : Loc, p ↦ x ={⊤}=∗ ∃ c, hsDecC p c ∗ ⌜c.model = m⌝) -∗
      Φ #x) ⊢
      treeWp (hsTree m) Φ := by
  iintro H
  simp only [hsTree, treeWp, treeWpL]
  iapply treeWp_cell
  iintro %pt Hpt
  isplitr
  · ipureintro; exact isPanic_intoVal pt
  iapply treeWp_cell
  iintro %pv Hpv
  isplitr
  · ipureintro; exact isPanic_intoVal pv
  iapply treeWp_cell
  iintro %pc Hpc
  isplitr
  · ipureintro; exact isPanic_intoVal pc
  simp [litBody, strctKes, kesσ, envσ]
  wp_auto
  iapply H
  iintro %l Hl
  ihave %Hnn := typedPointsto_not_null $$ Hl
  icases typedPointsto_split _ _ _ $$ Hl with Hl
  simp only [TypedPointsto.typedPointstoDef]
  icases Hl with ⟨HS, HT, HV, HC, HU, HSC, -⟩
  ihave Hnil := ownSlice_nil (V := w8) (GF := GF) (DFrac.own 1)
  imod optCell_freeze pt m.Term' $$ Hpt with ⟨%o1, #c1, %h1⟩
  imod optCell_freeze pv m.Vote' $$ Hpv with ⟨%o2, #c2, %h2⟩
  imod optCell_freeze pc m.Commit' $$ Hpc with ⟨%o3, #c3, %h3⟩
  imodintro
  iexists ⟨o1, o2, o3, []⟩
  unfold hsDecC hsOwnC
  isplitl
  · isplitl
    · iexists pt, pv, pc, _, _, _
      isplitr
      · ipureintro; exact Hnn
      simp only
      iframe
      isplitr; · iexact c1
      isplitr; · iexact c2
      isplitr; · iexact c3
      iexact Hnil
    · ipureintro; exact ufWire_nil _
  · ipureintro
    cases m
    simp only [WalHsC.model] at h1 h2 h3 ⊢
    rw [← h1, ← h2, ← h3]
    rfl

/-- **`pbHsC`'s decoded model is satisfiable** by the generic store. -/
theorem pbHsC_sat : (pbHsM (GF := GF)).Sat := by
  refine ⟨⟨raftpb.HardState, inferInstance, inferInstance,
    (inferInstance : IntoValTyped raftpb.HardState raftpb.HardState.ty), fun l => .rfl⟩, ?_⟩
  intro m l
  simp only [pbHsM]
  iintro Hl
  iapply wp_fupd
  iapply (storeInto_wp_typed (V := raftpb.HardState) (ty := raftpb.HardState.ty) l
    (zero_val raftpb.HardState))
  iapply (treeWp_hsTree (GF := GF) m)
  iintro %x Hx
  iexists x
  isplitr
  · ipureintro; rfl
  iframe Hl
  iintro Hl
  iapply Hx $$ Hl

end sat

end EtcdGrove
end Perennial
