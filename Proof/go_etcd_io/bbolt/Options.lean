/-
bbolt's `Options` laws (the frozen spec of 2026-11-03, `notes/bbolt-spec-decisions.md`, D13):
the operations clients and `Open` perform on an `Options` (the literal, allocation, whole loads
and stores, field reads and stores), over the points-to `optsAt` (`Spec/go_etcd_io/bbolt/Options.lean`),
for the part of the value `Open` depends on (`OptsM`).

(2026-11-17, S2 of `notes/bbolt-integration-plan.md`, D-I4) `Options` is translated (`bbolt.toml`),
so `optsAt` is the struct's typed points-to and these laws, trust-boundary axioms until then (the
type was axiomatized, its generated instances `sorry`), are lemmas, with unchanged statements.

**D13** (the user's decision): `OptsM` tracks `mlock` and `mmapFlags` too (`OptsM.ok` excludes
`Mlock` and `MmapFlags` other than `0` or `MAP_POPULATE`, scope restrictions of the model), so
`optsAt_bool` and `optsAt_int` do not cover them, and `optsAt_mlock`/`optsAt_mmapFlags` set them.
The read laws (`optsAt_*_rd`) and `optsAt_nonnull` are what `Open` needs; the backend's laws
(`Proof/go_etcd_io/etcd/server/v3/storage/backend/BboltOptions.lean`) are corollaries of these.
-/
module

public import Spec.go_etcd_io.bbolt.Options

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt


open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- The typed points-to of an `Options`, field by field (its generated `TypedPointsto` instance). -/
theorem optsPt_eq (l : Loc) (v : go_etcd_io.bbolt.Options) (dq : DFrac) :
    (l ↦{dq} v : IProp GF) ⊣⊢ iprop((
      structFieldRef go_etcd_io.bbolt.Options go!"Timeout" l ↦{dq} v.Timeout' ∗
      structFieldRef go_etcd_io.bbolt.Options go!"NoGrowSync" l ↦{dq} v.NoGrowSync' ∗
      structFieldRef go_etcd_io.bbolt.Options go!"NoFreelistSync" l ↦{dq} v.NoFreelistSync' ∗
      structFieldRef go_etcd_io.bbolt.Options go!"PreLoadFreelist" l ↦{dq} v.PreLoadFreelist' ∗
      structFieldRef go_etcd_io.bbolt.Options go!"FreelistType" l ↦{dq} v.FreelistType' ∗
      structFieldRef go_etcd_io.bbolt.Options go!"ReadOnly" l ↦{dq} v.ReadOnly' ∗
      structFieldRef go_etcd_io.bbolt.Options go!"MmapFlags" l ↦{dq} v.MmapFlags' ∗
      structFieldRef go_etcd_io.bbolt.Options go!"InitialMmapSize" l ↦{dq} v.InitialMmapSize' ∗
      structFieldRef go_etcd_io.bbolt.Options go!"PageSize" l ↦{dq} v.PageSize' ∗
      structFieldRef go_etcd_io.bbolt.Options go!"MaxSize" l ↦{dq} v.MaxSize' ∗
      structFieldRef go_etcd_io.bbolt.Options go!"NoSync" l ↦{dq} v.NoSync' ∗
      structFieldRef go_etcd_io.bbolt.Options go!"OpenFile" l ↦{dq} v.OpenFile' ∗
      structFieldRef go_etcd_io.bbolt.Options go!"Mlock" l ↦{dq} v.Mlock' ∗
      structFieldRef go_etcd_io.bbolt.Options go!"Logger" l ↦{dq} v.Logger' ∗
      structFieldRef go_etcd_io.bbolt.Options go!"NoStatistics" l ↦{dq} v.NoStatistics' ∗
      True) ∗ ⌜l ≠ Loc.null⌝) := by
  rw [typedPointsto_unseal_eq]; exact .rfl

/-- An `Options` the laws describe is never nil (a typed points-to's location is not). -/
theorem optsAt_nonnull (l : Loc) (dq : DFrac) (o : OptsM) :
    optsAt (GF := GF) l dq o ⊢ ⌜l ≠ Loc.null⌝ := by
  unfold optsAt
  iintro ⟨%v, Hv, -⟩
  icases (optsPt_eq l v dq).1 $$ Hv with ⟨-, %Hnn⟩
  ipureintro; exact Hnn

/-- A field read through an `AccessStrict` instance of the struct's points-to, giving `optsAt`
back. -/
theorem optsAt_acc {A : go_etcd_io.bbolt.Options → IProp GF} (l : Loc) (dq : DFrac) (o : OptsM)
    (h : ∀ v, AccessStrict (A v) (A v) (l ↦{dq} v) (l ↦{dq} v)) :
    optsAt (GF := GF) l dq o ⊢ ∃ v, ⌜optsVal v o⌝ ∗ A v ∗ (A v -∗ optsAt l dq o) := by
  unfold optsAt
  iintro ⟨%v, Hv, %hv⟩
  ihave ⟨HA, Hback⟩ := (h v).access_strict $$ Hv
  iexists v
  isplitr
  · ipureintro; exact hv
  iframe HA
  iintro HA
  ihave Hv := Hback $$ HA
  iexists v
  iframe Hv
  ipureintro; exact hv

/-! ### Reads at any fraction (round 4: what `Open` needs) -/

/-- Reading a tracked field at any fraction gives its `OptsM` value (round 4). One law per
field, by its Go type: -/
theorem optsAt_readOnly_rd (l : Loc) (dq : DFrac) (o : OptsM) :
  optsAt (GF := GF) l dq o ⊢ ∃ dq' : DFrac,
    structFieldRef go_etcd_io.bbolt.Options go!"ReadOnly" l ↦{dq'} o.readOnly ∗
    (structFieldRef go_etcd_io.bbolt.Options go!"ReadOnly" l ↦{dq'} o.readOnly -∗ optsAt l dq o) := by
  iintro H
  icases optsAt_acc l dq o (fun v => Options.access_load'Options'ReadOnly l v dq) $$ H with
    ⟨%v, %hv, Hf, Hback⟩
  iexists dq
  rw [← hv.1]
  iframe Hf; iexact Hback
theorem optsAt_mlock_rd (l : Loc) (dq : DFrac) (o : OptsM) :
  optsAt (GF := GF) l dq o ⊢ ∃ dq' : DFrac,
    structFieldRef go_etcd_io.bbolt.Options go!"Mlock" l ↦{dq'} o.mlock ∗
    (structFieldRef go_etcd_io.bbolt.Options go!"Mlock" l ↦{dq'} o.mlock -∗ optsAt l dq o) := by
  iintro H
  icases optsAt_acc l dq o (fun v => Options.access_load'Options'Mlock l v dq) $$ H with
    ⟨%v, %hv, Hf, Hback⟩
  iexists dq
  rw [← hv.2.2.2.2.1]
  iframe Hf; iexact Hback
theorem optsAt_pageSize_rd (l : Loc) (dq : DFrac) (o : OptsM) :
  optsAt (GF := GF) l dq o ⊢ ∃ dq' : DFrac,
    structFieldRef go_etcd_io.bbolt.Options go!"PageSize" l ↦{dq'} o.pageSize ∗
    (structFieldRef go_etcd_io.bbolt.Options go!"PageSize" l ↦{dq'} o.pageSize -∗ optsAt l dq o) := by
  iintro H
  icases optsAt_acc l dq o (fun v => Options.access_load'Options'PageSize l v dq) $$ H with
    ⟨%v, %hv, Hf, Hback⟩
  iexists dq
  rw [← hv.2.1]
  iframe Hf; iexact Hback
theorem optsAt_mmapFlags_rd (l : Loc) (dq : DFrac) (o : OptsM) :
  optsAt (GF := GF) l dq o ⊢ ∃ dq' : DFrac,
    structFieldRef go_etcd_io.bbolt.Options go!"MmapFlags" l ↦{dq'} o.mmapFlags ∗
    (structFieldRef go_etcd_io.bbolt.Options go!"MmapFlags" l ↦{dq'} o.mmapFlags -∗ optsAt l dq o) := by
  iintro H
  icases optsAt_acc l dq o (fun v => Options.access_load'Options'MmapFlags l v dq) $$ H with
    ⟨%v, %hv, Hf, Hback⟩
  iexists dq
  rw [← hv.2.2.2.2.2]
  iframe Hf; iexact Hback
theorem optsAt_openFile_rd (l : Loc) (dq : DFrac) (o : OptsM) :
  optsAt (GF := GF) l dq o ⊢ ∃ dq' : DFrac,
    structFieldRef go_etcd_io.bbolt.Options go!"OpenFile" l ↦{dq'} o.openFile ∗
    (structFieldRef go_etcd_io.bbolt.Options go!"OpenFile" l ↦{dq'} o.openFile -∗ optsAt l dq o) := by
  iintro H
  icases optsAt_acc l dq o (fun v => Options.access_load'Options'OpenFile l v dq) $$ H with
    ⟨%v, %hv, Hf, Hback⟩
  iexists dq
  rw [← hv.2.2.1]
  iframe Hf; iexact Hback
theorem optsAt_logger_rd (l : Loc) (dq : DFrac) (o : OptsM) :
  optsAt (GF := GF) l dq o ⊢ ∃ dq' : DFrac,
    structFieldRef go_etcd_io.bbolt.Options go!"Logger" l ↦{dq'}
      (o.logger : go_etcd_io.bbolt.Logger) ∗
    (structFieldRef go_etcd_io.bbolt.Options go!"Logger" l ↦{dq'}
      (o.logger : go_etcd_io.bbolt.Logger) -∗ optsAt l dq o) := by
  iintro H
  icases optsAt_acc l dq o (fun v => Options.access_load'Options'Logger l v dq) $$ H with
    ⟨%v, %hv, Hf, Hback⟩
  iexists dq
  rw [← hv.2.2.2.1]
  iframe Hf; iexact Hback

/-- Reading an untracked `bool` field at any fraction: some value (round 4; round 5: one law
per Go type, `db.go`'s declarations). -/
theorem optsAt_bool_rd (l : Loc) (dq : DFrac) (o : OptsM) (f : GoString)
    (hf : f = go!"NoGrowSync" ∨ f = go!"NoFreelistSync" ∨ f = go!"PreLoadFreelist" ∨
      f = go!"NoSync" ∨ f = go!"NoStatistics") :
  optsAt (GF := GF) l dq o ⊢ ∃ (dq' : DFrac) (x : Bool),
    structFieldRef go_etcd_io.bbolt.Options f l ↦{dq'} x ∗
    (structFieldRef go_etcd_io.bbolt.Options f l ↦{dq'} x -∗ optsAt l dq o) := by
  iintro H
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · icases optsAt_acc l dq o (fun v => Options.access_load'Options'NoGrowSync l v dq) $$ H with
      ⟨%v, -, Hf, Hback⟩
    iexists dq, _; iframe Hf; iexact Hback
  · icases optsAt_acc l dq o (fun v => Options.access_load'Options'NoFreelistSync l v dq) $$ H with
      ⟨%v, -, Hf, Hback⟩
    iexists dq, _; iframe Hf; iexact Hback
  · icases optsAt_acc l dq o (fun v => Options.access_load'Options'PreLoadFreelist l v dq) $$ H with
      ⟨%v, -, Hf, Hback⟩
    iexists dq, _; iframe Hf; iexact Hback
  · icases optsAt_acc l dq o (fun v => Options.access_load'Options'NoSync l v dq) $$ H with
      ⟨%v, -, Hf, Hback⟩
    iexists dq, _; iframe Hf; iexact Hback
  · icases optsAt_acc l dq o (fun v => Options.access_load'Options'NoStatistics l v dq) $$ H with
      ⟨%v, -, Hf, Hback⟩
    iexists dq, _; iframe Hf; iexact Hback

/-- Reading an untracked `int` field (`InitialMmapSize`, `MaxSize`) at any fraction. -/
theorem optsAt_int_rd (l : Loc) (dq : DFrac) (o : OptsM) (f : GoString)
    (hf : f = go!"InitialMmapSize" ∨ f = go!"MaxSize") :
  optsAt (GF := GF) l dq o ⊢ ∃ (dq' : DFrac) (x : w64),
    structFieldRef go_etcd_io.bbolt.Options f l ↦{dq'} x ∗
    (structFieldRef go_etcd_io.bbolt.Options f l ↦{dq'} x -∗ optsAt l dq o) := by
  iintro H
  rcases hf with rfl | rfl
  · icases optsAt_acc l dq o (fun v => Options.access_load'Options'InitialMmapSize l v dq) $$ H with
      ⟨%v, -, Hf, Hback⟩
    iexists dq, _; iframe Hf; iexact Hback
  · icases optsAt_acc l dq o (fun v => Options.access_load'Options'MaxSize l v dq) $$ H with
      ⟨%v, -, Hf, Hback⟩
    iexists dq, _; iframe Hf; iexact Hback

/-- Reading `FreelistType` at any fraction. -/
theorem optsAt_freelist_rd (l : Loc) (dq : DFrac) (o : OptsM) :
  optsAt (GF := GF) l dq o ⊢ ∃ (dq' : DFrac) (x : go_etcd_io.bbolt.FreelistType),
    structFieldRef go_etcd_io.bbolt.Options go!"FreelistType" l ↦{dq'} x ∗
    (structFieldRef go_etcd_io.bbolt.Options go!"FreelistType" l ↦{dq'} x -∗ optsAt l dq o) := by
  iintro H
  icases optsAt_acc l dq o (fun v => Options.access_load'Options'FreelistType l v dq) $$ H with
    ⟨%v, -, Hf, Hback⟩
  iexists dq, _; iframe Hf; iexact Hback

/-- Reading `Timeout` at any fraction. -/
theorem optsAt_timeout_rd (l : Loc) (dq : DFrac) (o : OptsM) :
  optsAt (GF := GF) l dq o ⊢ ∃ (dq' : DFrac) (x : time.Duration),
    structFieldRef go_etcd_io.bbolt.Options go!"Timeout" l ↦{dq'} x ∗
    (structFieldRef go_etcd_io.bbolt.Options go!"Timeout" l ↦{dq'} x -∗ optsAt l dq o) := by
  iintro H
  icases optsAt_acc l dq o (fun v => Options.access_load'Options'Timeout l v dq) $$ H with
    ⟨%v, -, Hf, Hback⟩
  iexists dq, _; iframe Hf; iexact Hback

/-! ### Whole values: the literal, allocation, load, store -/

/-- The zero value has the fields `optsZero` (`bolt.Options{}`). -/
theorem optsVal_zero : optsVal (zero_val go_etcd_io.bbolt.Options) optsZero :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- A zero `Options` (what `wp_auto` makes of `&bolt.Options{}`, now that the type is translated). -/
theorem optsAt_zero (l : Loc) :
    (l ↦ (zero_val go_etcd_io.bbolt.Options) : IProp GF) ⊢ optsAt l (DFrac.own 1) optsZero := by
  unfold optsAt
  iintro H
  iexists _
  iframe H
  ipureintro; exact optsVal_zero

/-- `bolt.Options{}` is the zero value. -/
theorem wp_optsLit :
  {{ (True : IProp GF) }}
    (App (Val (GoInstruction (CompositeLiteral go_etcd_io.bbolt.Options.ty)))
      (Val (LiteralValueV [])))
  {{ (v : go_etcd_io.bbolt.Options), RET #v; ⌜optsVal v optsZero⌝ }} := by
  wp_start
  wp_auto
  iapply HΦ
  ipureintro
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Allocating an `Options` value. -/
theorem wp_optsAlloc (v : go_etcd_io.bbolt.Options) (o : OptsM) (h : optsVal v o) :
  {{ (True : IProp GF) }}
    (App (Val (GoInstruction (GoAlloc go_etcd_io.bbolt.Options.ty))) (Val #v))
  {{ (l : Loc), RET #l; optsAt l (DFrac.own 1) o }} := by
  wp_start
  wp_apply_core (IntoValTyped.wp_alloc (t := go_etcd_io.bbolt.Options.ty) v)
  iintro %l Hl
  iapply HΦ
  unfold optsAt
  iexists v
  iframe Hl
  ipureintro; exact h

/-- Loading an `Options` value. -/
theorem wp_optsLoad (l : Loc) (dq : DFrac) (o : OptsM) :
  {{ optsAt (GF := GF) l dq o }}
    (App (Val (GoInstruction (GoLoad go_etcd_io.bbolt.Options.ty))) (Val #l))
  {{ (v : go_etcd_io.bbolt.Options), RET #v; optsAt l dq o ∗ ⌜optsVal v o⌝ }} := by
  wp_start as H
  unfold optsAt
  icases H with ⟨%v, Hv, %hv⟩
  wp_apply_core (IntoValTyped.wp_load (t := go_etcd_io.bbolt.Options.ty) l dq v) $$ [$Hv]
  iintro Hv
  iapply HΦ
  isplitl
  · iexists v; iframe Hv; ipureintro; exact hv
  · ipureintro; exact hv

/-- Storing an `Options` value. -/
theorem wp_optsStore (l : Loc) (o o' : OptsM) (v : go_etcd_io.bbolt.Options) (h : optsVal v o') :
  {{ optsAt (GF := GF) l (DFrac.own 1) o }}
    (App (Val (GoInstruction (GoStore go_etcd_io.bbolt.Options.ty))) (Val (PairV #l #v)))
  {{ RET #(); optsAt l (DFrac.own 1) o' }} := by
  wp_start as H
  unfold optsAt
  icases H with ⟨%v0, Hv, -⟩
  wp_apply_core (IntoValTyped.wp_store (t := go_etcd_io.bbolt.Options.ty) l v0 v) $$ [$Hv]
  iintro Hv
  iapply HΦ
  iexists v
  iframe Hv
  ipureintro; exact h

/-! ### Field stores (full ownership) -/

/-- A `bool` field other than `ReadOnly` and `Mlock` (`NoGrowSync`, `NoFreelistSync`,
`PreLoadFreelist`, `NoSync`, `NoStatistics`): storing it keeps `o`. (Round 3: `Mlock` moved out.) -/
theorem optsAt_bool (l : Loc) (o : OptsM) (f : GoString)
    (hf : f = go!"NoGrowSync" ∨ f = go!"NoFreelistSync" ∨ f = go!"PreLoadFreelist" ∨
      f = go!"NoSync" ∨ f = go!"NoStatistics") :
  optsAt (GF := GF) l (DFrac.own 1) o ⊢
    ∃ x : Bool, structFieldRef go_etcd_io.bbolt.Options f l ↦ x ∗
      (∀ y : Bool, structFieldRef go_etcd_io.bbolt.Options f l ↦ y -∗ optsAt l (DFrac.own 1) o) := by
  unfold optsAt
  iintro ⟨%v, Hv, %hv⟩
  icases (optsPt_eq l v _).1 $$ Hv with
    ⟨⟨H1, H2, H3, H4, H5, H6, H7, H8, H9, H10, H11, H12, H13, H14, H15, -⟩, %Hnn⟩
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · iexists _; iframe H2; iintro %y H2; iexists { v with NoGrowSync' := y }
    isplitl; · iapply (optsPt_eq l _ _).2; iframe; ipureintro; exact Hnn
    ipureintro; exact hv
  · iexists _; iframe H3; iintro %y H3; iexists { v with NoFreelistSync' := y }
    isplitl; · iapply (optsPt_eq l _ _).2; iframe; ipureintro; exact Hnn
    ipureintro; exact hv
  · iexists _; iframe H4; iintro %y H4; iexists { v with PreLoadFreelist' := y }
    isplitl; · iapply (optsPt_eq l _ _).2; iframe; ipureintro; exact Hnn
    ipureintro; exact hv
  · iexists _; iframe H11; iintro %y H11; iexists { v with NoSync' := y }
    isplitl; · iapply (optsPt_eq l _ _).2; iframe; ipureintro; exact Hnn
    ipureintro; exact hv
  · iexists _; iframe H15; iintro %y H15; iexists { v with NoStatistics' := y }
    isplitl; · iapply (optsPt_eq l _ _).2; iframe; ipureintro; exact Hnn
    ipureintro; exact hv

/-- The `Mlock` field (round 3): it holds `o.mlock`; storing it sets it. -/
theorem optsAt_mlock (l : Loc) (o : OptsM) :
  optsAt (GF := GF) l (DFrac.own 1) o ⊢
    structFieldRef go_etcd_io.bbolt.Options go!"Mlock" l ↦ o.mlock ∗
      (∀ y : Bool, structFieldRef go_etcd_io.bbolt.Options go!"Mlock" l ↦ y -∗
        optsAt l (DFrac.own 1) { o with mlock := y }) := by
  unfold optsAt
  iintro ⟨%v, Hv, %hv⟩
  icases (optsPt_eq l v _).1 $$ Hv with
    ⟨⟨H1, H2, H3, H4, H5, H6, H7, H8, H9, H10, H11, H12, H13, H14, H15, -⟩, %Hnn⟩
  rw [← hv.2.2.2.2.1]
  iframe H13; iintro %y H13; iexists { v with Mlock' := y }
  isplitl; · iapply (optsPt_eq l _ _).2; iframe; ipureintro; exact Hnn
  ipureintro
  obtain ⟨h1, h2, h3, h4, -, h6⟩ := hv
  exact ⟨h1, h2, h3, h4, rfl, h6⟩

/-- An `int` field other than `PageSize` and `MmapFlags` (`InitialMmapSize`, `MaxSize`): storing
it keeps `o`. (Round 3: `MmapFlags` moved out.) -/
theorem optsAt_int (l : Loc) (o : OptsM) (f : GoString)
    (hf : f = go!"InitialMmapSize" ∨ f = go!"MaxSize") :
  optsAt (GF := GF) l (DFrac.own 1) o ⊢
    ∃ x : w64, structFieldRef go_etcd_io.bbolt.Options f l ↦ x ∗
      (∀ y : w64, structFieldRef go_etcd_io.bbolt.Options f l ↦ y -∗ optsAt l (DFrac.own 1) o) := by
  unfold optsAt
  iintro ⟨%v, Hv, %hv⟩
  icases (optsPt_eq l v _).1 $$ Hv with
    ⟨⟨H1, H2, H3, H4, H5, H6, H7, H8, H9, H10, H11, H12, H13, H14, H15, -⟩, %Hnn⟩
  rcases hf with rfl | rfl
  · iexists _; iframe H8; iintro %y H8; iexists { v with InitialMmapSize' := y }
    isplitl; · iapply (optsPt_eq l _ _).2; iframe; ipureintro; exact Hnn
    ipureintro; exact hv
  · iexists _; iframe H10; iintro %y H10; iexists { v with MaxSize' := y }
    isplitl; · iapply (optsPt_eq l _ _).2; iframe; ipureintro; exact Hnn
    ipureintro; exact hv

/-- The `MmapFlags` field (round 3): it holds `o.mmapFlags`; storing it sets it. -/
theorem optsAt_mmapFlags (l : Loc) (o : OptsM) :
  optsAt (GF := GF) l (DFrac.own 1) o ⊢
    structFieldRef go_etcd_io.bbolt.Options go!"MmapFlags" l ↦ o.mmapFlags ∗
      (∀ y : w64, structFieldRef go_etcd_io.bbolt.Options go!"MmapFlags" l ↦ y -∗
        optsAt l (DFrac.own 1) { o with mmapFlags := y }) := by
  unfold optsAt
  iintro ⟨%v, Hv, %hv⟩
  icases (optsPt_eq l v _).1 $$ Hv with
    ⟨⟨H1, H2, H3, H4, H5, H6, H7, H8, H9, H10, H11, H12, H13, H14, H15, -⟩, %Hnn⟩
  rw [← hv.2.2.2.2.2]
  iframe H7; iintro %y H7; iexists { v with MmapFlags' := y }
  isplitl; · iapply (optsPt_eq l _ _).2; iframe; ipureintro; exact Hnn
  ipureintro
  obtain ⟨h1, h2, h3, h4, h5, -⟩ := hv
  exact ⟨h1, h2, h3, h4, h5, rfl⟩

/-- The `FreelistType` field: storing it keeps `o`. -/
theorem optsAt_freelist (l : Loc) (o : OptsM) :
  optsAt (GF := GF) l (DFrac.own 1) o ⊢
    ∃ x : go_etcd_io.bbolt.FreelistType,
      structFieldRef go_etcd_io.bbolt.Options go!"FreelistType" l ↦ x ∗
      (∀ y : go_etcd_io.bbolt.FreelistType,
        structFieldRef go_etcd_io.bbolt.Options go!"FreelistType" l ↦ y -∗
          optsAt l (DFrac.own 1) o) := by
  unfold optsAt
  iintro ⟨%v, Hv, %hv⟩
  icases (optsPt_eq l v _).1 $$ Hv with
    ⟨⟨H1, H2, H3, H4, H5, H6, H7, H8, H9, H10, H11, H12, H13, H14, H15, -⟩, %Hnn⟩
  iexists _; iframe H5; iintro %y H5; iexists { v with FreelistType' := y }
  isplitl; · iapply (optsPt_eq l _ _).2; iframe; ipureintro; exact Hnn
  ipureintro; exact hv

/-- The `Timeout` field: storing it keeps `o`. -/
theorem optsAt_timeout (l : Loc) (o : OptsM) :
  optsAt (GF := GF) l (DFrac.own 1) o ⊢
    ∃ x : time.Duration, structFieldRef go_etcd_io.bbolt.Options go!"Timeout" l ↦ x ∗
      (∀ y : time.Duration, structFieldRef go_etcd_io.bbolt.Options go!"Timeout" l ↦ y -∗
        optsAt l (DFrac.own 1) o) := by
  unfold optsAt
  iintro ⟨%v, Hv, %hv⟩
  icases (optsPt_eq l v _).1 $$ Hv with
    ⟨⟨H1, H2, H3, H4, H5, H6, H7, H8, H9, H10, H11, H12, H13, H14, H15, -⟩, %Hnn⟩
  iexists _; iframe H1; iintro %y H1; iexists { v with Timeout' := y }
  isplitl; · iapply (optsPt_eq l _ _).2; iframe; ipureintro; exact Hnn
  ipureintro; exact hv

/-- The `Logger` field: it holds `o.logger`; storing it sets it. -/
theorem optsAt_logger (l : Loc) (o : OptsM) :
  optsAt (GF := GF) l (DFrac.own 1) o ⊢
    structFieldRef go_etcd_io.bbolt.Options go!"Logger" l ↦ (o.logger : go_etcd_io.bbolt.Logger) ∗
      (∀ y : go_etcd_io.bbolt.Logger, structFieldRef go_etcd_io.bbolt.Options go!"Logger" l ↦ y -∗
        optsAt l (DFrac.own 1) { o with logger := y }) := by
  unfold optsAt
  iintro ⟨%v, Hv, %hv⟩
  icases (optsPt_eq l v _).1 $$ Hv with
    ⟨⟨H1, H2, H3, H4, H5, H6, H7, H8, H9, H10, H11, H12, H13, H14, H15, -⟩, %Hnn⟩
  rw [← hv.2.2.2.1]
  iframe H14; iintro %y H14; iexists { v with Logger' := y }
  isplitl; · iapply (optsPt_eq l _ _).2; iframe; ipureintro; exact Hnn
  ipureintro
  obtain ⟨h1, h2, h3, -, h5, h6⟩ := hv
  exact ⟨h1, h2, h3, rfl, h5, h6⟩

end lemmas

end bbolt
end EtcdGrove
end Perennial
