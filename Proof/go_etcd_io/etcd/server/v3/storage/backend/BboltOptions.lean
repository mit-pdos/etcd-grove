/-
bbolt's `Options` as the backend's constructor uses it. Lean-first (no Rocq counterpart);
2026-10-17, branch `construct`.

`newBackend` allocates an `Options` (`&bolt.Options{}`), copies `*boltOpenOptions` into it and
stores seven of its fields; this file states those operations' effects, over the points-to
`optsAt` (`BboltOptsDefs.lean`), for the part of an `Options` value bbolt's `Open` depends on
(`OptsM`).

**Lemmas** (2026-11-17, S2 of `notes/bbolt-integration-plan.md`, D-I4): `Options` is translated
(`Code/go_etcd_io/bbolt.toml`), the backend's `optsAt` is bbolt's (`Spec/go_etcd_io/bbolt/Options.lean`)
with `Mlock` and `MmapFlags` existential, and each law below is a corollary of bbolt's
(`Proof/go_etcd_io/bbolt/Options.lean`), with its statement unchanged. Until then these were
trust-boundary axioms over an abstract points-to (`Options` was axiomatized: `os.FileMode`, an alias
of `io/fs.FileMode`, was a translator gap).
- `optsAt l dq o`: the `Options` at `l` (fraction `dq`) has the fields `o` (and some others);
  `optsVal v o`: the Go value `v` is such an `Options`.
- `wp_optsLit`, `wp_optsAlloc`, `wp_optsLoad`, `wp_optsStore`: `bolt.Options{}` is the zero
  value (`optsZero`: not read-only, page size 0, no `OpenFile`, no logger), allocation, load and
  store of a whole value.
- `optsAt_bool`, `optsAt_int`, `optsAt_freelist`, `optsAt_timeout`, `optsAt_logger`: the typed
  points-to of a field; storing another field than `ReadOnly`, `PageSize`, `OpenFile` and `Logger`
  keeps `o`, storing `Logger` sets `o.logger`.

**What is still assumed**: `boltLogger l`, `l` is a `bolt.Logger` whose methods behave as bbolt's
calls need (they log; `Fatal`/`Panic` stop), abstract, given by `newBoltLoggerZap`'s axiom (zap is
names-only). It is not bbolt's own logger contract (`bbolt.boltLogger`, `Spec/go_etcd_io/bbolt/Logger.lean`)
yet: that one is stated over the file extension's instances (`[ExtSemantics fsExt] [FsSemOk]
[HasExt fsExt]`), which the backend's statements do not carry until the backend is ported onto
the proved bbolt (D-I1's `theFs`, S1).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.backend.InvBbolt
public import Proof.go_etcd_io.bbolt.Options

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace backend

open Iris Iris.BI Iris.ProofMode


section preds
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [bbolt_sem : go_etcd_io.bbolt.Assumptions]

/-- The `Options` value `v` has the fields `o` (bbolt's `optsVal`, whatever its `Mlock` and
`MmapFlags`). -/
def optsVal (v : go_etcd_io.bbolt.Options) (o : OptsM) : Prop :=
  ∃ (m : Bool) (f : w64), bbolt.optsVal v (o.toBolt m f)
/-- `l` is a `bolt.Logger` whose methods behave as bbolt's calls need. -/
axiom boltLogger (l : GoInterface) : IProp GF

@[instance] axiom boltLogger_persistent (l : GoInterface) : Persistent (boltLogger (GF := GF) l)
/-- `bolt.Options{}` is the zero value. -/
theorem wp_optsLit :
  {{ (True : IProp GF) }}
    (App (Val (GoInstruction (CompositeLiteral go_etcd_io.bbolt.Options.ty)))
      (Val (LiteralValueV [])))
  {{ (v : go_etcd_io.bbolt.Options), RET #v; ⌜optsVal v optsZero⌝ }} := by
  wp_start
  wp_apply_core bbolt.wp_optsLit
  iintro %v %hv
  iapply HΦ
  ipureintro
  exact ⟨false, W64 0, hv⟩

/-- A zero `Options` (what `wp_auto` makes of `&bolt.Options{}`, now that the type is
translated). -/
theorem optsAt_zero (l : Loc) :
    (l ↦ (zero_val go_etcd_io.bbolt.Options) : IProp GF) ⊢ optsAt l (DFrac.own 1) optsZero := by
  unfold optsAt
  iintro H
  ihave H := bbolt.optsAt_zero l $$ H
  rw [show bbolt.optsZero = optsZero.toBolt false (W64 0) from rfl]
  iexists false, W64 0
  iexact H

/-- Allocating an `Options` value. -/
theorem wp_optsAlloc (v : go_etcd_io.bbolt.Options) (o : OptsM) (h : optsVal v o) :
  {{ (True : IProp GF) }}
    (App (Val (GoInstruction (GoAlloc go_etcd_io.bbolt.Options.ty))) (Val #v))
  {{ (l : Loc), RET #l; optsAt l (DFrac.own 1) o }} := by
  unfold optsAt
  obtain ⟨m, f, h⟩ := h
  wp_start
  wp_apply_core (bbolt.wp_optsAlloc v _ h)
  iintro %l Hl
  iapply HΦ
  iexists m, f
  iexact Hl

/-- Loading an `Options` value. -/
theorem wp_optsLoad (l : Loc) (dq : DFrac) (o : OptsM) :
  {{ optsAt (GF := GF) l dq o }}
    (App (Val (GoInstruction (GoLoad go_etcd_io.bbolt.Options.ty))) (Val #l))
  {{ (v : go_etcd_io.bbolt.Options), RET #v; optsAt l dq o ∗ ⌜optsVal v o⌝ }} := by
  unfold optsAt
  wp_start as H
  icases H with ⟨%m, %f, H⟩
  wp_apply_core (bbolt.wp_optsLoad l dq _) $$ [$H]
  iintro %v ⟨H, %hv⟩
  iapply HΦ
  isplitl
  · iexists m, f; iexact H
  · ipureintro; exact ⟨m, f, hv⟩

/-- Storing an `Options` value. -/
theorem wp_optsStore (l : Loc) (o o' : OptsM) (v : go_etcd_io.bbolt.Options) (h : optsVal v o') :
  {{ optsAt (GF := GF) l (DFrac.own 1) o }}
    (App (Val (GoInstruction (GoStore go_etcd_io.bbolt.Options.ty))) (Val (PairV #l #v)))
  {{ RET #(); optsAt l (DFrac.own 1) o' }} := by
  unfold optsAt
  obtain ⟨m', f', h⟩ := h
  wp_start as H
  icases H with ⟨%m, %f, H⟩
  wp_apply_core (bbolt.wp_optsStore l _ _ v h) $$ [$H]
  iintro H
  iapply HΦ
  iexists m', f'
  iexact H

/-- A `bool` field other than `ReadOnly` (`db.go`: `NoGrowSync`, `NoFreelistSync`,
`PreLoadFreelist`, `NoSync`, `Mlock`, `NoStatistics`): storing it keeps `o`. -/
theorem optsAt_bool (l : Loc) (o : OptsM) (f : GoString)
    (hf : f = go!"NoGrowSync" ∨ f = go!"NoFreelistSync" ∨ f = go!"PreLoadFreelist" ∨
      f = go!"NoSync" ∨ f = go!"Mlock" ∨ f = go!"NoStatistics") :
  optsAt (GF := GF) l (DFrac.own 1) o ⊢
    ∃ x : Bool, structFieldRef go_etcd_io.bbolt.Options f l ↦ x ∗
      (∀ y : Bool, structFieldRef go_etcd_io.bbolt.Options f l ↦ y -∗ optsAt l (DFrac.own 1) o) := by
  unfold optsAt
  iintro ⟨%m, %fl, H⟩
  by_cases hm : f = go!"Mlock"
  · subst hm
    icases bbolt.optsAt_mlock l _ $$ H with ⟨Hf, Hback⟩
    iexists _
    iframe Hf
    iintro %y Hf
    ihave H := Hback $$ Hf
    rw [show ({ o.toBolt m fl with mlock := y } : bbolt.OptsM) = o.toBolt y fl from rfl]
    iexists y, fl
    iexact H
  · have hf' : f = go!"NoGrowSync" ∨ f = go!"NoFreelistSync" ∨ f = go!"PreLoadFreelist" ∨
        f = go!"NoSync" ∨ f = go!"NoStatistics" := by
      rcases hf with h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
      · exact absurd h hm
      · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
    icases bbolt.optsAt_bool l _ f hf' $$ H with ⟨%x, Hf, Hback⟩
    iexists x
    iframe Hf
    iintro %y Hf
    ihave H := Hback $$ Hf
    iexists m, fl
    iexact H

/-- An `int` field other than `PageSize` (`MmapFlags`, `InitialMmapSize`, `MaxSize`): storing it
keeps `o`. -/
theorem optsAt_int (l : Loc) (o : OptsM) (f : GoString)
    (hf : f = go!"MmapFlags" ∨ f = go!"InitialMmapSize" ∨ f = go!"MaxSize") :
  optsAt (GF := GF) l (DFrac.own 1) o ⊢
    ∃ x : w64, structFieldRef go_etcd_io.bbolt.Options f l ↦ x ∗
      (∀ y : w64, structFieldRef go_etcd_io.bbolt.Options f l ↦ y -∗ optsAt l (DFrac.own 1) o) := by
  unfold optsAt
  iintro ⟨%m, %fl, H⟩
  rcases hf with hm | hf'
  · subst hm
    icases bbolt.optsAt_mmapFlags l _ $$ H with ⟨Hf, Hback⟩
    iexists _
    iframe Hf
    iintro %y Hf
    ihave H := Hback $$ Hf
    rw [show ({ o.toBolt m fl with mmapFlags := y } : bbolt.OptsM) = o.toBolt m y from rfl]
    iexists m, y
    iexact H
  · icases bbolt.optsAt_int l _ f hf' $$ H with ⟨%x, Hf, Hback⟩
    iexists x
    iframe Hf
    iintro %y Hf
    ihave H := Hback $$ Hf
    iexists m, fl
    iexact H

/-- The `FreelistType` field: storing it keeps `o`. -/
theorem optsAt_freelist (l : Loc) (o : OptsM) :
  optsAt (GF := GF) l (DFrac.own 1) o ⊢
    ∃ x : go_etcd_io.bbolt.FreelistType,
      structFieldRef go_etcd_io.bbolt.Options go!"FreelistType" l ↦ x ∗
      (∀ y : go_etcd_io.bbolt.FreelistType,
        structFieldRef go_etcd_io.bbolt.Options go!"FreelistType" l ↦ y -∗
          optsAt l (DFrac.own 1) o) := by
  unfold optsAt
  iintro ⟨%m, %fl, H⟩
  icases bbolt.optsAt_freelist l _ $$ H with ⟨%x, Hf, Hback⟩
  iexists x
  iframe Hf
  iintro %y Hf
  ihave H := Hback $$ Hf
  iexists m, fl
  iexact H

/-- The `Timeout` field: storing it keeps `o`. -/
theorem optsAt_timeout (l : Loc) (o : OptsM) :
  optsAt (GF := GF) l (DFrac.own 1) o ⊢
    ∃ x : time.Duration, structFieldRef go_etcd_io.bbolt.Options go!"Timeout" l ↦ x ∗
      (∀ y : time.Duration, structFieldRef go_etcd_io.bbolt.Options go!"Timeout" l ↦ y -∗
        optsAt l (DFrac.own 1) o) := by
  unfold optsAt
  iintro ⟨%m, %fl, H⟩
  icases bbolt.optsAt_timeout l _ $$ H with ⟨%x, Hf, Hback⟩
  iexists x
  iframe Hf
  iintro %y Hf
  ihave H := Hback $$ Hf
  iexists m, fl
  iexact H

/-- The `Logger` field: it holds `o.logger`; storing it sets it. -/
theorem optsAt_logger (l : Loc) (o : OptsM) :
  optsAt (GF := GF) l (DFrac.own 1) o ⊢
    structFieldRef go_etcd_io.bbolt.Options go!"Logger" l ↦ (o.logger : go_etcd_io.bbolt.Logger) ∗
      (∀ y : go_etcd_io.bbolt.Logger, structFieldRef go_etcd_io.bbolt.Options go!"Logger" l ↦ y -∗
        optsAt l (DFrac.own 1) { o with logger := y }) := by
  unfold optsAt
  iintro ⟨%m, %fl, H⟩
  icases bbolt.optsAt_logger l _ $$ H with ⟨Hf, Hback⟩
  rw [show (o.toBolt m fl).logger = o.logger from rfl]
  iframe Hf
  iintro %y Hf
  ihave H := Hback $$ Hf
  rw [show ({ o.toBolt m fl with logger := y } : bbolt.OptsM) =
    ({ o with logger := y } : OptsM).toBolt m fl from rfl]
  iexists m, fl
  iexact H

end preds


end backend
end EtcdGrove
end Perennial
