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
public import Spec.go_etcd_io.bbolt.Logger

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

/-- **`l` is a `bolt.Logger` whose methods behave as bbolt's calls need**: bbolt's own contract
(`bbolt.boltLogger`, `Spec/go_etcd_io/bbolt/Logger.lean`) at the program's file-extension instances
(`theFs`), and `True` where there are none (S3e, 2026-11-17: until then an axiom, abstract; its
meaning is what `newBoltLoggerZap`'s axiom claims of etcd's zap logger, as bbolt's `Logger.lean`
already said). -/
def boltLogger (l : GoInterface) : IProp GF :=
  match theFs GF with
  | some c => letI := c.S; letI := c.ok; letI := c.has; bbolt.boltLogger l
  | none => iprop(True)

@[instance] theorem boltLogger_persistent (l : GoInterface) :
    Persistent (boltLogger (GF := GF) l) := by
  unfold boltLogger; split <;> infer_instance

/-- The backend's logger contract is bbolt's, at the instances. -/
theorem boltLogger_eq [S : ExtSemantics Fs.fsExt] [ok : Fs.FsSemOk] [has : HasExt Fs.fsExt]
 [FsNoErrAll] (l : GoInterface) :
    boltLogger (GF := GF) l = bbolt.boltLogger l := by
  unfold boltLogger; rw [theFs_eq]

/-- An `Options` the laws describe is never nil. -/
theorem optsAt_nonnull (l : Loc) (dq : DFrac) (o : OptsM) :
    optsAt (GF := GF) l dq o ⊢ ⌜l ≠ Loc.null⌝ := by
  unfold optsAt
  iintro ⟨%v, Hv, -⟩
  icases (bbolt.optsPt_eq l v dq).1 $$ Hv with ⟨-, %Hnn⟩
  ipureintro; exact Hnn

theorem optsVal_zero : optsVal (zero_val go_etcd_io.bbolt.Options) optsZero :=
  ⟨W64 0, Or.inl rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl, rfl⟩

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
  exact optsVal_zero

/-- A zero `Options` (what `wp_auto` makes of `&bolt.Options{}`). -/
theorem optsAt_zero (l : Loc) :
    (l ↦ (zero_val go_etcd_io.bbolt.Options) : IProp GF) ⊢ optsAt l (DFrac.own 1) optsZero := by
  unfold optsAt
  iintro H
  iexists _
  iframe H
  ipureintro; exact optsVal_zero

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

/-- A `bool` field other than `ReadOnly`, `Mlock` and `NoFreelistSync` (`NoGrowSync`,
`PreLoadFreelist`, `NoSync`, `NoStatistics`): storing it keeps `o`. -/
theorem optsAt_bool (l : Loc) (o : OptsM) (f : GoString)
    (hf : f = go!"NoGrowSync" ∨ f = go!"PreLoadFreelist" ∨ f = go!"NoSync" ∨
      f = go!"NoStatistics") :
  optsAt (GF := GF) l (DFrac.own 1) o ⊢
    ∃ x : Bool, structFieldRef go_etcd_io.bbolt.Options f l ↦ x ∗
      (∀ y : Bool, structFieldRef go_etcd_io.bbolt.Options f l ↦ y -∗ optsAt l (DFrac.own 1) o) := by
  unfold optsAt
  iintro ⟨%v, Hv, %hv⟩
  obtain ⟨fl, hfl, hb, h1, h2, h3⟩ := hv
  icases (bbolt.optsPt_eq l v _).1 $$ Hv with
    ⟨⟨H1, H2, H3, H4, H5, H6, H7, H8, H9, H10, H11, H12, H13, H14, H15, -⟩, %Hnn⟩
  rcases hf with rfl | rfl | rfl | rfl
  · iexists _; iframe H2; iintro %y H2; iexists { v with NoGrowSync' := y }
    isplitl; · iapply (bbolt.optsPt_eq l _ _).2; iframe; ipureintro; exact Hnn
    ipureintro; exact ⟨fl, hfl, hb, h1, h2, h3⟩
  · iexists _; iframe H4; iintro %y H4; iexists { v with PreLoadFreelist' := y }
    isplitl; · iapply (bbolt.optsPt_eq l _ _).2; iframe; ipureintro; exact Hnn
    ipureintro; exact ⟨fl, hfl, hb, h1, h2, h3⟩
  · iexists _; iframe H11; iintro %y H11; iexists { v with NoSync' := y }
    isplitl; · iapply (bbolt.optsPt_eq l _ _).2; iframe; ipureintro; exact Hnn
    ipureintro; exact ⟨fl, hfl, hb, h1, h2, h3⟩
  · iexists _; iframe H15; iintro %y H15; iexists { v with NoStatistics' := y }
    isplitl; · iapply (bbolt.optsPt_eq l _ _).2; iframe; ipureintro; exact Hnn
    ipureintro; exact ⟨fl, hfl, hb, h1, h2, h3⟩

/-- The `NoFreelistSync` field: storing it sets `o.noFreelistSync`. -/
theorem optsAt_noFreelistSync (l : Loc) (o : OptsM) :
  optsAt (GF := GF) l (DFrac.own 1) o ⊢
    ∃ x : Bool, structFieldRef go_etcd_io.bbolt.Options go!"NoFreelistSync" l ↦ x ∗
      (∀ y : Bool, structFieldRef go_etcd_io.bbolt.Options go!"NoFreelistSync" l ↦ y -∗
        optsAt l (DFrac.own 1) { o with noFreelistSync := y }) := by
  unfold optsAt
  iintro ⟨%v, Hv, %hv⟩
  obtain ⟨fl, hfl, hb, h1, h2, h3⟩ := hv
  icases (bbolt.optsPt_eq l v _).1 $$ Hv with
    ⟨⟨H1, H2, H3, H4, H5, H6, H7, H8, H9, H10, H11, H12, H13, H14, H15, -⟩, %Hnn⟩
  iexists _; iframe H3; iintro %y H3; iexists { v with NoFreelistSync' := y }
  isplitl; · iapply (bbolt.optsPt_eq l _ _).2; iframe; ipureintro; exact Hnn
  ipureintro; exact ⟨fl, hfl, hb, h1, rfl, h3⟩

/-- The `Mlock` field: storing `false` keeps `o` (bbolt's proved `Open` takes only `Mlock` false). -/
theorem optsAt_mlock (l : Loc) (o : OptsM) :
  optsAt (GF := GF) l (DFrac.own 1) o ⊢
    ∃ x : Bool, structFieldRef go_etcd_io.bbolt.Options go!"Mlock" l ↦ x ∗
      (structFieldRef go_etcd_io.bbolt.Options go!"Mlock" l ↦ false -∗ optsAt l (DFrac.own 1) o) := by
  unfold optsAt
  iintro ⟨%v, Hv, %hv⟩
  obtain ⟨fl, hfl, hb, h1, h2, h3⟩ := hv
  icases (bbolt.optsPt_eq l v _).1 $$ Hv with
    ⟨⟨H1, H2, H3, H4, H5, H6, H7, H8, H9, H10, H11, H12, H13, H14, H15, -⟩, %Hnn⟩
  iexists _; iframe H13; iintro H13; iexists { v with Mlock' := false }
  isplitl; · iapply (bbolt.optsPt_eq l _ _).2; iframe; ipureintro; exact Hnn
  ipureintro
  obtain ⟨b1, b2, b3, b4, -, b6⟩ := hb
  exact ⟨fl, hfl, ⟨b1, b2, b3, b4, rfl, b6⟩, h1, h2, h3⟩

/-- The `InitialMmapSize` field: storing it sets `o.initialMmapSize`. -/
theorem optsAt_initialMmapSize (l : Loc) (o : OptsM) :
  optsAt (GF := GF) l (DFrac.own 1) o ⊢
    ∃ x : w64, structFieldRef go_etcd_io.bbolt.Options go!"InitialMmapSize" l ↦ x ∗
      (∀ y : w64, structFieldRef go_etcd_io.bbolt.Options go!"InitialMmapSize" l ↦ y -∗
        optsAt l (DFrac.own 1) { o with initialMmapSize := y }) := by
  unfold optsAt
  iintro ⟨%v, Hv, %hv⟩
  obtain ⟨fl, hfl, hb, h1, h2, h3⟩ := hv
  icases (bbolt.optsPt_eq l v _).1 $$ Hv with
    ⟨⟨H1, H2, H3, H4, H5, H6, H7, H8, H9, H10, H11, H12, H13, H14, H15, -⟩, %Hnn⟩
  iexists _; iframe H8; iintro %y H8; iexists { v with InitialMmapSize' := y }
  isplitl; · iapply (bbolt.optsPt_eq l _ _).2; iframe; ipureintro; exact Hnn
  ipureintro; exact ⟨fl, hfl, hb, h1, h2, rfl⟩

/-- The `MaxSize` field: storing it keeps `o`. -/
theorem optsAt_maxSize (l : Loc) (o : OptsM) :
  optsAt (GF := GF) l (DFrac.own 1) o ⊢
    ∃ x : w64, structFieldRef go_etcd_io.bbolt.Options go!"MaxSize" l ↦ x ∗
      (∀ y : w64, structFieldRef go_etcd_io.bbolt.Options go!"MaxSize" l ↦ y -∗
        optsAt l (DFrac.own 1) o) := by
  unfold optsAt
  iintro ⟨%v, Hv, %hv⟩
  obtain ⟨fl, hfl, hb, h1, h2, h3⟩ := hv
  icases (bbolt.optsPt_eq l v _).1 $$ Hv with
    ⟨⟨H1, H2, H3, H4, H5, H6, H7, H8, H9, H10, H11, H12, H13, H14, H15, -⟩, %Hnn⟩
  iexists _; iframe H10; iintro %y H10; iexists { v with MaxSize' := y }
  isplitl; · iapply (bbolt.optsPt_eq l _ _).2; iframe; ipureintro; exact Hnn
  ipureintro; exact ⟨fl, hfl, hb, h1, h2, h3⟩

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
  obtain ⟨fl, hfl, hb, h1, h2, h3⟩ := hv
  icases (bbolt.optsPt_eq l v _).1 $$ Hv with
    ⟨⟨H1, H2, H3, H4, H5, H6, H7, H8, H9, H10, H11, H12, H13, H14, H15, -⟩, %Hnn⟩
  iexists _; iframe H5; iintro %y H5; iexists { v with FreelistType' := y }
  isplitl; · iapply (bbolt.optsPt_eq l _ _).2; iframe; ipureintro; exact Hnn
  ipureintro; exact ⟨fl, hfl, hb, h1, h2, h3⟩

/-- The `Timeout` field: storing it sets `o.timeout`. -/
theorem optsAt_timeout (l : Loc) (o : OptsM) :
  optsAt (GF := GF) l (DFrac.own 1) o ⊢
    ∃ x : time.Duration, structFieldRef go_etcd_io.bbolt.Options go!"Timeout" l ↦ x ∗
      (∀ y : time.Duration, structFieldRef go_etcd_io.bbolt.Options go!"Timeout" l ↦ y -∗
        optsAt l (DFrac.own 1) { o with timeout := y }) := by
  unfold optsAt
  iintro ⟨%v, Hv, %hv⟩
  obtain ⟨fl, hfl, hb, h1, h2, h3⟩ := hv
  icases (bbolt.optsPt_eq l v _).1 $$ Hv with
    ⟨⟨H1, H2, H3, H4, H5, H6, H7, H8, H9, H10, H11, H12, H13, H14, H15, -⟩, %Hnn⟩
  iexists _; iframe H1; iintro %y H1; iexists { v with Timeout' := y }
  isplitl; · iapply (bbolt.optsPt_eq l _ _).2; iframe; ipureintro; exact Hnn
  ipureintro; exact ⟨fl, hfl, hb, rfl, h2, h3⟩

/-- The `Logger` field: it holds `o.logger`; storing it sets it. -/
theorem optsAt_logger (l : Loc) (o : OptsM) :
  optsAt (GF := GF) l (DFrac.own 1) o ⊢
    structFieldRef go_etcd_io.bbolt.Options go!"Logger" l ↦ (o.logger : go_etcd_io.bbolt.Logger) ∗
      (∀ y : go_etcd_io.bbolt.Logger, structFieldRef go_etcd_io.bbolt.Options go!"Logger" l ↦ y -∗
        optsAt l (DFrac.own 1) { o with logger := y }) := by
  unfold optsAt
  iintro ⟨%v, Hv, %hv⟩
  obtain ⟨fl, hfl, hb, h1, h2, h3⟩ := hv
  icases (bbolt.optsPt_eq l v _).1 $$ Hv with
    ⟨⟨H1, H2, H3, H4, H5, H6, H7, H8, H9, H10, H11, H12, H13, H14, H15, -⟩, %Hnn⟩
  obtain ⟨b1, b2, b3, b4, b5, b6⟩ := hb
  rw [show (o.logger : go_etcd_io.bbolt.Logger) = v.Logger' from b4.symm]
  iframe H14; iintro %y H14; iexists { v with Logger' := y }
  isplitl; · iapply (bbolt.optsPt_eq l _ _).2; iframe; ipureintro; exact Hnn
  ipureintro; exact ⟨fl, hfl, ⟨b1, b2, b3, rfl, b5, b6⟩, h1, h2, h3⟩

/-- **The options `Open` accepts, as bbolt's** (S3e): the backend's `optsAt` at options it accepts
(`OptsM.ok`) with no error of their own (`OptsM.noErr`) is bbolt's `optsAtNoErr` at options its
`Open` accepts, with its `Mlock` false. -/
theorem optsAt_bolt (l : Loc) (dq : DFrac) (o : OptsM) (hok : o.ok) (hne : o.noErr) :
    optsAt (GF := GF) l dq o ⊢ ∃ f : w64, ⌜(o.toBolt false f).ok⌝ ∗
      bbolt.optsAtNoErr l dq (o.toBolt false f) ∗
      (bbolt.optsAtNoErr l dq (o.toBolt false f) -∗
        ∃ x : w64, optsAt l dq { o with initialMmapSize := x }) := by
  unfold optsAt bbolt.optsAtNoErr
  iintro ⟨%v, Hv, %hv⟩
  obtain ⟨f, hf, hb, h1, h2, h3⟩ := hv
  iexists f
  isplitr
  · ipureintro
    obtain ⟨k1, k2, k3, k4⟩ := hok
    exact ⟨k1, k2, k3, rfl, hf, k4⟩
  isplitl [Hv]
  · iexists v; iframe Hv; ipureintro
    obtain ⟨n1, n2, n3⟩ := hne
    refine ⟨hb, ?_, ?_, ?_⟩
    · rw [h1]; exact n1
    · rw [h2]; exact n2
    · rw [h3]; exact n3
  iintro ⟨%v', Hv', %hv'⟩
  obtain ⟨hb', n1', n2', -⟩ := hv'
  iexists v'.InitialMmapSize'
  iexists v'; iframe Hv'; ipureintro
  exact ⟨f, hf, hb', by rw [n1', hne.1], by rw [n2', hne.2.1], rfl⟩

end preds


end backend
end EtcdGrove
end Perennial
