/-
raft v3.7's `raftpb` entries as the apply thread reads them: the server's model `EntryModel`
over raft's own points-to predicate (stage R6 of the raft v3.7 retarget, D9: `notes/decisions.md`,
"The swap"). Lean-first (no Rocq counterpart).

Until the swap (2026-10-16) the server's raft was a names-only translation of etcd's dependency
(`EtcdDeps/`), and this file described an entry field by field (`optU64`/`optU32` per optional
field, `entryAt`), with the getters' specs restated over that. Now the server's translation
imports the verified raft, whose `InvPb.lean` describes the same objects (`entPts l dq e` over
`EntryM`: one `cellRO` per optional field, the data bytes read-only, the hidden protobuf fields
in the `protobuf` invariant), and the getters' specs are raft's. So `entryAt e m` is raft's
`entRO e m.toM`: the server keeps its model (its ghost logs, `rnReadyP`, the request path's
`InvRequest` and the exported `Results` are stated over `EntryModel`), raft provides the
points-to. The lemmas below restate raft's getter specs in the shape the server's proofs use
(`wp_entryAt_GetIndex` and the like take the raft spec as a hypothesis, as raft's own
`LemmasMiscR.lean` does for `hsOpt`).

It imports the apply package's `Base` (raftpb's instance), not the server's `BaseApply`: the
apply package reads entries too (`apply.Apply`) and must not import the server's translation.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.Base
public import Proof.go_etcd_io.raft.v3.InvPb
public import Spec.go_etcd_io.raft.v3.raftpb.Entry__GetIndex
public import Spec.go_etcd_io.raft.v3.raftpb.Entry__GetTerm
public import Spec.go_etcd_io.raft.v3.raftpb.Entry__GetType
public import Spec.go_etcd_io.raft.v3.raftpb.ConfChange__GetId

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

/-- The bytes `bs` are the protobuf encoding of some `raftpb.ConfChange` (what etcd proposes
as an `EntryConfChange`'s data: `cc.Marshal()` in `configure`): raft's decoder `ccDecodeV1`
(`CCModel.lean`, what `proto.Unmarshal` makes of bytes into a `*ConfChange`, opaque) accepts
them. `pbutil.MustUnmarshalMessage` panics on any other bytes. Until stage R8b of the raft v3.7
retarget (2026-10-16) an opaque predicate of the server's own; now one notion of a `ConfChange`
encoding, so that the bootstrap log's entries (`BootLogOk`: bytes decoding to `AddNode`) pass
the server's `srvIdxOk` and `srvCCPolicy` matches raft's policy. -/
def isConfChangeEncoding [FfiSyntax] (bs : List w8) : Prop := (ccDecodeV1 bs).isSome

/-- **The id of the conf change the bytes decode to** (`pbutil.MustUnmarshalMessage`'s, a
function of the bytes): what the apply thread triggers the wait with after a conf change
(`s.w.Trigger(cc.ID, ...)`); `0` when the bytes do not decode (2026-10-12, the request path's unit
2: the decoder's axiom names it, so that the apply loop's premise can say the conf change's id
is no KV request's; stage R8b: raft's decoder's `id`, until then opaque). -/
def ccIdOf [FfiSyntax] (bs : List w8) : w64 :=
  match ccDecodeV1 bs with
  | some m => m.id
  | none => W64 0

theorem isConfChangeEncoding_of_decode [FfiSyntax] {bs : List w8} {m : CCV1M}
    (h : ccDecodeV1 bs = some m) : isConfChangeEncoding bs := by
  unfold isConfChangeEncoding; rw [h]; rfl

theorem isConfChangeEncoding_decode [FfiSyntax] {bs : List w8} (h : isConfChangeEncoding bs) :
    ∃ m : CCV1M, ccDecodeV1 bs = some m := by
  unfold isConfChangeEncoding at h
  exact Option.isSome_iff_exists.mp h

theorem ccIdOf_of_decode [FfiSyntax] {bs : List w8} {m : CCV1M} (h : ccDecodeV1 bs = some m) :
    ccIdOf bs = m.id := by
  unfold ccIdOf; rw [h]

/-- A raft entry as the apply thread uses it (the server's model; raft's is `EntryM`,
`Proof/go_etcd_io/raft/v3/PbModel.lean`, the same five values). (2026-10-19, witness support:
raft#168's `Entry.Subterm`, which the server never reads, is carried so that `toM`/`ofM` stay
inverse; the server's specs constrain it nowhere.) -/
structure EntryModel where
  term : w64
  index : w64
  typ : w32
  data : List w8
  subterm : w64

/-- (Moved here from `InvRaftNode.lean`, 2026-10-14, unit T1: the server's raft contract keeps
logs of entries in ghost state.) -/
instance entryModel_countable : Pos.Countable EntryModel :=
  .ofInjective (fun m => Pos.Countable.encode ((((m.term, m.index), m.typ), m.data), m.subterm))
    (fun ⟨_, _, _, _, _⟩ ⟨_, _, _, _, _⟩ h => by
      have h := Pos.encode_inj h
      simp only [Prod.mk.injEq] at h
      obtain ⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩, rfl⟩ := h
      rfl)

/-- The server's entry as raft's record (`EntryM`: what the getters return, field for field;
`raftpb.EntryType` is `w32`). -/
def EntryModel.toM [FfiSyntax] (m : EntryModel) : EntryM := ⟨m.term, m.index, m.typ, m.data, m.subterm⟩

-- Projection lemmas, `@[simp, word_unfold]` (`Proof/go_etcd_io/raft/v3/ProjSimps.lean`).
proj_simps Perennial.EtcdGrove.EntryModel.toM

theorem EntryModel.toM_inj [FfiSyntax] {m m' : EntryModel} (h : m.toM = m'.toM) : m = m' := by
  cases m; cases m'
  simp only [EntryModel.toM, EntryM.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h
  rfl

/-- Raft's record as the server's entry (2026-10-16, stage R7b: the server's contract is defined
over raft's protocol, whose logs are of `EntryM`). -/
def EntryModel.ofM [FfiSyntax] (e : EntryM) : EntryModel :=
  ⟨e.Term', e.Index', e.Type', e.Data', e.Subterm'⟩

proj_simps Perennial.EtcdGrove.EntryModel.ofM

@[simp] theorem EntryModel.toM_ofM [FfiSyntax] (e : EntryM) : (EntryModel.ofM e).toM = e := by
  cases e; rfl

@[simp] theorem EntryModel.ofM_toM [FfiSyntax] (m : EntryModel) : EntryModel.ofM m.toM = m := by
  cases m; rfl

theorem EntryModel.toM_injective [FfiSyntax] : Function.Injective (EntryModel.toM) :=
  fun _ _ h => EntryModel.toM_inj h

@[simp] theorem EntryModel.map_toM_ofM [FfiSyntax] (l : List EntryM) :
    (l.map EntryModel.ofM).map EntryModel.toM = l := by
  rw [List.map_map]; exact List.map_id'' (fun e => EntryModel.toM_ofM e) l

@[simp] theorem EntryModel.map_ofM_toM [FfiSyntax] (L : List EntryModel) :
    (L.map EntryModel.toM).map EntryModel.ofM = L := by
  rw [List.map_map]; exact List.map_id'' (fun m => EntryModel.ofM_toM m) L

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.raftpb.Assumptions]

/-- `e` is a (non-nil) read-only entry modelled by `m`: raft's `entRO` (D9). -/
def entryAt (e : Loc) (m : EntryModel) : IProp GF := entRO e m.toM

instance entryAt_persistent (e : Loc) (m : EntryModel) : Persistent (entryAt (GF := GF) e m) := by
  unfold entryAt; infer_instance

/-- What the apply thread reads of an entry besides the getters: it is non-nil, and its `Data`
field holds a read-only slice of the model's bytes (`pbutil.MustUnmarshalMessage`'s argument). -/
theorem entryAt_fields (e : Loc) (m : EntryModel) :
    entryAt (GF := GF) e m ⊢
      ⌜e ≠ null⌝ ∗ ∃ d : GoSlice, e.[raftpb.Entry, go!"Data"] ↦□ d ∗ d ↦*□ m.data := by
  iintro H
  unfold entryAt entRO entPts
  iNamed H
  isplitr
  · ipureintro; exact Hnn
  iexists ds
  iframe HD
  iExactEq Hd
  rfl

/-! ## The getters, in the server's terms -/

/-- `e.GetIndex()` of an entry at `m` is `m.index` (raft's `Entry.GetIndex.spec`). -/
theorem wp_entryAt_GetIndex (wp_GetIndex : raftpb.Entry.GetIndex.spec (GF := GF) (hG := hG)) :
    ∀ (e : Loc) (m : EntryModel),
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb ∗ entryAt e m }}
      (App (Val (e @!! go.GoType.PointerType raftpb.Entry.ty @!! go!"GetIndex")) (Val #()))
    {{ RET #m.index; True }} := by
  intro e m
  iintro %Φ ⟨#Hi, #H⟩ HΦ
  iunfold entryAt at H
  iapply wp_GetIndex.1 e DFrac.discard m.toM $$ [$Hi $H]
  inext
  iintro -
  ispecialize HΦ $$ []
  · itrivial
  iExactEq HΦ
  rfl

/-- `e.GetTerm()` of an entry at `m` is `m.term`. -/
theorem wp_entryAt_GetTerm (wp_GetTerm : raftpb.Entry.GetTerm.spec (GF := GF) (hG := hG)) :
    ∀ (e : Loc) (m : EntryModel),
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb ∗ entryAt e m }}
      (App (Val (e @!! go.GoType.PointerType raftpb.Entry.ty @!! go!"GetTerm")) (Val #()))
    {{ RET #m.term; True }} := by
  intro e m
  iintro %Φ ⟨#Hi, #H⟩ HΦ
  iunfold entryAt at H
  iapply wp_GetTerm.1 e DFrac.discard m.toM $$ [$Hi $H]
  inext
  iintro -
  ispecialize HΦ $$ []
  · itrivial
  iExactEq HΦ
  rfl

/-- `e.GetType()` of an entry at `m` is `m.typ`. -/
theorem wp_entryAt_GetType (wp_GetType : raftpb.Entry.GetType.spec (GF := GF) (hG := hG)) :
    ∀ (e : Loc) (m : EntryModel),
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb ∗ entryAt e m }}
      (App (Val (e @!! go.GoType.PointerType raftpb.Entry.ty @!! go!"GetType")) (Val #()))
    {{ RET #m.typ; True }} := by
  intro e m
  iintro %Φ ⟨#Hi, #H⟩ HΦ
  iunfold entryAt at H
  iapply wp_GetType.1 e DFrac.discard m.toM $$ [$Hi $H]
  inext
  iintro -
  ispecialize HΦ $$ []
  · itrivial
  iExactEq HΦ
  rfl

/-- `cc.GetId()` of a conf change holding `m` (raft's `ownCCV1`, at any fraction) whose id is
`id`: what the apply thread triggers the wait with (`ccIdOf`, stated by
`pbutil.MustUnmarshalMessage`'s spec and kept by `applyConfChange`'s). -/
theorem wp_ownCCV1_GetId (wp_GetId : raftpb.ConfChange.GetId.spec (GF := GF) (hG := hG))
    (cc : Loc) (dq : DFrac) (m : CCV1M) (id : w64) (hid : m.id = id) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb ∗ ownCCV1 cc dq m }}
      (App (Val (cc @!! go.GoType.PointerType raftpb.ConfChange.ty @!! go!"GetId")) (Val #()))
    {{ RET #id; ownCCV1 cc dq m }} := by
  subst hid
  iintro %Φ ⟨#Hi, H⟩ HΦ
  iapply wp_GetId.1 cc dq m $$ [$Hi $H] HΦ

end defs

end EtcdGrove
end Perennial
