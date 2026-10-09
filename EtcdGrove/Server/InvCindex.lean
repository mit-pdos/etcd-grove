/-
etcd's consistent index (`server/v3/etcdserver/cindex/cindex.go`) and its reads and writes of
the backend (`server/v3/storage/schema/cindex.go`): the shared vocabulary of
`Spec/consistentIndex__*.lean`, `Spec/NewConsistentIndex.lean` and the `schema` specs.
Lean-first (no Rocq counterpart).

A `consistentIndex` caches the backend's `consistent_index` key: the index of the last raft
entry whose effects the backend holds. Its four `uint64`s are atomics; `be` is the backend
it lazily loads the index from, under `mutex`.

**The index and its term.** `consistentIndex`/`term` are read and written by several
goroutines (the apply thread sets them; a backend commit, under the batch transaction's lock,
saves them with `UnsafeSave`), so they live in an invariant (`ciInv`) with half of a ghost
variable mirroring the index; the client holds the other half (`ciIdx γ k`), which it
keeps in its own invariant. The specs of the operations that read or write the index are
logically atomic, in Perennial's style for `sync/atomic`: the caller passes a fancy update
that, at the moment the index is read or stored, hands over `ciIdx γ k` and gets it back
(updated). The term is not mirrored: it is whatever was last stored, and only the
backend's copy of it is ever read back. `SetConsistentIndex` stores the index, *then* the
term: two atomic steps, so a concurrent `UnsafeSave` can save a new index with the old term
(see notes/decisions.md); the specs say nothing about the term for that reason.

**The applying index** (`applyingIndex`/`applyingTerm`) is only ever accessed by the apply
thread, which owns the two fields outright (`ciApplying`).

**The backend field.** `be` is written by `SetBackend` under `mutex`, read by
`ConsistentIndex` under `mutex`, and read by `UnsafeConsistentIndex` *without* it. So half
of `ci.be ↦ b` is the mutex's, the other half the owner's (`ciOwner ci b`, the apply
thread's): writing needs both, reading either. Every caller of `ConsistentIndex` in etcd is
on the apply path (the apply loop, the entry applier's deferred update, the auth applier,
`snapshot`), so its spec asks for `ciOwner` too.

**The backend's meta keys** are an abstract view `View : MetaCI → IProp`, chosen by the
client: `metaReader r E View` is the contract of an `UnsafeReader` whose `UnsafeRange` on the
two keys is a linearizable read of the view (a fancy update at mask `E`), `metaReadTx` that
of a `ReadTx` (`RLock`/`RUnlock` too), `isMetaBackend b E View` that of a `Backend` whose
`ReadTx()` returns one; `metaWriter tx TM` is the contract of the batch transaction (an
`UnsafeReadWriter`) the lock holder writes through, whose meta keys are `TM m`, owned. These
are definitions: a client supplies the triples with its backend, as raft's clients do with
`Storage`. A stored value is the 8-byte big-endian encoding of a non-zero `uint64`; an absent
key reads as 0 (`schema` never stores 0).
-/
import EtcdGrove.Server.Base

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.cindex
  go_etcd_io.etcd.server.v3.storage

/-! ## Big-endian encoding -/

/-- The big-endian encoding of `x` (`binary.BigEndian.PutUint64`). -/
def u64Be (x : w64) : List w8 := (u64Le x).reverse

/-- Big-endian decoding of 8 bytes (`binary.BigEndian.Uint64`). -/
def beToU64 (bs : List w8) : w64 := leToU64 bs.reverse

theorem beToU64_u64Be (x : w64) : beToU64 (u64Be x) = x := by
  simp [beToU64, u64Be, u64Le_to_word]

theorem u64Be_length (x : w64) : (u64Be x).length = 8 := by
  simp [u64Be, u64Le_length]

/-! ## The meta keys -/

/-- The backend's `consistent_index` and `term` keys, as `uint64`s (0: absent). -/
abbrev MetaCI := w64 × w64

/-- The meta keys after `UnsafeUpdateConsistentIndex(tx, k, t)` on `m`: nothing if `k = 0`,
else the index `k`, and the term `t` if it is not 0. -/
def metaAfterSave (m : MetaCI) (k t : w64) : MetaCI :=
  if k = W64 0 then m else (k, if t = W64 0 then m.2 else t)

-- The field addresses of a `consistentIndex`.
section addrs
variable [FfiSyntax] [GoGlobalContext] [GoSemanticsFunctions]

abbrev ciIdxAddr (ci : Loc) : Loc := structFieldRef consistentIndex go!"consistentIndex" ci
abbrev ciTermAddr (ci : Loc) : Loc := structFieldRef consistentIndex go!"term" ci
abbrev ciAppIdxAddr (ci : Loc) : Loc := structFieldRef consistentIndex go!"applyingIndex" ci
abbrev ciAppTermAddr (ci : Loc) : Loc := structFieldRef consistentIndex go!"applyingTerm" ci
abbrev ciBeAddr (ci : Loc) : Loc := structFieldRef consistentIndex go!"be" ci
abbrev ciMutexAddr (ci : Loc) : Loc := structFieldRef consistentIndex go!"mutex" ci

end addrs

/-- The consistent index's invariant's namespace. -/
def ciN : Namespace := nroot.@"cindex"

/-- The ghost names of a consistent index. -/
structure CINames where
  /-- `ghostVar w64`: the index (half in `ciInv`, half the client's `ciIdx`) -/
  idx : GName

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]

/-- The client's view of the index: it is `k`. -/
def ciIdx (γ : CINames) (k : w64) : IProp GF := ghostVar γ.idx (1 : Qp).half k

instance ciIdx_timeless (γ : CINames) (k : w64) : Timeless (ciIdx (GF := GF) γ k) := by
  unfold ciIdx; infer_instance

/-- The index and term fields, with the invariant's half of the index's mirror. -/
def ciInv (ci : Loc) (γ : CINames) : IProp GF :=
  iprop(∃ (k t : w64), ciIdxAddr ci ↦ k ∗ ghostVar γ.idx (1 : Qp).half k ∗ ciTermAddr ci ↦ t)

/-- The mutex's half of the backend field. -/
def ciLockInv (ci : Loc) : IProp GF :=
  iprop(∃ b : GoInterface, typedPointsto (ciBeAddr ci) b (DFrac.own (1 : Qp).half))

/-- `ci` is a consistent index with ghost names `γ` (persistent). -/
def isCI (ci : Loc) (γ : CINames) : IProp GF :=
  iprop(inv ciN (ciInv ci γ) ∗ sync.isMutex (ciMutexAddr ci) (ciLockInv ci))

instance isCI_persistent (ci : Loc) (γ : CINames) : Persistent (isCI (GF := GF) ci γ) := by
  unfold isCI; infer_instance

/-- The owner's half of the backend field: the backend is `b`. -/
def ciOwner (ci : Loc) (b : GoInterface) : IProp GF :=
  typedPointsto (ciBeAddr ci) b (DFrac.own (1 : Qp).half)

/-- The applying index and term, owned by the apply thread. -/
def ciApplying (ci : Loc) (a t : w64) : IProp GF :=
  iprop(ciAppIdxAddr ci ↦ a ∗ ciAppTermAddr ci ↦ t)

/-! ## The backend's contracts -/

/-- `vs` is what `UnsafeRange` returns for a meta key holding `x` (0: absent): no value, or
the one value, the encoding of `x`. -/
def metaVals (vs : GoSlice) (x : w64) : IProp GF :=
  if x = W64 0 then iprop(vs ↦*□ ([] : List GoSlice))
  else iprop(∃ s : GoSlice, vs ↦*□ [s] ∗ s ↦*□ u64Be x)

instance metaVals_persistent (vs : GoSlice) (x : w64) : Persistent (metaVals (GF := GF) vs x) := by
  unfold metaVals; split <;> infer_instance

/-- A linearizable read of the view `View` at mask `E`, continuing with `Ψ` of what it read. -/
def readAU (E : CoPset) (View : MetaCI → IProp GF) (Ψ : MetaCI → IProp GF) : IProp GF :=
  iprop(|={⊤,E}=> ∃ m : MetaCI, View m ∗ (View m ={E,⊤}=∗ Ψ m))

/-- `UnsafeRange` of the reader `r` on a meta key (bucket `Meta`, the key's name, no end key,
no limit) reads `sel m` of the view. -/
def metaRangeSpec (r : GoInterfaceOk) (keyName : GoString) (sel : MetaCI → w64) (E : CoPset)
    (View : MetaCI → IProp GF) : IProp GF :=
  iprop(∀ (b : GoInterface) (key : GoSlice) (Φ : val → IProp GF),
    globalAddr schema.Meta ↦□ b -∗ key ↦*□ keyName -∗
    readAU E View (fun m => iprop(∀ (ks vs : GoSlice), metaVals vs (sel m) -∗ Φ (PairV #ks #vs))) -∗
    WP (App (App (App (App (Val #(methods r.ty go!"UnsafeRange" r.v)) (Val #b)) (Val #key))
          (Val #(slice.nil))) (Val #(W64 0))) {{ Φ }})

/-- `r` is an `UnsafeReader` whose meta keys are a linearizable view `View` (persistent). -/
def metaReader (r : GoInterfaceOk) (E : CoPset) (View : MetaCI → IProp GF) : IProp GF :=
  iprop(□ metaRangeSpec r schema.ciKeyBytes Prod.fst E View ∗
    □ metaRangeSpec r schema.termKeyBytes Prod.snd E View)

instance metaReader_persistent (r : GoInterfaceOk) (E : CoPset) (View : MetaCI → IProp GF) :
    Persistent (metaReader r E View) := by
  unfold metaReader; infer_instance

/-- `rt` is a `ReadTx` whose meta keys are the view `View`: `RLock`/`RUnlock` return, and its
reads are `metaReader`'s. -/
def metaReadTx (rt : GoInterfaceOk) (E : CoPset) (View : MetaCI → IProp GF) : IProp GF :=
  iprop(□ ({{ True }} (App (Val #(methods rt.ty go!"RLock" rt.v)) (Val #())) {{ RET #(); True }}) ∗
    □ ({{ True }} (App (Val #(methods rt.ty go!"RUnlock" rt.v)) (Val #())) {{ RET #(); True }}) ∗
    metaReader rt E View)

instance metaReadTx_persistent (rt : GoInterfaceOk) (E : CoPset) (View : MetaCI → IProp GF) :
    Persistent (metaReadTx rt E View) := by
  unfold metaReadTx; infer_instance

/-- `b` is a `Backend` whose `ReadTx()` returns a `metaReadTx` of the view `View`. -/
def isMetaBackend (b : GoInterface) (E : CoPset) (View : MetaCI → IProp GF) : IProp GF :=
  iprop(∃ bi : GoInterfaceOk, ⌜b = GoInterface.ok bi⌝ ∗
    □ ({{ True }} (App (Val #(methods bi.ty go!"ReadTx" bi.v)) (Val #()))
       {{ (rt : GoInterfaceOk), RET #(GoInterface.ok rt); metaReadTx rt E View }}))

instance isMetaBackend_persistent (b : GoInterface) (E : CoPset) (View : MetaCI → IProp GF) :
    Persistent (isMetaBackend b E View) := by
  unfold isMetaBackend; infer_instance

/-- `UnsafePut` of the batch transaction `tx` on a meta key: the key's stored value becomes the
encoding of `x` (`upd m x`); the transaction keeps the value slice. -/
def metaPutSpec (tx : GoInterfaceOk) (keyName : GoString) (upd : MetaCI → w64 → MetaCI)
    (TM : MetaCI → IProp GF) : IProp GF :=
  iprop(∀ (b : GoInterface) (key val : GoSlice) (m : MetaCI) (x : w64),
    {{ globalAddr schema.Meta ↦□ b ∗ key ↦*□ keyName ∗ val ↦* u64Be x ∗ TM m }}
      (App (App (App (Val #(methods tx.ty go!"UnsafePut" tx.v)) (Val #b)) (Val #key)) (Val #val))
    {{ RET #(); TM (upd m x) }})

/-- `tx` is a batch transaction (`UnsafeReadWriter`) whose meta keys are `TM m`, owned by the
holder of its lock: it reads them (`metaReader` at mask `⊤`) and writes them. -/
def metaWriter (tx : GoInterfaceOk) (TM : MetaCI → IProp GF) : IProp GF :=
  iprop(metaReader tx ⊤ TM ∗
    □ metaPutSpec tx schema.ciKeyBytes (fun m x => (x, m.2)) TM ∗
    □ metaPutSpec tx schema.termKeyBytes (fun m x => (m.1, x)) TM)

instance metaWriter_persistent (tx : GoInterfaceOk) (TM : MetaCI → IProp GF) :
    Persistent (metaWriter tx TM) := by
  unfold metaWriter; infer_instance

/-- The two reads of `schema.UnsafeReadConsistentIndex` (the index; then, if it is not 0, the
term), continuing with `Ψ` of the pair it returns. -/
def readCIAU (E : CoPset) (View : MetaCI → IProp GF) (Ψ : MetaCI → IProp GF) : IProp GF :=
  readAU E View (fun m =>
    if m.1 = W64 0 then Ψ (W64 0, W64 0) else readAU E View (fun m' => Ψ (m.1, m'.2)))

/-- A read's continuation can be weakened. -/
theorem readAU_wand (E : CoPset) (View : MetaCI → IProp GF) (Ψ Ψ' : MetaCI → IProp GF) :
    readAU E View Ψ ⊢ (∀ m, Ψ m -∗ Ψ' m) -∗ readAU E View Ψ' := by
  unfold readAU
  iintro HAU HΨ
  imod HAU with ⟨%m, Hv, HAU⟩
  imodintro
  iexists m
  iframe Hv
  iintro Hv
  imod HAU $$ Hv with HAU
  imodintro
  iapply HΨ $$ HAU

/-- `readCIAU`'s continuation can be weakened. -/
theorem readCIAU_wand (E : CoPset) (View : MetaCI → IProp GF) (Ψ Ψ' : MetaCI → IProp GF) :
    readCIAU E View Ψ ⊢ (∀ m, Ψ m -∗ Ψ' m) -∗ readCIAU E View Ψ' := by
  unfold readCIAU
  iintro HAU HΨ
  iapply readAU_wand $$ HAU
  iintro %m Hm
  by_cases h : m.1 = W64 0
  · simp only [h, ↓reduceIte]
    iapply HΨ $$ Hm
  · simp only [h, ↓reduceIte]
    iapply readAU_wand $$ Hm
    iintro %m' Hm'
    iapply HΨ $$ Hm'

end defs

/-! ## Atomics on owned fields -/

section atomics
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : sync.atomic.Assumptions]

/-- `atomic.LoadUint64` of an owned field, as a plain triple. -/
theorem wp_LoadUint64_own (addr : Loc) (dq : DFrac) (v : w64) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sync.atomic ∗ addr ↦{dq} v }}
      (App (Val (@! sync.atomic.LoadUint64)) (Val #addr))
    {{ RET #v; addr ↦{dq} v }} := by
  iintro %Φ ⟨#Hpkg, Ha⟩ HΦ
  wp_apply_core sync.atomic.wp_LoadUint64 $$ [] [Ha HΦ]
  · iexact Hpkg
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  iexists v
  iframe Ha
  iintro Ha
  imod Hmask with -
  imodintro
  iapply HΦ $$ Ha

/-- `atomic.StoreUint64` to an owned field, as a plain triple. -/
theorem wp_StoreUint64_own (addr : Loc) (v0 v : w64) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sync.atomic ∗ addr ↦ v0 }}
      (App (App (Val (@! sync.atomic.StoreUint64)) (Val #addr)) (Val #v))
    {{ RET #(); addr ↦ v }} := by
  iintro %Φ ⟨#Hpkg, Ha⟩ HΦ
  wp_apply_core sync.atomic.wp_StoreUint64 $$ [] [Ha HΦ]
  · iexact Hpkg
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  iexists v0
  iframe Ha
  iintro Ha
  imod Hmask with -
  imodintro
  iapply HΦ $$ Ha

end atomics

end EtcdGrove
end Perennial
