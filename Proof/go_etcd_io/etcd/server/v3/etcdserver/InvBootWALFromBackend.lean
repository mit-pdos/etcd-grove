/-
`bootstrapWALFromBackend`'s contracts (etcd-io/etcd#19693; pr-verify, 2026-10-17). Lean-first
(no Rocq counterpart).

**The backend** is fixed while the member bootstraps (nothing else runs on it yet): its meta keys
hold `m0` (the consistent index and term, `MetaCI`), read through `ReadTx()` as the constant view
`fun m => ⌜m = m0⌝` of `InvCindex.lean`'s `metaReadTx`, and its conf state is read through the
same `ReadTx` (`csReadTx`, `InvConfState.lean`). `ciPos m0` is the position
`schema.ReadConsistentIndex` returns of it: `(0, 0)` when no index is stored, else the index and
the term.

**The WAL** is the trust boundary `openWALFromPosition` (its body opens the WAL with `wal.Open`,
reads it with `ReadAll`, repairs a torn tail once and `Fatal`s otherwise; the `wal` package is
translated names-only): it returns the WAL, its last hard state (`nil` or read-only), the entries
after the position and the WAL's metadata. `EntsAfter i p`: the `k`-th entry is at index
`i + 1 + k`, what `ReadAll`'s `ErrSliceOutOfRange` check ensures of the entries it returns after the
position it was opened at (an entry past the next index is an error, an earlier one overwrites the
tail: `ents = append(ents[:offset], e)`); and the last is below `2^61` (raft's storage bound) --
**not** checked by `ReadAll`: an assumption on the WAL's contents, as raft's own bound is.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvConfState
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvCindex
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvBootWAL
public import Proof.go_etcd_io.raft.v3.InvPbLog

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage go_etcd_io.raft.v3

section pure
variable [FfiSyntax]

/-- The position `ReadConsistentIndex` returns of the meta keys `m0` (index, term). -/
def ciPos (m0 : MetaCI) : go_etcd_io.etcd.server.v3.storage.wal.Position :=
  if m0.1 = W64 0 then go_etcd_io.etcd.server.v3.storage.wal.Position.mk (W64 0) (W64 0)
  else go_etcd_io.etcd.server.v3.storage.wal.Position.mk m0.2 m0.1

/-- The entries `p` follow the index `i`, one by one, the last below `2^61`. -/
def EntsAfter (i : w64) (p : List EntryM) : Prop :=
  (∀ (k : Nat) (e : EntryM), p[k]? = some e → uint.Z e.Index' = uint.Z i + 1 + k) ∧
    uint.Z i + (p.length : Int) < 2^61

/-- `MemoryStorage`'s first premise (`Spec/.../bootstrappedWAL__MemoryStorage.lean`) from
`EntsAfter`, with a conf state: the base is the snapshot at `pos`. -/
theorem entsAfter_head (pos : go_etcd_io.etcd.server.v3.storage.wal.Position) (cp : Loc)
    (cs : ConfStateM) (p : List EntryM) (Hcp : cp ≠ null) (H : EntsAfter pos.Index' p) :
    ∀ e0, p.head? = some e0 →
      uint.Z e0.Index' = uint.Z (bwalBase pos cp cs).prev.index' + 1 := by
  intro e0 he
  rw [bwalBase_prev_index, if_neg Hcp]
  have h := H.1 0 e0 (by cases p <;> simp_all)
  simp at h
  omega

/-- ... and its second. -/
theorem entsAfter_last (i : w64) (p : List EntryM) (H : EntsAfter i p) :
    ∀ e0, p.head? = some e0 → uint.Z e0.Index' + (p.length : Int) ≤ 2^61 := by
  intro e0 he
  have h := H.1 0 e0 (by cases p <;> simp_all)
  have h2 := H.2
  simp at h
  omega

/-- Without a conf state the base is index `0`: `MemoryStorage`'s first premise fails as soon
as the backend's consistent index is not `0` and the WAL has an entry after it -- `Append` then
panics (`"missing log entry"`). The PR's `MemoryStorage` applies a snapshot only when the backend
has a conf state, which etcd persists only since v3.5 and only on a membership change. -/
theorem entsAfter_head_noConfState (pos : go_etcd_io.etcd.server.v3.storage.wal.Position)
    (cs : ConfStateM) (e0 : EntryM) (p : List EntryM) (Hi : pos.Index' ≠ W64 0)
    (H : EntsAfter pos.Index' (e0 :: p)) :
    ¬ uint.Z e0.Index' = uint.Z (bwalBase pos null cs).prev.index' + 1 := by
  rw [bwalBase_prev_index]
  simp only [↓reduceIte]
  have h := H.1 0 e0 rfl
  have : uint.Z pos.Index' ≠ 0 := by intro h0; apply Hi; word
  have h00 : uint.Z (W64 0) = 0 := by word
  simp at h
  intro heq
  have : 0 ≤ uint.Z pos.Index' := by word
  omega

end pure

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- The backend `be` at bootstrap, its meta keys `m0`: `ReadTx()` returns a read transaction of
the constant view, through which the conf state is read too. -/
def bootBackendOk (be : GoInterface) (m0 : MetaCI) : IProp GF :=
  iprop(∃ bi : GoInterfaceOk, ⌜be = GoInterface.ok bi⌝ ∗
    □ ({{ True }} (App (Val #(methods bi.ty go!"ReadTx" bi.v)) (Val #()))
       {{ (rt : GoInterfaceOk), RET #(GoInterface.ok rt);
          metaReadTx rt ⊤ (fun m => iprop(⌜m = m0⌝)) ∗ csReadTx rt }}))

instance bootBackendOk_persistent (be : GoInterface) (m0 : MetaCI) :
    Persistent (bootBackendOk (GF := GF) be m0) := by
  unfold bootBackendOk; infer_instance

/-- A read of the constant view `m0`, in `readCIAU`'s shape: what `ReadConsistentIndex` returns. -/
theorem readCIAU_const (m0 : MetaCI) (Ψ : MetaCI → IProp GF) :
    Ψ ((ciPos m0).Index', (ciPos m0).Term') ⊢ readCIAU ⊤ (fun m => iprop(⌜m = m0⌝)) Ψ := by
  by_cases h : m0.1 = W64 0
  · simp only [ciPos, h, ↓reduceIte]
    iintro HΨ
    unfold readCIAU readAU
    imodintro
    iexists m0
    isplitr
    · ipureintro; rfl
    iintro -
    imodintro
    simp only [h, ↓reduceIte]
    iexact HΨ
  · simp only [ciPos, h, ↓reduceIte]
    iintro HΨ
    unfold readCIAU readAU
    imodintro
    iexists m0
    isplitr
    · ipureintro; rfl
    iintro -
    imodintro
    simp only [h, ↓reduceIte]
    imodintro
    iexists m0
    isplitr
    · ipureintro; rfl
    iintro -
    imodintro
    iexact HΨ

end defs

end EtcdGrove
end Perennial
