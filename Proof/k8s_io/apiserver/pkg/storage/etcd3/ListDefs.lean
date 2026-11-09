/-
Lean-first (no Rocq counterpart).

# The store's lists: vocabulary (stage 7e-2 of `notes/k8s-7e-scope.md`; `notes/k8s-7e-2-draft.md`
§1 with its "Corrections (2026-11-09)")

- `kInScope kp recur k`: a list's scope (recursive, the keys under the prepared prefix `kp`; not
  recursive, `kp` itself);
- `kListL dec sel lim kp recur s`: the store's list over the store `s` at the read revision, through
  7e-3a's loop (`ListModel.loop`): the first `lim` key-values in scope the predicate selects, whether
  a key in scope follows the `lim`-th match, the last match's key, the count of the scope;
- `limN`: a list's limit as a count; `listRevL`: the revision a list reads (`ValidateListOptions`);
- `kvSameHist σ σ'`: two states of one history (`kvSameHist_at`: they agree at every revision both
  keep); `kvWfHist c σ`: every revision's key-values under the store's prefix decode;
  `kvKeysShort σ`: every revision holds fewer than `2 ^ 41` key-values, each key shorter than
  `opKeyMax` (correction G3).
-/
module

public import Proof.k8s_io.apiserver.pkg.storage.etcd3.Store
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.ListModel

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver

/-! ## The pure part -/

section pure
variable [GooseExts]
variable {Obj : Type}

/-- **A list's scope** (`store.go:1081-1100`): recursive, the keys under the prepared prefix `kp`
(`kubernetes.Client.List`'s range `[kp, GetPrefixRangeEnd kp)`, `client.go:59-73`); not recursive,
the key `kp` itself (`kubernetes.Client.Get`, `client.go:47-57`). -/
def kInScope (kp : GoString) (recur : Bool) (k : GoString) : Bool :=
  if recur then decide (kp <+: k) else decide (k = kp)

/-- **The store's list over the store `s` at the list's revision**: the key-values of the scope in
key order, each decoded by `dec` (`ObjSpec.dec`) with its mod revision, through 7e-3a's loop
(`ListModel.loop`): the first `lim` the predicate `sel` selects (all for `lim = 0`), whether a key in
scope follows the `lim`-th match (`more`), the last match's key, and the count of keys in scope. -/
def kListL (dec : Dec Obj) (sel : Obj → Bool) (lim : Nat) (kp : GoString) (recur : Bool)
    (s : KVStore) : k8s_etcd3.ListModel.LState w8 (Obj × Nat) :=
  k8s_etcd3.ListModel.loop (fun x => sel x.1) lim
    ((s.kvs.filter fun v => kInScope kp recur v.key).filterMap fun v =>
      (dec v.value).map fun d => (v.key, (d.1, sint.nat v.modRev)))

/-- A list's limit as a count (`opts.Predicate.Limit`; none for `≤ 0`). -/
def limN (l : w64) : Nat := if 0 < sint.Z l then sint.nat l else 0

/-- **Two states of one history**: the same base and compaction revision, one's changes a prefix
of the other's (so they agree at every revision both keep: `kvSameHist_at`). -/
def kvSameHist (σ σ' : KVState) : Prop :=
  σ.compacted = σ'.compacted ∧ σ.base = σ'.base ∧
    (σ.changes <+: σ'.changes ∨ σ'.changes <+: σ.changes)

theorem take_of_prefix {α : Type} {l l' : List α} (h : l <+: l') (n : Nat) (hn : n ≤ l.length) :
    l.take n = l'.take n := by
  obtain ⟨t, rfl⟩ := h
  rw [List.take_append_of_le_length hn]

theorem kvSameHist_at (σ σ' : KVState) (r : Nat) (h : kvSameHist σ σ') (hr : r ≤ σ.rev)
    (hr' : r ≤ σ'.rev) : σ.at r = σ'.at r := by
  obtain ⟨hc, hb, hp⟩ := h
  unfold KVState.at
  rw [hc, hb]
  unfold KVState.rev at hr hr'
  split
  · rfl
  · congr 2
    rcases hp with hp | hp
    · exact take_of_prefix hp _ (by omega)
    · exact (take_of_prefix hp _ (by omega)).symm

/-- **The revision a list reads** (`ValidateListOptions`, `interfaces.go:372-410`): its resource
version `n` for `Exact`, and for the legacy match when recursive with a limit and `n > 0`; else
(`0`) the latest. -/
def listRevL (m : GoString) (recur : Bool) (lim : w64) (n : w64) : w64 :=
  if m = go!"Exact" then n
  else if m = [] ∧ recur = true ∧ 0 < sint.Z lim ∧ 0 < uint.Z n then n else W64 0

/-- **Every revision's key-values are few and their keys short** (correction G3): fewer than
`2 ^ 41` key-values (a response's `Count` and the metrics' sums stay below `2 ^ 63`), each key
shorter than `opKeyMax` (a later page's start key, the last key and `"\x00"`, is a key
`Client.List` takes). -/
def kvKeysShort (σ : KVState) : Prop :=
  ∀ R ≤ σ.rev, (σ.at R).kvs.length < 2 ^ 41 ∧
    ∀ kv ∈ (σ.at R).kvs, kv.key.length < opKeyMax

end pure

/-! ## The store's part -/

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [go_etcd_io.etcd.client.v3.Assumptions]
variable [go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable {Obj : Type} [DecidableEq Obj]

/-- **Every revision of `σ` is the store's** (D30i, at each revision a past read may read): the key-
values under the prefix decode. -/
def kvWfHist (c : StoreCfg GF Obj) (σ : KVState) : Prop :=
  ∀ r, r ≤ σ.rev → ∀ v ∈ (σ.at r).kvs, c.pfx <+: v.key → c.S.dec v.value ≠ none

end defs

end k8s
end EtcdGrove
end Perennial
