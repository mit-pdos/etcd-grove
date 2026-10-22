/-
Lean-first (no Rocq counterpart).

# The server's start store is empty (D20 (c), 2026-10-19)

A new member's KV state is the KV model of its bootstrap log (`common.alloc1`'s `etcdKV` at
`kvStateOf (kvModel γk (bootEntries bootLog))`, with `γk.log0 = [[], []]`). The bootstrap log is
conf changes only (`BootLogOk`: every entry of type `1`), which change no KV state (`kvEntry`
dispatches only normal entries), so the model is the start log `[[], []]`, whose state has no key:
`absKV` of it is empty and its key-values are sorted, what `linkvInv_alloc` takes
(`linkvInv_alloc_boot`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.linkv.Inv
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvBuild

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace linkv

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section pure
variable [ext : FfiSyntax]

/-- A bootstrap log's entries change no KV state: they are conf changes. -/
theorem kvRaftOf_boot (c₀ : w64) (ch : apply.Chain) (log₀ : mvcc.Log)
    (ccOk : w32 → List w8 → Prop) (ps : List w64) (bootLog : List EntryM)
    (hb : BootLogOk ccOk ps bootLog) : kvRaftOf c₀ ch log₀ (bootEntries bootLog) = log₀ := by
  obtain ⟨-, -, he⟩ := hb
  unfold kvRaftOf bootEntries
  rw [List.foldl_map]
  suffices h : ∀ (l : List EntryM), (∀ e ∈ l, e.Type' = W32 1) →
      l.foldl (fun log e => kvEntry c₀ ch log (EntryModel.ofM e)) log₀ = log₀ by
    apply h
    intro e hm
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hm
    exact (he k _ (List.getElem?_eq_getElem hk)).2.2.1
  intro l
  induction l with
  | nil => intro _; rfl
  | cons e l ih =>
    intro hl
    rw [List.foldl_cons]
    have ht : e.Type' = W32 1 := hl e (List.mem_cons_self ..)
    have : kvEntry c₀ ch log₀ (EntryModel.ofM e) = log₀ := by
      unfold kvEntry
      simp only [EntryModel.ofM, ht]
      rfl
    rw [this]
    exact ih (fun e' h' => hl e' (List.mem_cons_of_mem _ h'))

/-- The start log's state has no key. -/
theorem stateAfter_start : mvcc.stateAfter [[], []] = [] := rfl

/-- **The server's start store**: the KV model of a bootstrap log from the start log `[[], []]`
is empty and sorted. -/
theorem boot_store_empty (γk : KVNames) (hlog : γk.log0 = [[], []])
    (ccOk : w32 → List w8 → Prop) (ps : List w64) (bootLog : List EntryM)
    (hb : BootLogOk ccOk ps bootLog) :
    (kvStateOf (kvModel γk (bootEntries bootLog))).kvs.Pairwise etcdKvLess ∧
      absKV (kvStateOf (kvModel γk (bootEntries bootLog))) = fun _ => none := by
  have h : kvModel γk (bootEntries bootLog) = [[], []] := by
    unfold kvModel
    rw [kvRaftOf_boot _ _ _ ccOk ps bootLog hb, hlog]
  rw [h]
  refine ⟨mvcc.stateAfter_sorted _, ?_⟩
  funext k
  simp only [absKV, kvStateOf, stateAfter_start]
  rfl

end pure

section alloc
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.linkv.Assumptions]

/-- **`linkvInv_alloc` at a new member's start state** (see the file header). -/
theorem linkvInv_alloc_boot (γk : KVNames) (hlog : γk.log0 = [[], []])
    (ccOk : w32 → List w8 → Prop) (ps : List w64) (bootLog : List EntryM)
    (hb : BootLogOk ccOk ps bootLog) (hW : ∀ op, γk.wl.writes op) (Em : CoPset) :
    etcdKV (GF := GF) γk (kvStateOf (kvModel γk (bootEntries bootLog))) ⊢
      |={Em}=> ∃ γ : LinkvNames, linkvInv γ γk ∗ linkvState γ kvInit :=
  have h := boot_store_empty γk hlog ccOk ps bootLog hb
  linkvInv_alloc γk _ h.1 h.2 hW Em

end alloc

end linkv
end EtcdGrove
end Perennial
