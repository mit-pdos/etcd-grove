/-
Lean-first (no Rocq counterpart).

# linkvtxn: the server's start state is the model's initial one (linkv-txn stage G)

As linkv's `Boot.lean` did: a new member's KV state is the KV model of its bootstrap log, conf changes
only, which change no KV state (`linkv.kvRaftOf_boot`), so it is the start log `[[], []]`'s: no
key, at revision `1`. That state is good (`GoodKV`) and its model state is the model's initial
one (`mInit`), what `linkvInv_alloc` takes (`linkvInv_alloc_boot`). (`linkv.kvRaftOf_boot` was
`linkv/Boot.lean`'s until linkv was retired, 2026-10-22, `notes/decisions.md` D34.)
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.linkvtxn.Inv
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvBuild

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

namespace linkv

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

end pure

end linkv

namespace linkvtxn

section alloc
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.linkvtxn.Assumptions]

/-- **`linkvInv_alloc` at a new member's start state** (see the file header). -/
theorem linkvInv_alloc_boot (γk : KVNames) (hlog : γk.log0 = [[], []])
    (ccOk : w32 → List w8 → Prop) (ps : List w64) (bootLog : List EntryM)
    (hb : BootLogOk ccOk ps bootLog) (hW : ∀ op, γk.wl.writes op) (Em : CoPset) :
    etcdKV (GF := GF) γk (kvStateOf (kvModel γk (bootEntries bootLog))) ⊢
      |={Em}=> ∃ γ : LinkvNames, linkvInv γ γk ∗ linkvState γ (linkv.pInit TS) := by
  have h : kvModel γk (bootEntries bootLog) = [[], []] := by
    unfold kvModel
    rw [linkv.kvRaftOf_boot _ _ _ ccOk ps bootLog hb, hlog]
  rw [h]
  exact linkvInv_alloc γk _ (goodKV_empty 1) rfl hW Em

end alloc

end linkvtxn
end EtcdGrove
end Perennial
