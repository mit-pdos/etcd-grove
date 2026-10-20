/-
Lean-first (no Rocq counterpart).

# linkvtxn: the server's start state is the model's initial one (linkv-txn stage G)

As `linkv/Boot.lean`: a new member's KV state is the KV model of its bootstrap log, conf changes
only, which change no KV state (`linkv.kvRaftOf_boot`), so it is the start log `[[], []]`'s: no
key, at revision `1`. That state is good (`GoodKV`) and its model state is the model's initial
one (`mInit`), what `linkvInv_alloc` takes (`linkvInv_alloc_boot`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.linkvtxn.Inv
public import Proof.github_com.mit_pdos.etcd_grove.examples.linkv.Boot

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace linkvtxn

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

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
