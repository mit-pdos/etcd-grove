/-
**`persistent.law` and `mvccState_reachable.law`** (2026-11-06). Lean-first (no Rocq counterpart).
Over the sealed definitions of `Api.lean` (imported with `import all`).

`persistent.law` gathers the instances (`SnapLaws`, `WatchLaws`, `Api.lean`'s `hookIs_persistent`,
the backend's `commitReq_persistent`). `mvccState_reachable.law`: the client's state carries the
committed log's persistent receipt (`mvccStateI`'s `⧖ (logCh σ.log)`), below the store's
`receiptBound ≤ 2 ^ 48` (`isStore`'s), and a reachable log has a change in each revision past the
first two (`reach_len`: an empty notification leaves nothing pending, and a commit appends only the
pending revision), so its length is at most `2 ^ 48 + 2`.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.Api
import all Spec.go_etcd_io.etcd.server.v3.storage.mvcc.Api
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Api.SnapLaws
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Api.WatchLaws

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvcc
namespace api

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- **A reachable log has a change in each revision past the first two**, and nothing empty is
pending. -/
theorem reach_len (σ : MvccState) (h : MvccReachable σ) :
    σ.log.length ≤ logCh σ.log + 2 ∧ σ.pending ≠ some [] := by
  induction h with
  | start => exact ⟨by simp [mvccStart, logCh], by simp [mvccStart]⟩
  | notify σ pend _ _ _ ih =>
    refine ⟨ih.1, ?_⟩
    simp only [MvccState.notify]
    split
    · simp
    · rename_i hne; intro h; injection h with h; exact hne h
  | commit σ _ ih =>
    obtain ⟨hl, hp⟩ := ih
    simp only [MvccState.commitPending]
    refine ⟨?_, by simp⟩
    cases hpe : σ.pending with
    | none => simp only [Option.getD_none, commitLog, ↓reduceIte]; exact hl
    | some p =>
      have hne : p ≠ [] := fun h => hp (by rw [hpe, h])
      have hp0 : 0 < p.length := List.length_pos_iff.2 hne
      have hc := logCh_snoc σ.log p
      simp only [Option.getD_some, commitLog, hne, ↓reduceIte, List.length_append,
        List.length_singleton]
      omega
  | compact σ r _ _ _ _ _ ih => exact ih

theorem persistent.law_holds : persistent.law (GF := GF) := by
  refine ⟨fun kv γ => inferInstance, fun ws γ ι => inferInstance, fun ι n => inferInstance,
    fun B f => inferInstance, fun B Pk X Y => ?_, fun γ σ => inferInstance,
    fun ι S => inferInstance, fun ι rs => inferInstance, fun γ B Pk => inferInstance⟩
  unfold storageReq; infer_instance

/-- The store's receipt bound, from its handle. -/
theorem isMvcc_rb (kv : GoInterface) (γ : MvccName) :
    isMvcc (GF := GF) kv γ ⊢ ⌜receiptBound GF ≤ 2 ^ 48⌝ := by
  iintro Hmv
  iunfold isMvcc at Hmv
  icases Hmv with #(⟨Hmv, -⟩ | Hmv)
  · iunfold isMvccPlain at Hmv
    icases Hmv with ⟨%s, -, #Hs, -⟩
    iunfold isStore at Hs
    iNamed Hs
    ipureintro; exact Hrb
  · iunfold isMvccWatchable at Hmv
    icases Hmv with ⟨%s, %st, %γw, %γp, -, #Hws, -⟩
    iunfold isWatchableStore at Hws
    iNamed Hws
    iunfold isStore at Hs
    iNamed Hs
    ipureintro; exact Hrb

theorem mvccState_reachable.law_holds : mvccState_reachable.law (GF := GF) := by
  intro kv γ σ
  iintro ⟨Hmv, Hσ⟩
  ihave %hrb := isMvcc_rb kv γ $$ Hmv
  iunfold mvccState at Hσ
  iunfold mvccStateI at Hσ
  icases Hσ with ⟨-, -, -, -, %Hreach, #Hrc⟩
  ihave %hlt := preceipt_lt _ $$ Hrc
  ipureintro
  have := (reach_len σ Hreach).1
  exact ⟨Hreach, by omega⟩

end laws

end api
end mvcc
end EtcdGrove
end Perennial
