/-
**The writer's observation of the key bucket** (the merged snapshot's window, S2,
`etcdserver.mergedCreate_window`; `notes/decisions.md`, "The merged snapshot's window: the writer's
key observation"). Lean-first (no Rocq counterpart).

`kvWriter_keyObs`: the sole writer at the committed log `log` and a view of the backend's data
(`backend.viewAt`) sees the key bucket at most `bucketMap log`, and exactly `bucketMap log` when
the backend's store does not compact (`d.cm = false`). `kvWriter_noCmp`: with compaction off, a
snapshot's data records no compaction (the reader's bound `backend.fkRd` that `backend.Snapshot`
gives). Both from the writer's pin (`mvcc.writerPin`, in `wlogOwn`; M2's item 37, 2026-11-02:
until then named `sorry`s over the batch lock's resource `lateW`, which a restore leaves
unregistered).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.Writer
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.InvSnapshot
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.ReadLemmas
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.DelKeys

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace txn

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

section keyObs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.txn.Assumptions]

/-- **The writer's pin observes a snapshot of the key bucket** (M2's item 37): the pin's quarter of
the view at a bucket of `log` (`bucketViewL`: thin of `bucketMap log`, the whole of it off) and a snapshot's view `vd` of the real backend `d`: every key `vd` has
is `bucketMap log`'s, at its value (the physical view is thin of the clients' view,
`backend.viewAt_bView`), and `vd` is `bucketMap log` on the key bucket when the store does not
compact (the pin's loan: nothing deletable, `backend.thinV_exact`). -/
theorem writerPin_keyObs (γ : mvcc.StoreNames) (d : mvcc.KBReal) (hk : γ.kb = some d)
    (log : mvcc.Log) (vd : backend.VData) :
    mvcc.writerPin (GF := GF) γ log ∗ backend.viewAt d.γB vd ⊢
      ⌜(∀ k v, vd.lookup (mvcc.keyName, k) = some v → (mvcc.bucketMap log).lookup k = some v) ∧
        (d.cm = false → ∀ k, vd.lookup (mvcc.keyName, k) = (mvcc.bucketMap log).lookup k)⌝ := by
  unfold mvcc.writerPin mvcc.bucketViewL mvcc.bucketLog mvcc.snapThin mvcc.bucketView mvcc.kbView
    mvcc.writerLoan mvcc.kbCmpM mvcc.kbNoDel
  rw [hk]
  simp only
  unfold mvcc.bkView
  have h1 : ∀ (m : mvcc.Bucket) (vd' : backend.VData), mvcc.keyView vd' m →
      (∀ k v, m.lookup k = some v → (mvcc.bucketMap log).lookup k = some v) →
      (∀ nk v, vd.lookup nk = some v → vd'.lookup nk = some v) →
      ∀ k v, vd.lookup (mvcc.keyName, k) = some v → (mvcc.bucketMap log).lookup k = some v := by
    intro m vd' Hkv Hsub Hthin k v h
    have := Hthin _ _ h
    rw [Hkv] at this
    exact Hsub k v (by simpa using this)
  rcases Bool.eq_false_or_eq_true d.cm with hc | hc
  rotate_left
  · simp only [hc, Bool.false_eq_true, ↓reduceIte, not_false_eq_true, forall_const]
    iintro ⟨⟨⟨%m, ⟨%vd', Hb, %Hkv⟩, ⟨%Hsub, -⟩, %Hoff⟩, -, #Hnd⟩, Hv⟩
    subst Hoff
    ihave ⟨-, -, #Ht⟩ := backend.viewAt_bView d.γB vd vd' _ $$ [$Hv $Hb]
    ihave #Ht' := Ht
    iunfold backend.thinV at Ht'
    icases Ht' with ⟨%Hthin, -⟩
    ihave %Heq := backend.thinV_exact d.γB vd vd' $$ [$Hnd $Ht]
    subst Heq
    ipureintro
    refine ⟨h1 _ vd Hkv Hsub Hthin, fun k => ?_⟩
    rw [Hkv]; simp
  · simp only [hc, ↓reduceIte]
    iintro ⟨⟨⟨%m, ⟨%vd', Hb, %Hkv⟩, ⟨%Hsub, -⟩, -⟩, -⟩, Hv⟩
    ihave ⟨-, -, #Ht⟩ := backend.viewAt_bView d.γB vd vd' _ $$ [$Hv $Hb]
    iunfold backend.thinV at Ht
    icases Ht with ⟨%Hthin, -⟩
    ipureintro
    exact ⟨h1 m vd' Hkv Hsub Hthin, fun h => by simp at h⟩

/-- **The writer's pin rules out the compaction keys** (M2's item 37): a reader's bound of the
real backend's compaction-key flag (`backend.fkRd`) at the view `rv` finds no compaction key when
the store does not compact (the pin's loan: the client's half of the flag at `0`,
`backend.fkRd_abs`). -/
theorem writerPin_noCmp (γ : mvcc.StoreNames) (d : mvcc.KBReal) (hk : γ.kb = some d)
    (log : mvcc.Log) (rv : backend.RView) :
    mvcc.writerPin (GF := GF) γ log ∗ backend.fkRd d.γB d.P rv ⊢
      ⌜d.cm = false → backend.fkAbsRv d.P rv⌝ ∗ mvcc.writerPin γ log := by
  unfold mvcc.writerPin mvcc.writerLoan mvcc.kbCmpM mvcc.kbNoCmp mvcc.kbNoDel
  rw [hk]
  simp only
  rcases Bool.eq_false_or_eq_true d.cm with hc | hc
  rotate_left
  · simp only [hc, Bool.false_eq_true, ↓reduceIte]
    iintro ⟨⟨Hb, Hnc, #Hnd⟩, Hfk⟩
    unfold mvcc.bkNoCmp
    ihave ⟨Hnc, %Habs⟩ := backend.fkRd_abs d.γB d.P rv $$ [$Hnc $Hfk]
    iframe Hb Hnc Hnd
    ipureintro; intro _; exact Habs
  · simp only [hc, ↓reduceIte]
    iintro ⟨⟨Hb, -⟩, -⟩
    iframe Hb
    ipureintro; intro h; simp at h

/-- **The writer's observation of the key bucket**: the sole writer of the store `(s, γ)` over the
real backend `d` at the log `log` and a view `vd` of its data: every key `vd` has is `bucketMap
log`'s, at its value (thin, both modes: the compaction deletes keys physically), and `vd` is
`bucketMap log` on the key bucket when the store does not compact (the writer's pin,
`writerPin_keyObs`). -/
theorem kvWriter_keyObs (s : Loc) (γ : mvcc.StoreNames) (d : mvcc.KBReal) (hk : γ.kb = some d)
    (log : mvcc.Log) (vd : backend.VData) :
    kvWriter (GF := GF) s γ log ∗ backend.viewAt d.γB vd ⊢
      ⌜(∀ k v, vd.lookup (mvcc.keyName, k) = some v → (mvcc.bucketMap log).lookup k = some v) ∧
        (d.cm = false → ∀ k, vd.lookup (mvcc.keyName, k) = (mvcc.bucketMap log).lookup k)⌝ := by
  iintro ⟨Hkw, Hv⟩
  iunfold kvWriter at Hkw
  icases Hkw with ⟨-, Hwl, -⟩
  iunfold wlogOwn at Hwl
  icases Hwl with ⟨-, Hpin⟩
  iapply writerPin_keyObs γ d hk log vd $$ [$Hpin $Hv]

/-- **The writer rules out the compaction keys**: a reader's bound of the real backend's
compaction-key flag finds none when the store does not compact (`writerPin_noCmp`). -/
theorem kvWriter_noCmp (s : Loc) (γ : mvcc.StoreNames) (d : mvcc.KBReal) (hk : γ.kb = some d)
    (log : mvcc.Log) (rv : backend.RView) :
    kvWriter (GF := GF) s γ log ∗ backend.fkRd d.γB d.P rv ⊢
      ⌜d.cm = false → backend.fkAbsRv d.P rv⌝ ∗ kvWriter s γ log := by
  iintro ⟨Hkw, Hfk⟩
  iunfold kvWriter at Hkw
  icases Hkw with ⟨Hsw, Hwl, Hf⟩
  iunfold wlogOwn at Hwl
  icases Hwl with ⟨Hw, Hpin⟩
  ihave ⟨%Habs, Hpin⟩ := writerPin_noCmp γ d hk log rv $$ [$Hpin $Hfk]
  isplitl []
  · ipureintro; exact Habs
  iunfold kvWriter
  iframe Hsw Hf
  iunfold wlogOwn
  iframe Hw Hpin

end keyObs

end txn
end EtcdGrove
end Perennial
