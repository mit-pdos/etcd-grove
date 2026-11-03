/-
**What the writer's pin observes** (`writerPin`'s laws, so that no client unfolds it; moved from
`etcdserver/txn/KeyObs.lean`, F2's Freeze, stage 2, review round 3): a snapshot's view of the key
bucket (`writerPin_keyObs`) and of the compaction keys (`writerPin_noCmp`). Lean-first.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvStore
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.InvSnapshot
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.ReadLemmas
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.DelKeys

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvcc

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

section pinObs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- **The writer's pin observes a snapshot of the key bucket** (M2's item 37): the pin's quarter of
the view at a bucket of `log` (`bucketViewL`: thin of `bucketMap log`, the whole of it off) and a snapshot's view `vd` of the real backend `d`: every key `vd` has
is `bucketMap log`'s, at its value (the physical view is thin of the clients' view,
`backend.viewAt_bView`), and `vd` is `bucketMap log` on the key bucket when the store does not
compact (the pin's loan: nothing deletable, `backend.thinV_exact`). -/
theorem writerPin_keyObs (γ : StoreNames) (d : KBReal) (hk : γ.kb = some d)
    (log : Log) (vd : backend.VData) :
    writerPin (GF := GF) γ log ∗ backend.viewAt d.γB vd ⊢
      ⌜(∀ k v, vd.lookup (keyName, k) = some v → (bucketMap log).lookup k = some v) ∧
        (d.cm = false → ∀ k, vd.lookup (keyName, k) = (bucketMap log).lookup k)⌝ := by
  unfold writerPin bucketViewL bucketLog snapThin bucketView kbView
    writerLoan kbCmpM kbNoDel
  rw [hk]
  simp only
  unfold bkView
  have h1 : ∀ (m : Bucket) (vd' : backend.VData), keyView vd' m →
      (∀ k v, m.lookup k = some v → (bucketMap log).lookup k = some v) →
      (∀ nk v, vd.lookup nk = some v → vd'.lookup nk = some v) →
      ∀ k v, vd.lookup (keyName, k) = some v → (bucketMap log).lookup k = some v := by
    intro m vd' Hkv Hsub Hthin k v h
    have := Hthin _ _ h
    rw [Hkv] at this
    exact Hsub k v (by simpa using this)
  rcases Bool.eq_false_or_eq_true d.cm with hc | hc
  rotate_left
  · simp only [hc, Bool.false_eq_true, ↓reduceIte, not_false_eq_true, forall_const]
    iintro ⟨⟨⟨%m, ⟨%vd', Hb, %Hkv⟩, ⟨%Hsub, -⟩, %Hoff⟩, ⟨-, #Hnd⟩, -, -⟩, Hv⟩
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
theorem writerPin_noCmp (γ : StoreNames) (d : KBReal) (hk : γ.kb = some d)
    (log : Log) (rv : backend.RView) :
    writerPin (GF := GF) γ log ∗ backend.fkRd d.γB d.P rv ⊢
      ⌜d.cm = false → backend.fkAbsRv d.P rv⌝ ∗ writerPin γ log := by
  unfold writerPin writerLoan kbCmpM kbNoCmp kbNoDel
  rw [hk]
  simp only
  rcases Bool.eq_false_or_eq_true d.cm with hc | hc
  rotate_left
  · simp only [hc, Bool.false_eq_true, ↓reduceIte]
    iintro ⟨⟨Hb, ⟨Hnc, #Hnd⟩, Hlg, #Hrg⟩, Hfk⟩
    unfold bkNoCmp
    ihave ⟨Hnc, %Habs⟩ := backend.fkRd_abs d.γB d.P rv $$ [$Hnc $Hfk]
    iframe Hb Hnc Hnd Hlg Hrg
    ipureintro; intro _; exact Habs
  · simp only [hc, ↓reduceIte]
    iintro ⟨⟨Hb, -, Hlg, #Hrg⟩, -⟩
    iframe Hb Hlg Hrg
    ipureintro; intro h; simp at h

end pinObs

end mvcc
end EtcdGrove
end Perennial
