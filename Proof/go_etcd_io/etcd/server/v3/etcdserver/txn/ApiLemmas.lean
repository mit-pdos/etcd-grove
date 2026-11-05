/-
The txn proofs' lemmas over mvcc's API (strict M1, 2026-11-05): a transaction's and a store
handle's dynamic type meets its interface's contracts (from `shapes.law`), keeping the resource.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.ApiVocab

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc
open mvcc.api (MvccState MTxn MvccName)

/-- A reachable state's log has `NewStore`'s two revisions. -/
theorem txn.reach_len (σ : MvccState) (h : mvcc.api.MvccReachable σ) : 2 ≤ σ.log.length := by
  induction h with
  | start => decide
  | notify σ pend _ _ _ ih => exact ih
  | commit σ _ ih =>
    unfold mvcc.api.MvccState.commitPending mvcc.commitLog
    split
    · exact ih
    · simp only [List.length_append, List.length_singleton]; omega
  | compact σ r _ _ _ _ _ ih => exact ih

/-- A reachable state's compaction revision is in `[-1, rev]`. -/
theorem txn.reach_crev (σ : MvccState) (h : mvcc.api.MvccReachable σ) :
    -1 ≤ σ.crev ∧ σ.crev ≤ (σ.rev : Int) := by
  induction h with
  | start => simp [mvcc.api.mvccStart, mvcc.api.MvccState.rev]
  | notify σ pend _ _ _ ih => exact ih
  | commit σ _ ih =>
    refine ⟨ih.1, ?_⟩
    have : σ.rev ≤ σ.commitPending.rev := by
      unfold mvcc.api.MvccState.commitPending mvcc.api.MvccState.rev mvcc.commitLog
      split <;> simp <;> omega
    have h2 : σ.commitPending.crev = σ.crev := rfl
    rw [h2]; omega
  | compact σ r _ _ h1 h2 h3 ih =>
    exact ⟨by simp [mvcc.api.MvccState.compactTo]; omega, by
      simpa [mvcc.api.MvccState.compactTo, mvcc.api.MvccState.rev] using h3⟩

/-- A transaction's begin state after changes. -/
theorem txn.MTxn.append_state (k : MTxn) (chs : List mvcc.Change) :
    (txn.MTxn.append k chs).state = k.state := by cases k <;> rfl

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.txn.Assumptions]

/-- **A transaction is an interface value whose type meets `TxnWrite`'s contracts**
(`shapes.law`), the transaction kept. -/
theorem txn.mvccTxn_shape (hsh : mvcc.api.shapes.law (GF := GF) (hG := hG))
    (t : GoInterface) (γ : MvccName) (trace : Loc) (k : MTxn) :
    mvcc.api.mvccTxn (GF := GF) t γ trace k ⊢
      ⌜∃ ty v, t = interface.mkOk ty v ∧ mvcc.api.isTxn (GF := GF) ty v⌝ ∗
        mvcc.api.mvccTxn t γ trace k :=
  persistent_entails_right (hsh.2.2.1 t γ trace k)

/-- **A store handle is an interface value whose type meets `KV`'s contracts** (`shapes.law`),
the handle kept. -/
theorem txn.isMvcc_shape (hsh : mvcc.api.shapes.law (GF := GF) (hG := hG))
    (kv : GoInterface) (γ : MvccName) :
    mvcc.api.isMvcc (GF := GF) kv γ ⊢
      ⌜∃ ty v, kv = interface.mkOk ty v ∧ mvcc.api.isKV (GF := GF) ty v⌝ ∗ mvcc.api.isMvcc kv γ :=
  persistent_entails_right (hsh.1 kv γ)

/-- **The caller's read update, with what txn records of its state** (`clients-txn.md` §3, the
wrapper): given the store's handle, the caller's update at a read becomes one whose commit also
gives `Reach σ` (`mvccState_reachable.law` at the state in hand). -/
theorem txn.readAU_reach (hpers : mvcc.api.persistent.law (GF := GF) (hG := hG))
    (hreach : mvcc.api.mvccState_reachable.law (GF := GF) (hG := hG))
    (kv : GoInterface) (γ : MvccName) (Q : MvccState → IProp GF) :
    mvcc.api.isMvcc kv γ ⊢
      txn.readAU γ Q -∗ txn.readAU γ (fun σ => iprop(Q σ ∗ ⌜txn.Reach σ⌝)) := by
  haveI := hpers.1 kv γ
  iintro #Hkv Hau
  unfold txn.readAU
  iauintro
  ihave Hacc := aupd_aacc $$ Hau
  unfold atomic_acc
  imod Hacc with Hacc
  isimp only [texist_cons, texist_nil, Std.Tele.app, ULift.down] at Hacc
  icases Hacc with ⟨%x, Hx, Hcl⟩
  imodintro
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
  iexists x
  iframe Hx
  isplit
  · iintro Hx
    icases Hcl with ⟨Hab, -⟩
    iapply Hab $$ Hx
  · iintro Hx
    icases (persistent_entails_right (hreach kv γ x)) $$ [$Hkv $Hx] with ⟨%Hr, -, Hx⟩
    icases Hcl with ⟨-, Hco⟩
    isimp only [tforall_cons, tforall_nil, Std.Tele.app, ULift.down] at Hco
    imod Hco $$ Hx with HQ
    imodintro
    iframe HQ
    ipureintro; exact Hr

/-- **The caller's begin update, with what txn records of its state**: the commit also gives
`Reach σ` and the promised `σ.pending = none`. -/
theorem txn.beginAU_reach (hpers : mvcc.api.persistent.law (GF := GF) (hG := hG))
    (hreach : mvcc.api.mvccState_reachable.law (GF := GF) (hG := hG))
    (kv : GoInterface) (γ : MvccName) (R : MvccState → IProp GF) :
    mvcc.api.isMvcc kv γ ⊢
      txn.beginAU γ R -∗
        txn.beginAU γ (fun σ => iprop(⌜txn.Reach σ ∧ σ.pending = none⌝ ∗ R σ)) := by
  haveI := hpers.1 kv γ
  iintro #Hkv Hau
  unfold txn.beginAU
  iauintro
  ihave Hacc := aupd_aacc $$ Hau
  unfold atomic_acc
  imod Hacc with Hacc
  isimp only [texist_cons, texist_nil, Std.Tele.app, ULift.down] at Hacc
  icases Hacc with ⟨%x, Hx, Hcl⟩
  imodintro
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
  iexists x
  iframe Hx
  isplit
  · iintro Hx
    icases Hcl with ⟨Hab, -⟩
    iapply Hab $$ Hx
  · iintro ⟨%Hpn, Hx⟩
    icases (persistent_entails_right (hreach kv γ x)) $$ [$Hkv $Hx] with ⟨%Hr, -, Hx⟩
    icases Hcl with ⟨-, Hco⟩
    isimp only [tforall_cons, tforall_nil, Std.Tele.app, ULift.down] at Hco
    imod Hco $$ [Hx] with HR
    · iframe Hx; ipureintro; exact Hpn
    imodintro
    iframe HR
    ipureintro; exact ⟨Hr, Hpn⟩

/-- **A read transaction's `End`**: the thread token back (`Txn.End.contract` at a read
transaction, whose backend arguments do not matter). -/
theorem txn.end_read {ty : go.GoType} {v : val}
    (hEnd : mvcc.api.Txn.End.contract (GF := GF) (hG := hG) ty v)
    (γ : MvccName) (trace : Loc) (σ : MvccState) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
        mvcc.api.mvccTxn (interface.mkOk ty v) γ trace (.read σ) }}
      (App (Val #(methods ty go!"End" v)) (Val #()))
    {{ RET #(); threadTok }} := by
  have hB : Nonempty mvcc.api.BkRef := by
    refine ⟨⟨?_, ?_, null⟩⟩
    · constructor <;> first | exact default | (constructor <;> exact default)
    · constructor <;> exact default
  obtain ⟨B⟩ := hB
  iintro %Φ ⟨#Hpkg, Htx⟩ HΦ
  iapply (hEnd γ trace (.read σ) 1 B iprop(True) iprop(True)) $$ [Htx]
  · iframe Hpkg Htx
  inext
  iintro ⟨Htt, -⟩
  iapply HΦ $$ Htt

/-- **A write transaction's `End`**: the caller's two commit updates (`commitAU`, `Txn.End`'s
shape), the batch lock's invariant `P` given, the backend share and the thread token back. -/
theorem txn.end_write {ty : go.GoType} {v : val}
    (hEnd : mvcc.api.Txn.End.contract (GF := GF) (hG := hG) ty v)
    (γ : MvccName) (trace : Loc) (σ₀ : MvccState) (pend : List mvcc.Change) (q : Qp)
    (B : mvcc.api.BkRef) (P Q : IProp GF) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
        mvcc.api.mvccTxn (interface.mkOk ty v) γ trace (.write σ₀ pend) ∗
        mvcc.api.mvccBackend γ q B P ∗ P ∗ txn.commitAU γ σ₀ pend Q }}
      (App (Val #(methods ty go!"End" v)) (Val #()))
    {{ RET #(); threadTok ∗ mvcc.api.mvccBackend γ q B P ∗ Q }} := by
  have h := hEnd γ trace (.write σ₀ pend) q B P Q
  dsimp only at h
  iintro %Φ ⟨#Hpkg, Htx, Hbk, HP, Hau⟩ HΦ
  iapply h $$ [Htx Hbk HP Hau]
  · iframe Hpkg Htx Hbk HP
    iexact Hau
  inext
  iintro ⟨Htt, Hbk, HQ⟩
  iapply HΦ
  iframe Htt Hbk HQ

end lemmas

end EtcdGrove
end Perennial
