/-
Lean-first (no Rocq counterpart).

# The store's atomic updates (D30h, `notes/k8s-etcd3-plan.md` phase 4)

- `k8sAu1 γk c step Φ`: the caller's update for an operation that writes, fired at most once: at a
  state of the store `σ` (`kvWf`, with room for one more revision), the next state is any state of
  the store whose model is the model's `step`'s (`∀∀ σ'`: the store chooses it, the transaction it
  sends), and the caller learns `Φ σ`. Relational, since the caller cannot name the transaction:
  its value is the transformer's (encryption may be randomized).
- `k8sAu1_kvAu1`: such an update gives the client's update (`kvAu1`) for a transaction whose step
  keeps the store's states and moves the model as `step` (`StepOk`), whose result also says the
  state it fired at was the store's.
-/
module

public import Proof.k8s_io.apiserver.pkg.storage.etcd3.Store

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [go_etcd_io.etcd.client.v3.Assumptions]
variable [go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable {Obj : Type} [DecidableEq Obj]

/-- **The caller's update for a write** (see the file header). -/
def k8sAu1 (γk : KVNames) (c : StoreCfg GF Obj) (step : KSt Obj → KSt Obj)
    (Φ : KVState → IProp GF) : IProp GF :=
  iprop(AU <{ ∃∃ (σ : KVState), etcdKV γk σ ∗ ⌜kvWf c σ ∧ σ.rev + 2 < 2 ^ 63⌝ ∗ kvSeen c.γh σ }>
      @ (⊤ \ ↑srvRaftN) \ ↑kvN, ∅
    <{ ∀∀ (σ' : KVState), etcdKV γk σ' ∗ ⌜kvWf c σ' ∧ c.abs σ' = step (c.abs σ)⌝, COMM Φ σ }>)

/-- **A transaction's step is the model's** at the store's states (with room for a revision). -/
def StepOk (c : StoreCfg GF Obj) (op : KVOp) (step : KSt Obj → KSt Obj) : Prop :=
  ∀ σ, kvWf c σ → σ.rev + 2 < 2 ^ 63 →
    kvWf c (kvOpStep op σ) ∧ c.abs (kvOpStep op σ) = step (c.abs σ)

/-- **The caller's update gives the client's** for a transaction whose step is the model's. -/
theorem k8sAu1_kvAu1 (γk : KVNames) (c : StoreCfg GF Obj) (op : KVOp)
    (step : KSt Obj → KSt Obj) (Φ : KVState → IProp GF) (h : StepOk c op step) :
    k8sAu1 γk c step Φ ⊢
      kvAu1 γk (kvOpStep op)
        (fun σ => iprop(Φ σ ∗ ⌜kvWf c σ ∧ σ.rev + 2 < 2 ^ 63⌝ ∗ kvSeen c.γh σ)) := by
  unfold kvAu1
  refine (BI.and_intro BI.true_intro .rfl).trans (aupd_intro ?_)
  iintro ⟨-, HAU⟩
  unfold k8sAu1
  ihave HAC := aupd_aacc $$ HAU
  iunfold atomic_acc at HAC
  unfold atomic_acc
  imod HAC with HAC
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down] at HAC
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
  icases HAC with ⟨%σ, ⟨Hkv, %Hwf, #Hseen⟩, Hcl⟩
  imodintro
  iexists σ
  iframe Hkv
  isplit
  · iintro Hkv
    icases Hcl with ⟨Habort, -⟩
    iapply Habort
    iframe Hkv Hseen
    ipureintro; exact Hwf
  · iintro Hkv
    icases Hcl with ⟨-, Hcommit⟩
    obtain ⟨hwf', habs⟩ := h σ Hwf.1 Hwf.2
    ispecialize Hcommit $$ %(kvOpStep op σ)
    imod Hcommit $$ [Hkv] with HΦ
    · iframe Hkv
      ipureintro; exact ⟨hwf', habs⟩
    imodintro
    iframe HΦ Hseen
    ipureintro; exact Hwf

/-- **The caller's update for an operation that may write, read-like outcomes persistent** (see
the file header). -/
def k8sAuRW (γk : KVNames) (c : StoreCfg GF Obj) (step : KSt Obj → KSt Obj) (W : IProp GF)
    (Q Φ : KVState → IProp GF) : IProp GF :=
  iprop(□ AU <{ ∃∃ (σ : KVState), etcdKV γk σ ∗ ⌜kvWf c σ ∧ σ.rev + 2 < 2 ^ 63⌝ ∗ kvSeen c.γh σ }>
      @ (⊤ \ ↑srvRaftN) \ ↑kvN, ∅
    <{ ∀∀ (b : Bool) (σ' : KVState), etcdKV γk σ' ∗
        (if b then W ∗ ⌜kvWf c σ' ∧ c.abs σ' = step (c.abs σ)⌝ else ⌜σ' = σ⌝),
      COMM if b then Φ σ else □ Q σ }>)

instance k8sAuRW_persistent (γk : KVNames) (c : StoreCfg GF Obj) (step : KSt Obj → KSt Obj)
    (W : IProp GF) (Q Φ : KVState → IProp GF) : Persistent (k8sAuRW γk c step W Q Φ) := by
  unfold k8sAuRW; infer_instance

/-- What a read through `k8sAuRW` learns of the state it fired at. -/
def rdOk (c : StoreCfg GF Obj) (Q : KVState → IProp GF) (σ : KVState) : IProp GF :=
  iprop(□ Q σ ∗ ⌜kvWf c σ ∧ σ.rev + 2 < 2 ^ 63⌝ ∗ kvSeen c.γh σ)

instance rdOk_persistent (c : StoreCfg GF Obj) (Q : KVState → IProp GF) (σ : KVState) :
    Persistent (rdOk c Q σ) := by
  unfold rdOk; infer_instance

/-- **The update fires as a read.** -/
theorem k8sAuRW_read (γk : KVNames) (c : StoreCfg GF Obj) (step : KSt Obj → KSt Obj)
    (W : IProp GF) (Q Φ : KVState → IProp GF) :
    k8sAuRW γk c step W Q Φ ⊢ kvReadAu γk (rdOk c Q) := by
  have h : k8sAuRW γk c step W Q Φ ⊢
      AU <{ ∃∃ (σ : KVState), etcdKV γk σ }> @ (⊤ \ ↑srvRaftN) \ ↑kvN, ∅
        <{ etcdKV γk ((fun σ => σ) σ), COMM □ rdOk c Q σ }> := by
    refine (BI.and_intro BI.true_intro .rfl).trans (aupd_intro ?_)
    iintro ⟨-, #HAU⟩
    unfold k8sAuRW
    ihave HAC := aupd_aacc $$ HAU
    iunfold atomic_acc at HAC
    unfold atomic_acc
    imod HAC with HAC
    isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down] at HAC
    isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
    icases HAC with ⟨%σ, ⟨Hkv, %Hwf, #Hseen⟩, Hcl⟩
    imodintro
    iexists σ
    iframe Hkv
    isplit
    · iintro Hkv
      icases Hcl with ⟨Habort, -⟩
      imod Habort $$ [Hkv] with -
      · iframe Hkv Hseen
        ipureintro; exact Hwf
      imodintro
      iexact HAU
    · iintro Hkv
      icases Hcl with ⟨-, Hcommit⟩
      ispecialize Hcommit $$ %false %σ
      isimp only [Bool.false_eq_true, ↓reduceIte] at Hcommit
      imod Hcommit $$ [Hkv] with #HQ
      · iframe Hkv
      imodintro
      imodintro
      unfold rdOk
      iframe HQ Hseen
      ipureintro; exact Hwf
  unfold kvReadAu kvAu
  iintro #H
  imodintro
  ihave H2 := h $$ H
  iexact H2

/-- **A conditional transaction's update, from the caller's** (see the file header): at a state
of the store where `A` holds (what the store's history `kvSeen` tells, `HA`), the transaction's
step is the model's when it succeeds (`ok σ`) and the identity when it fails; it fires the
caller's update as the write, or as a read, giving `W` back. -/
theorem k8sAuRW_kvAu1 (γk : KVNames) (c : StoreCfg GF Obj) (step : KSt Obj → KSt Obj)
    (W : IProp GF) (Q Φ : KVState → IProp GF) (op : KVOp) (ok : KVState → Bool)
    (A : KVState → Prop)
    (h : ∀ σ, kvWf c σ → σ.rev + 2 < 2 ^ 63 → A σ →
      (ok σ = true → kvWf c (kvOpStep op σ) ∧ c.abs (kvOpStep op σ) = step (c.abs σ)) ∧
      (ok σ = false → kvOpStep op σ = σ)) :
    k8sAuRW γk c step W Q Φ ∗ W ∗ □ (∀ σ, kvSeen c.γh σ -∗ ⌜A σ⌝) ⊢
      kvAu1 γk (kvOpStep op) (fun σ => iprop((if ok σ then Φ σ else iprop(□ Q σ ∗ W)) ∗
        ⌜kvWf c σ ∧ σ.rev + 2 < 2 ^ 63 ∧ A σ⌝ ∗ kvSeen c.γh σ)) := by
  unfold kvAu1
  refine (BI.and_intro BI.true_intro .rfl).trans (aupd_intro ?_)
  iintro ⟨-, #HAU, HW, #HA⟩
  unfold k8sAuRW
  ihave HAC := aupd_aacc $$ HAU
  iunfold atomic_acc at HAC
  unfold atomic_acc
  imod HAC with HAC
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down] at HAC
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
  icases HAC with ⟨%σ, ⟨Hkv, %Hwf, #Hseen⟩, Hcl⟩
  ihave %HAσ := HA $$ %σ Hseen
  have hst := h σ Hwf.1 Hwf.2 HAσ
  imodintro
  iexists σ
  iframe Hkv
  isplit
  · iintro Hkv
    icases Hcl with ⟨Habort, -⟩
    imod Habort $$ [Hkv] with -
    · iframe Hkv Hseen
      ipureintro; exact Hwf
    imodintro
    iframe HAU HW HA
  · icases Hcl with ⟨-, Hcommit⟩
    cases hok : ok σ
    · rw [hst.2 hok]
      iintro Hkv
      ispecialize Hcommit $$ %false %σ
      isimp only [Bool.false_eq_true, ↓reduceIte] at Hcommit
      imod Hcommit $$ [Hkv] with #HQ
      · iframe Hkv
      imodintro
      isimp only [Bool.false_eq_true, ↓reduceIte]
      iframe HQ HW Hseen
      ipureintro; exact ⟨Hwf.1, Hwf.2, HAσ⟩
    · obtain ⟨hwf', habs⟩ := hst.1 hok
      iintro Hkv
      ispecialize Hcommit $$ %true %(kvOpStep op σ)
      isimp only [↓reduceIte] at Hcommit
      imod Hcommit $$ [Hkv HW] with HΦ
      · iframe Hkv HW
        ipureintro; exact ⟨hwf', habs⟩
      imodintro
      isimp only [↓reduceIte]
      iframe HΦ Hseen
      ipureintro; exact ⟨Hwf.1, Hwf.2, HAσ⟩

end defs

end k8s
end EtcdGrove
end Perennial
