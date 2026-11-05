/-
**The compactor example's invariant** (K4 of `notes/k8s-compactor-plan.md`, its second part).
Lean-first.

`Main` (`examples/k8s/compactor/compactor.go`) owns the clients' half of etcd's KV state
(`etcdKV`, which `etcdstart.alloc1_false` hands it at the member's start state) in one invariant,
`cinv`, with the protocol of `compact_rev_key` that the compactors' contract (`k8s.casOk`, K2)
relies on (`keyOk`):
- the key is absent, and the flag `γ.seen` is `false` (owned by the invariant); or
- the key was written (`seenOk`: the flag discarded `true`, persistent) and holds `FormatInt c`
  for a revision `c` that is `0` or reached (`revOk`).

Every write of the workload keeps it: the writer's puts of another key (`writeKey`), and the
compactors' compare-and-swap rounds, which put `FormatInt rev` for a `rev` they hold `revOk` of.
Nothing deletes the key (`issues/k8s-apiserver-compactor-missing-key-panic.md`: the compactor
panics if something does).

For the compactors' watch loop (Q1 (b), 2026-11-04) the invariant also keeps the key's history
(`histOk`): every value the key held is `FormatInt c` for a `c` in a list `C` of revisions that are
`0` or reached (`KeyHist`, `KeyHist.lean`), each revision has at most one change (`OneChange`: no
revision writes a key twice, the watch server's `noDupKeys`), and the state is past revision `1`.

The compactors' `recorded` is `True` here: `Main`'s checks read the key's value and the
compactors' revisions only through `revOk` (reached), not through which revisions were recorded.
-/
module

public import Proof.k8s_io.apiserver.pkg.storage.etcd3.CompactorDefs
public import Perennial.Ghost.DGhostVar
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.compactor.KeyHist

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_compactor

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver k8s

/-- The example's invariant's namespace. -/
def cinvN : Namespace := nroot .@ "k8scompactor"

/-- The invariant is outside the client operations' atomic updates' mask. -/
theorem cinvN_mask : (↑cinvN : CoPset) ⊆ (⊤ \ ↑srvRaftN) \ ↑kvN := by
  intro p hp
  rw [Iris.Std.LawfulSet.mem_diff, Iris.Std.LawfulSet.mem_diff]
  exact ⟨⟨CoPset.mem_full, fun h => ndot_ne_disjoint nroot (by decide) p ⟨hp, h⟩⟩,
    fun h => ndot_ne_disjoint nroot (by decide) p ⟨hp, h⟩⟩

/-- The invariant's ghost names: the flag "the key was written", and a monotone counter of the
KV state's revision. -/
structure CNames where
  seen : GName
  rv : GName

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **The key was written** (persistent): the compactors' `Seen`. -/
def seenOk (γ : CNames) : IProp GF := dghostVar γ.seen .discard true

instance seenOk_persistent (γ : CNames) : Persistent (seenOk (GF := GF) γ) := by
  unfold seenOk; infer_instance

/-- **`compact_rev_key`'s protocol at the KV state `σ`** (see the file header). -/
def keyOk (γk : KVNames) (γ : CNames) (σ : KVState) : IProp GF :=
  iprop((⌜keyValue σ compactRevKey = none⌝ ∗ dghostVar γ.seen (.own 1) false) ∨
    (seenOk γ ∗ ∃ c : w64, ⌜keyValue σ compactRevKey = some (fmtInt c (W64 10))⌝ ∗ k8s.revOk γk c))

instance keyOk_timeless (γk : KVNames) (γ : CNames) (σ : KVState) :
    Timeless (keyOk (GF := GF) γk γ σ) := by
  unfold keyOk seenOk k8s.revOk; infer_instance

/-- **`compact_rev_key`'s history at the KV state `σ`** (see the file header). -/
def histOk (γk : KVNames) (σ : KVState) : IProp GF :=
  iprop(∃ C : List w64, ⌜KeyHist σ C ∧ OneChange σ ∧ 1 ≤ σ.rev⌝ ∗ [∗list] c ∈ C, k8s.revOk γk c)

instance histOk_timeless (γk : KVNames) (σ : KVState) : Timeless (histOk (GF := GF) γk σ) := by
  unfold histOk k8s.revOk; infer_instance

instance histOk_persistent (γk : KVNames) (σ : KVState) : Persistent (histOk (GF := GF) γk σ) := by
  unfold histOk k8s.revOk; infer_instance

/-- **The example's invariant** (persistent; see the file header): the clients' half of etcd's
KV state, the counter of its revision, `compact_rev_key`'s protocol and its history. -/
def cinv (γk : KVNames) (γ : CNames) : IProp GF :=
  inv cinvN iprop(∃ σ : KVState, etcdKV γk σ ∗ monoNatAuthOwn γ.rv 1 σ.rev ∗ keyOk γk γ σ ∗
    histOk γk σ)

instance cinv_persistent (γk : KVNames) (γ : CNames) : Persistent (cinv (GF := GF) γk γ) := by
  unfold cinv; infer_instance

end defs

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions]

open Iris.ProofMode in
/-- **A reached revision is a lower bound of the invariant's counter** (the read-side law,
`kv_revLbZ_le`, at the invariant's state): outside the client operations' atomic updates (with the
KV invariant's and this invariant's namespaces available), a revision `n` the cluster reached is at
most the KV state's revision, kept as a lower bound of `γ.rv` that read updates can use. -/
theorem cinv_revLb (γr : ServerRaftNames) (γk : KVNames) (γ : CNames) (E : CoPset)
    (hE : ↑kvN ⊆ E \ ↑cinvN) (hc : ↑cinvN ⊆ E) (n : Int) :
    ⊢ kvInv (GF := GF) γr γk -∗ cinv γk γ -∗ kvRevLbZ γk n ={E}=∗ monoNatLbOwn γ.rv n.toNat := by
  iintro #Hkv #Hinv #Hlb
  iunfold cinv at Hinv
  iinv Hinv with >Hi Hclose
  icases Hi with ⟨%σ, Hσ, Hrv, Hk, Hh⟩
  imod (kv_revLbZ_le γr γk (E \ ↑cinvN) hE n σ) $$ Hkv Hlb Hσ with ⟨Hσ, %Hle⟩
  ihave #Hlb' := monoNatLbOwn_get γ.rv 1 σ.rev $$ Hrv
  imod Hclose $$ [Hσ Hrv Hk Hh] with -
  · inext; iexists σ; iframe
  imodintro
  iapply monoNatLbOwn_le n.toNat (by omega) $$ Hlb'

open Iris.ProofMode in
/-- **The invariant at the member's start state** (`Main`'s: no key, no change, revision `1`). -/
theorem cinv_alloc (γk : KVNames) (E : CoPset) :
    etcdKV (GF := GF) γk (kvStateOf [[], []]) ⊢ |={E}=> ∃ γ : CNames, cinv γk γ := by
  iintro Hσ
  imod dghostVar_alloc (GF := GF) false with ⟨%γs, Hf⟩
  imod (mono_nat_own_alloc (GF := GF) (kvStateOf [[], []]).rev) with ⟨%γrv, Hrv, -⟩
  imod (inv_alloc cinvN E iprop(∃ σ' : KVState, etcdKV γk σ' ∗
      monoNatAuthOwn γrv 1 σ'.rev ∗ keyOk γk ⟨γs, γrv⟩ σ' ∗ histOk γk σ')) $$ [Hσ Hf Hrv] with #Hinv
  · inext; iexists (kvStateOf [[], []]); iframe Hσ Hrv
    isplitl [Hf]
    · iunfold keyOk; ileft; iframe Hf; ipureintro; exact keyValue_boot
    iunfold histOk; iexists []
    isplitr
    · ipureintro; exact ⟨KeyHist_boot, OneChange_boot, by rw [kvStateOf_boot_rev]; exact Nat.le_refl 1⟩
    iapply BigSepL.bigSepL_nil.2; itrivial
  imodintro
  iexists ⟨γs, γrv⟩
  iunfold cinv
  iexact Hinv

end laws

end k8s_compactor
end EtcdGrove
end Perennial
