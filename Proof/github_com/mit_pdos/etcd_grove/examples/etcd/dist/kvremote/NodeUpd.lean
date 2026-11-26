/-
# The kv client machine's update (`notes/etcd-dist-plan.md` §11.3, step 3)

`kvremote.Node`'s operation `op(sys, in)` is `txnlin.Call(sys.(*Client), in)`: a slot's update for the
wire input `x` (`slotUpd (kvR γk) x Φ`, remote's) is turned into the update `Call` takes
(`callUpd γk (kvMi x) Q`, txnlin's), and `Call`'s result back into `Φ` of a store output:

- **a write** (`lin_kvOpAu1`): remote's atomic update `lin` (`kvSys γk st` to its step) becomes the
  client's `kvOpAu1 γk (opIn i)` (the half `etcdKV γk σ` that `kvSys` holds, to the server's step),
  with `Q := nodeQ x Φ`: at the commit the next state is good (`goodKV_step`), abstracts to the
  model's step (`absSt_step`) and keeps `kvGood` (its values' bound by `kvOut_good`, its revision
  from the server's room `kvRoom`, `kvOpStep_cases`); `lin` aborts when the AU does.
- **a read** (`lin_kvReadAu`): remote's persistent `□ lin` becomes the client's persistent
  `kvReadAu γk`, whose result must be persistent: each firing fires a copy of `lin` and puts its
  `Φ` in an invariant `nodeInv γt …` that the caller's token `γt` opens once (`nodeRQ`).
- **the result** (`nodeQ_out`, `nodeRQ_out`): `Call`'s output `y` at a good state `σ` is `outAt i σ`,
  which is `call`'s output of the model's answer (`kvOut_good`), so `Φ` of that `VOut`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote.Store
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.txnlin.Calls
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.txnlin.Inv

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.etcd.txnlin
open EtcdGrove EtcdGrove.etcd_txnlin
open go_etcd_io.etcd.server.v3.etcdserver mvcc
open github_com.mit_pdos.etcd_grove.examples.lib.remote Net

/-! ## Pure facts of a step -/

section pure
variable [GooseExts]

/-- A wire input's keys are the workload's. -/
theorem kvMi_keys (x : VIn) : (kvMi x).KeysIn wks := by
  obtain ⟨i, h, hk⟩ := x.2.1
  rw [kvMi_dec x] at h
  cases h
  exact inKeys_keysIn _ hk

/-- **The server's step keeps the far side's state**: from a good `σ` that abstracts to a `kvGood`
state, with the server's room, the step of `x` is good, abstracts to the model's step, and is
`kvGood`. -/
theorem kvSys_step (x : VIn) (σ : KVState) (hg : GoodKV σ) (hk : kvGood (linkv.absSt σ))
    (hroom : kvRoom σ) :
    GoodKV (kvOpStep (opIn (kvMi x)) σ) ∧
      linkv.absSt (kvOpStep (opIn (kvMi x)) σ) = (TSo.step (kvMi x) (linkv.absSt σ)).1 ∧
      kvGood (TSo.step (kvMi x) (linkv.absSt σ)).1 := by
  have habs := absSt_step σ hg (kvMi x)
  refine ⟨goodKV_step σ hg _ (kvMi_keys x), habs, ?_, (kvOut_good x _ hk).2⟩
  show (linkv.mStep wks (kvMi x) (linkv.absSt σ)).1.rev < 2 ^ 63
  rw [← habs]
  show (kvOpStep (opIn (kvMi x)) σ).rev < 2 ^ 63
  unfold kvRoom at hroom
  rcases kvOpStep_cases (opIn (kvMi x)) σ (linkv.opOf_isKV _ _ _) with h | h
  · rw [h]; omega
  · rw [h]; omega

/-- **The answer `Call` gives at a good state is the store's output** there. -/
theorem kvOut_outAt (x : VIn) (σ : KVState) (hk : kvGood (linkv.absSt σ)) :
    (TSo.step (kvMi x) (linkv.absSt σ)).2.1 = outAt (kvMi x) σ :=
  (kvOut_good x _ hk).1

end pure

/-! ## The updates -/

section upd
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- The namespace of a read's result invariants. -/
def nodeN : Namespace := (nroot.@"kvremote").@"node"

/-- **A write's result** (see the file header): `Φ` of the store's output at `σ`, which is good. -/
def nodeQ (x : VIn) (Φ : VOut → IProp GF) (σ : KVState) : IProp GF :=
  iprop(Φ (TSo.step (kvMi x) (linkv.absSt σ)).2 ∗ ⌜GoodKV σ ∧ kvGood (linkv.absSt σ)⌝)

/-- **A read's result** (see the file header), persistent: `Φ` of the store's output at `σ` in an
invariant, until the token `γt` takes it. -/
def nodeRQ (γt : GName) (x : VIn) (Φ : VOut → IProp GF) (σ : KVState) : IProp GF :=
  iprop(inv nodeN iprop(Φ (TSo.step (kvMi x) (linkv.absSt σ)).2 ∨ token γt) ∗
    ⌜GoodKV σ ∧ kvGood (linkv.absSt σ)⌝)

instance nodeRQ_persistent (γt : GName) (x : VIn) (Φ : VOut → IProp GF) (σ : KVState) :
    Persistent (nodeRQ γt x Φ σ) := by
  unfold nodeRQ; infer_instance

/-- **A write's update** (see the file header). -/
theorem lin_kvOpAu1 (γk : KVNames) (x : VIn) (Φ : VOut → IProp GF) :
    lin (Gg := hG.goose_globalGS) (kvR γk) x Φ ⊢ kvOpAu1 γk (opIn (kvMi x)) (nodeQ x Φ) := by
  unfold lin kvOpAu1 kvAu1
  simp only [kvR]
  rw [kvEop_mask]
  iintro HL
  iauintro
  unfold atomic_acc
  ihave HL := aupd_aacc $$ HL
  unfold atomic_acc
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down] at HL
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
  imod HL with ⟨%st, Hs, HL⟩
  iunfold kvSys at Hs
  icases Hs with ⟨%σ, Hσ, %hσ⟩
  obtain ⟨hg, hst, hk⟩ := hσ
  subst hst
  imodintro
  iexists σ
  iframe Hσ
  isplit
  · -- abort: `lin` aborts
    iintro Hσ
    icases HL with ⟨HL, -⟩
    iapply HL
    iunfold kvSys
    iexists σ
    iframe Hσ
    ipureintro; exact ⟨hg, rfl, hk⟩
  · -- commit: `lin` commits at the server's step
    iintro ⟨Hσ, %hroom⟩
    icases HL with ⟨-, HL⟩
    obtain ⟨hg', habs, hk'⟩ := kvSys_step x σ hg hk hroom
    imod HL $$ [Hσ] with HΦ
    · iunfold kvSys
      iexists _
      iframe Hσ
      ipureintro; exact ⟨hg', habs, hk'⟩
    imodintro
    iunfold nodeQ
    iframe HΦ
    ipureintro; exact ⟨hg, hk⟩

/-- **A read's update** (see the file header). -/
theorem lin_kvReadAu (γk : KVNames) (γt : GName) (x : VIn) (Φ : VOut → IProp GF)
    (hw : (kvMi x).isWrite = false) :
    □ lin (Gg := hG.goose_globalGS) (kvR γk) x Φ ⊢ kvReadAu γk (nodeRQ γt x Φ) := by
  unfold lin kvReadAu kvAu
  simp only [kvR]
  rw [kvEop_mask]
  iintro #HL
  imodintro
  iauintro
  unfold atomic_acc
  ihave HL' := aupd_aacc $$ HL
  unfold atomic_acc
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down] at HL'
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
  imod HL' with ⟨%st, Hs, HL'⟩
  iunfold kvSys at Hs
  icases Hs with ⟨%σ, Hσ, %hσ⟩
  obtain ⟨hg, hst, hk⟩ := hσ
  subst hst
  have hstay : (TSo.step (kvMi x) (linkv.absSt σ)).1 = linkv.absSt σ :=
    linkv.mStep_read wks (kvMi x) (linkv.absSt σ) hw
  imodintro
  iexists σ
  iframe Hσ
  isplit
  · -- abort: this copy of `lin` aborts
    iintro Hσ
    icases HL' with ⟨HL', -⟩
    imod HL' $$ [Hσ] with -
    · iunfold kvSys
      iexists σ
      iframe Hσ
      ipureintro; exact ⟨hg, rfl, hk⟩
    imodintro
    itrivial
  · -- commit: this copy commits at the same state; its result goes to an invariant
    iintro ⟨Hσ, %hroom⟩
    icases HL' with ⟨-, HL'⟩
    imod HL' $$ [Hσ] with HΦ
    · iunfold kvSys
      iexists σ
      iframe Hσ
      ipureintro; exact ⟨hg, hstay.symm, by rw [hstay]; exact hk⟩
    imod inv_alloc nodeN _ (iprop(Φ (TSo.step (kvMi x) (linkv.absSt σ)).2 ∨ token γt)) $$ [HΦ]
      with #Hi
    · iintro !>
      ileft
      iexact HΦ
    imodintro
    imodintro
    iunfold nodeRQ
    iframe Hi
    ipureintro; exact ⟨hg, hk⟩

/-- **A slot's update is the update `Call` takes**, at the result `nodeQ` (a write) or `nodeRQ γt`
(a read). -/
theorem slotUpd_callUpd (γk : KVNames) (γt : GName) (x : VIn) (Φ : VOut → IProp GF) :
    slotUpd (Gg := hG.goose_globalGS) (kvR γk) x Φ ⊢
      callUpd γk (kvMi x) (if (kvMi x).isWrite then nodeQ x Φ else nodeRQ γt x Φ) := by
  cases hw : (kvMi x).isWrite
  · have hw' : (kvR (GF := GF) γk).B.isWrite ((kvR (GF := GF) γk).mi x) = false := hw
    rw [slotUpd_read _ hw']
    unfold callUpd
    simp only [hw, Bool.false_eq_true, ↓reduceIte]
    iintro #HL
    iright
    iapply lin_kvReadAu γk γt x Φ hw
    iexact HL
  · have hw' : (kvR (GF := GF) γk).B.isWrite ((kvR (GF := GF) γk).mi x) = true := hw
    rw [slotUpd_write _ hw']
    unfold callUpd
    simp only [hw, ↓reduceIte]
    exact lin_kvOpAu1 γk x Φ

/-- **A write's result is `Φ` of a store output** that is `Call`'s answer `y`. -/
theorem nodeQ_out (x : VIn) (Φ : VOut → IProp GF) (σ : KVState) (y : Output)
    (hy : GoodKV σ → y = outAt (kvMi x) σ) :
    nodeQ x Φ σ ⊢ ∃ o : VOut, ⌜y = o.1⌝ ∗ Φ o := by
  unfold nodeQ
  iintro ⟨HΦ, %h⟩
  iexists _
  iframe HΦ
  ipureintro
  rw [hy h.1, kvOut_outAt x σ h.2]

/-- **A read's result, with its token, is `Φ` of a store output** that is `Call`'s answer `y`
(after a later: the invariant's). -/
theorem nodeRQ_out (γt : GName) (x : VIn) (Φ : VOut → IProp GF) (σ : KVState) (y : Output)
    (hy : GoodKV σ → y = outAt (kvMi x) σ) (E : CoPset) (hE : (↑nodeN : CoPset) ⊆ E) :
    nodeRQ γt x Φ σ -∗ token γt ={E}=∗ ▷ ∃ o : VOut, ⌜y = o.1⌝ ∗ Φ o := by
  unfold nodeRQ
  iintro ⟨#Hi, %h⟩ Ht
  iinv Hi with Hc Hclose
  icases Hc with (HΦ | >Ht')
  · imod Hclose $$ [Ht] with -
    · inext
      iright
      iexact Ht
    imodintro
    inext
    iexists _
    iframe HΦ
    ipureintro
    rw [hy h.1, kvOut_outAt x σ h.2]
  · iexfalso
    iapply token_exclusive γt $$ Ht Ht'

end upd

end github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote
end Perennial
