/-
The readers' read lemmas (`readOne`, `checkStoreRange`; as mvccrand's `reader.lean`): the
history's snapshot as `checkRangeAt` takes it, `checkRangeAt`'s premises at a read, the result's
struct of a live read (`outcome_acc`), a read transaction's shape and `End`. Lean-first.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccfull.Readers
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.checkRangeAt
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.TxnRange
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvStore
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.EtcdBackend
public import Spec.context.TODO

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccfull

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.mvccfull mvcc mvcc.api

/-! ## The pure part -/

section model
variable [GooseExts]

/-- **A read state's log is well formed** (`checkRangeAt`'s `LogOk`), from the range contract's
facts and the log's bound. -/
theorem logOk_read (σ : MvccState) (hb : σ.log.length + 3 ≤ 2 ^ 63) (hr : MvccReachable σ)
    (hwf : LogWf' σ.log ∧ ∀ cs ∈ σ.log, cs.length < 2 ^ 63) : txn.LogOk σ.log := by
  have := (reach_bounds σ hr).1
  have hne : σ.log ≠ [] := by intro h0; rw [h0] at this; simp at this
  exact txn.LogOk.of_cert ⟨hwf.1, by omega, hwf.2⟩ hne

/-- **`checkRangeAt`'s premises at a read** of the state `σ` (`readQ`'s facts, `Hl` its history's
lower bound), with the snapshot `Hs` (its maps `ms`) taken after: the revision read not negative,
in the snapshot, every revision up to it the log's state (from any floor `c`). -/
theorem check_ok (ks : List GoString) (σ : MvccState) (Hl Hs : List HRev) (ms : List GoMap)
    (hh : histOkM ks σ Hl) (hr : MvccReachable σ) (hb : σ.log.length + 3 ≤ 2 ^ 63)
    (hpre : Hl <+: Hs) (hms : ms.length = Hs.length) (c : Int) :
    0 ≤ sint.Z (W64 (σ.rev : Int)) ∧ sint.nat (W64 (σ.rev : Int)) < ms.length ∧
      ∀ r : Nat, c ≤ (r : Int) → r ≤ sint.nat (W64 (σ.rev : Int)) →
        ∃ M, (Hs.map Prod.fst)[r]? = some M ∧ stMatch ks M (stateAt σ.log r) := by
  have hle : σ.log.length ≤ σ.notifiedLog.length := by
    unfold MvccState.notifiedLog; split <;> simp
  have h2 := (reach_bounds σ hr).1
  have hr' : σ.rev < σ.log.length := by unfold MvccState.rev; omega
  have hz : sint.nat (W64 (σ.rev : Int)) = σ.rev := by
    have : sint.nat (W64 (σ.rev : Int)) = (sint.Z (W64 (σ.rev : Int))).toNat := rfl
    rw [this]
    have : sint.Z (W64 (σ.rev : Int)) = σ.rev := by word
    omega
  have hlen := hpre.length_le
  have h1 := hh.1
  refine ⟨by word, by omega, fun r _ hr2 => hist_match ks σ Hl Hs hh hpre r (by omega)⟩

/-- The revision of a reachable state with the log's bound, as a word, is itself. -/
theorem rev_w64 (σ : MvccState) (hb : σ.log.length + 3 ≤ 2 ^ 63) :
    sint.Z (W64 (σ.rev : Int)) = σ.rev := by
  have : σ.rev ≤ σ.log.length := by unfold MvccState.rev; omega
  word

end model

/-! ## The snapshot's maps -/

section own
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccfull.Assumptions]

theorem statesP_aux : ∀ (ms : List GoMap) (Hs : List HRev), ms.length = Hs.length →
    (([∗list] x ∈ ms.zip Hs, x.1 ↦$□ x.2.1) : IProp GF) ⊢
      [∗list] x ∈ ms.zip ((Hs.map Prod.fst).zip (List.replicate Hs.length DFrac.discard)),
        x.1 ↦${x.2.2} x.2.1
  | [], _, _ => by simp only [List.zip_nil_left]; exact .rfl
  | _ :: _, [], h => by simp at h
  | m :: ms, e :: Hs, h => by
    simp only [List.zip_cons_cons, List.map_cons, List.length_cons, List.replicate_succ]
    exact sep_mono .rfl (statesP_aux ms Hs (by simpa using h))

/-- The states' persistent maps, as `checkRangeAt` takes them (each at `DFrac.discard`). -/
theorem statesP_statesAt (ms : List GoMap) (Hs : List HRev) :
    statesP (GF := GF) ms Hs ⊢
      statesAt ms (Hs.map Prod.fst) (List.replicate Hs.length DFrac.discard) := by
  iintro H
  iunfold statesP at H
  icases H with ⟨%Hl, H⟩
  iunfold statesAt
  isplitr
  · ipureintro; simp [Hl]
  iapply statesP_aux ms Hs Hl $$ H

end own

/-! ## A read's result and transaction -/

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccfull.Assumptions]
variable [mvcc_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- **A live read's result** (`res` not null): its struct, of revision `rev`, given back to
the outcome; the error nil or `ErrFutureRev`'s. -/
theorem outcome_acc (r : Loc) (err : GoInterface) (L : Log) (rev : w64) (endNil : Bool)
    (k e : GoString) (ro : go_etcd_io.etcd.server.v3.storage.mvcc.RangeOptions) (hr : r ≠ null) :
    rangeOutcome (GF := GF) r err L rev endNil k e ro ⊢
      ∃ v : go_etcd_io.etcd.server.v3.storage.mvcc.RangeResult, r ↦ v ∗ ⌜v.Rev' = rev⌝ ∗
        (r ↦ v -∗ rangeOutcome r err L rev endNil k e ro) ∗
        (⌜err = GoInterface.nil⌝ ∨
          ∃ ef : GoInterfaceOk, globalAddr go_etcd_io.etcd.server.v3.storage.mvcc.ErrFutureRev ↦□ GoInterface.ok ef ∗
            ⌜err = GoInterface.ok ef⌝) := by
  iintro H
  iunfold rangeOutcome at H
  icases H with (⟨%H1, #Hef, Hr⟩ | ⟨%H1, %H2, %Hnull, -⟩ | ⟨%H1, %Herr, Hr⟩)
  · iexists _
    iframe Hr
    isplitr
    · ipureintro; rfl
    isplitl []
    · iintro Hr
      iunfold rangeOutcome
      ileft
      iframe Hr Hef
      ipureintro; exact H1
    iright; iexact Hef
  · exact absurd Hnull hr
  · cases hco : ro.CountOnly'
    · simp only [Bool.false_eq_true, ↓reduceIte]
      icases Hr with ⟨%kvs, Hr, Hkvs⟩
      iexists _
      iframe Hr
      isplitr
      · ipureintro; rfl
      isplitl [Hkvs]
      · iintro Hr
        iunfold rangeOutcome
        iright; iright
        isplitr
        · ipureintro; exact H1
        isplitr
        · ipureintro; exact Herr
        simp only [hco, Bool.false_eq_true, ↓reduceIte]
        iexists kvs
        iframe
      ileft; ipureintro; exact Herr
    · simp only [↓reduceIte]
      iexists _
      iframe Hr
      isplitr
      · ipureintro; rfl
      isplitl []
      · iintro Hr
        iunfold rangeOutcome
        iright; iright
        isplitr
        · ipureintro; exact H1
        isplitr
        · ipureintro; exact Herr
        simp only [hco, ↓reduceIte]
        iexact Hr
      ileft; ipureintro; exact Herr

/-- **A transaction is an interface value whose type meets `TxnWrite`'s contracts**
(`shapes.law`), the transaction kept. -/
theorem mvccTxn_shape (hsh : mvcc.api.shapes.law (GF := GF) (hG := hG))
    (t : GoInterface) (γ : MvccName) (trace : Loc) (k : MTxn) :
    mvccTxn (GF := GF) t γ trace k ⊢
      ⌜∃ ty v, t = interface.mkOk ty v ∧ isTxn (GF := GF) ty v⌝ ∗ mvccTxn t γ trace k :=
  persistent_entails_right (hsh.2.2.1 t γ trace k)

/-- A context descriptor for `context.TODO()`'s context, which `rangeCtx true` ignores. -/
def todoCd : context.ContextDesc (IProp GF) :=
  { Values := GMap.empty, Deadline := none, Done_gn := ⟨0, 0⟩, PDone := iprop(True) }

/-- **A read transaction's `End`**: the store's reader token back (`Txn.End.contract` at a read
transaction, whose backend arguments do not matter). -/
theorem end_read {ty : go.GoType} {v : val}
    (hEnd : mvcc.api.Txn.End.contract (GF := GF) (hG := hG) ty v)
    (γ : MvccName) (trace : Loc) (σ : MvccState) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
        mvccTxn (interface.mkOk ty v) γ trace (.read σ) }}
      (App (Val #(methods ty go!"End" v)) (Val #()))
    {{ RET #(); mvccReaders γ 1 }} := by
  have hB : Nonempty MvccStorage := by
    refine ⟨etcdStorage ⟨?_, ∅, 0, W64 0, null, ?_, false⟩⟩
    · constructor <;> first | exact default | (constructor <;> exact default)
    · exact default
  obtain ⟨B⟩ := hB
  iintro %Φ ⟨#Hpkg, Htx⟩ HΦ
  iapply (hEnd γ trace (.read σ) 1 B iprop(True) iprop(True)) $$ [Htx]
  · iframe Hpkg Htx
  inext
  iintro ⟨Hrdr, -⟩
  iapply HΦ; iframe

end proof

end mvccfull
end EtcdGrove
end Perennial
