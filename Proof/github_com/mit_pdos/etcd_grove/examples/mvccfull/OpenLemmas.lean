/-
mvccfull's `open` (F1 Prove): its lemmas. Lean-first (no Rocq counterpart).

Before the new incarnation's invariant is allocated the writer holds the store's whole state
(`mvccState`), so its reads' updates are trivial (`own_au`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccfull.Writer

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccfull

open Iris Iris.BI Iris.ProofMode github_com.mit_pdos.etcd_grove.examples.mvccfull mvcc mvcc.api

section model
variable [GooseExts]

/-- A member that applied no operation is at the fresh store's state. -/
theorem σOf_zero (ks : List GoString) (ops : List OpM) : σOf ks ops 0 = mvccStart := by
  simp only [σOf, histAt, cmpAfter, runM_zero]; rfl

end model

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [mvcc_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- **A read's update of a store whose state the caller holds**: the state back, unchanged. -/
theorem own_au (γ : MvccName) (σf : MvccState) :
    mvccState (GF := GF) γ σf ⊢
      AU <{ ∃∃ (σ : MvccState), mvccState γ σ }> @ ⊤ \ ↑mvccN, ∅
        <{ mvccState γ σ, COMM (fun (σ : MvccState) => iprop(⌜σ = σf⌝ ∗ mvccState γ σf)) σ }> := by
  iintro Hσ
  iauintro
  unfold atomic_acc
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ ⊤ \ ↑mvccN from Std.LawfulSet.empty_subset)
  iintro Hclose
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
  iexists σf
  iframe Hσ
  isplit
  · iintro Hσ; imod Hclose with -; imodintro; iexact Hσ
  · iintro Hσ; imod Hclose with -; imodintro; iframe; ipureintro; rfl

/-- A reader slot of the lessor of `γl`, at its pin (mvccrand's `lessorRd_of`, without mvccrand's
package assumptions). -/
theorem lessorRd_of' (lp : Loc) (γl : GName) :
    lease.lessorInv (GF := GF) lp γl ∗ lease.lessorRdOf γl ⊢ lease.lessorRd lp γl := by
  iintro ⟨#Hinv, Hrd⟩
  iunfold lease.lessorRdOf at Hrd
  icases Hrd with ⟨%lp', #Hpin, Hrd⟩
  iunfold lease.lessorInv at Hinv
  icases Hinv with ⟨-, #Hpin0, -⟩
  ihave %Heq := lease.lessorPin_agree γl lp lp' $$ [Hpin0 Hpin]
  · iframe Hpin0 Hpin
  subst Heq
  iexact Hrd

/-- A zero `atomic.Int64` is owned at `0`. -/
theorem ownInt64_of_zero (l : Loc) :
    (l ↦ (zeroValDef : sync.atomic.Int64) : IProp GF) ⊢ sync.atomic.ownInt64 l (DFrac.own 1) (W64 0) := by
  rw [sync.atomic.ownInt64_unseal]
  unfold sync.atomic.ownInt64Def
  rw [show ({ «_#0'» := zero_val _, «_#1'» := zero_val _, v' := W64 0 } : sync.atomic.Int64) =
    zeroValDef from rfl]

variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccfull.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **A member that applied no operation is the same of every log** (`runM_zero`). -/
theorem memCore_ops0 (ks : List GoString) (γh : HistNames) (ops ops' : List OpM) (i : Nat) (mp : Loc)
    (m : MemberNames) (f : GoFunc) (v : MemS) (qw : Qp) (nw k : Nat) (h0 : v.ops = 0) :
    memCore (GF := GF) ks γh ops i mp m f v qw nw k = memCore ks γh ops' i mp m f v qw nw k := by
  unfold memCore
  simp only [h0, σOf, revAfter, cmpAfter, leasesAfter, grantedAfter, histAt, runM_zero, Nat.zero_le]

end lemmas

end mvccfull
end EtcdGrove
end Perennial
