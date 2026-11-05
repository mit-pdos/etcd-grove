/-
**The chain's KV updates from the server's builders** (strict M1, 2026-11-05): txn's update shapes
(`txn.beginAU`, `txn.commitAU`) from the builders' (`srvApi.auBegin`, `srvApi.auEnd`, `envAus`): a
begin update at the writer's state whose payload is the caller's `R` at that state is txn's begin
update of `R`; an end update's payload weakened by a wand. Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.Chain

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace apply

open Iris Iris.BI Iris.ProofMode
open mvcc.api (MvccState MvccName mvccN)

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.txn.Assumptions]

/-- **The builder's begin update at `σ₀` is txn's begin update** of any payload `R`, given at `σ₀`
(the update commits only at `σ₀`). -/
theorem beginAU_of_auBegin (γ : MvccName) (σ₀ : MvccState) (R : MvccState → IProp GF) :
    srvApi.auBegin γ σ₀ (R σ₀) ⊢ txn.beginAU γ R := by
  iintro Hau
  iunfold srvApi.auBegin at Hau
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
  · iintro Hx
    icases Hcl with ⟨-, Hco⟩
    isimp only [tforall_cons, tforall_nil, Std.Tele.app, ULift.down] at Hco
    imod Hco $$ Hx with ⟨%Heq, HR⟩
    subst Heq
    imodintro
    iexact HR

/-- **An end update's payload, weakened** (the inner update's commit). -/
theorem auEnd_wand (γ : MvccName) (σ₀ : MvccState) (pend : List mvcc.Change) (Y Y' : IProp GF) :
    srvApi.auEnd γ σ₀ pend Y ⊢ (Y -∗ Y') -∗ srvApi.auEnd γ σ₀ pend Y' := by
  iintro Hau Hw
  iunfold srvApi.auEnd at Hau
  iunfold srvApi.auEnd
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
    imod Hab $$ Hx with Hau
    imodintro
    iframe Hau Hw
  · iintro Hx
    icases Hcl with ⟨-, Hco⟩
    isimp only [tforall_cons, tforall_nil, Std.Tele.app, ULift.down] at Hco
    imod Hco $$ Hx with Hin
    imodintro
    iauintro
    ihave Hacc := aupd_aacc $$ Hin
    unfold atomic_acc
    imod Hacc with Hacc
    isimp only [texist_cons, texist_nil, Std.Tele.app, ULift.down] at Hacc
    icases Hacc with ⟨%y, Hy, Hcl⟩
    imodintro
    isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
    iexists y
    iframe Hy
    isplit
    · iintro Hy
      icases Hcl with ⟨Hab, -⟩
      imod Hab $$ Hy with Hin
      imodintro
      iframe Hin Hw
    · iintro Hy
      icases Hcl with ⟨-, Hco⟩
      isimp only [tforall_cons, tforall_nil, Std.Tele.app, ULift.down] at Hco
      imod Hco $$ Hy with HY
      imodintro
      iapply Hw $$ HY

/-- **A read update's payload, weakened** (at its commit). -/
theorem auRead_wand (γ : MvccName) (Q Q' : MvccState → IProp GF) :
    srvApi.auRead γ Q ⊢ (∀ σ, Q σ -∗ Q' σ) -∗ srvApi.auRead γ Q' := by
  iintro Hau Hw
  iunfold srvApi.auRead at Hau
  iunfold srvApi.auRead
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
    imod Hab $$ Hx with Hau
    imodintro
    iframe Hau Hw
  · iintro Hx
    icases Hcl with ⟨-, Hco⟩
    isimp only [tforall_cons, tforall_nil, Std.Tele.app, ULift.down] at Hco
    imod Hco $$ Hx with HQ
    imodintro
    iapply Hw $$ HQ

/-- **The builder's end update is txn's commit update.** -/
theorem commitAU_of_auEnd (γ : MvccName) (σ₀ : MvccState) (pend : List mvcc.Change) (Y : IProp GF) :
    srvApi.auEnd γ σ₀ pend Y ⊢ txn.commitAU γ σ₀ pend Y := by
  iintro H
  iunfold srvApi.auEnd at H
  unfold txn.commitAU
  iexact H

end lemmas

end apply
end EtcdGrove
end Perennial
