/-
The writer's loop (`runner.write`): the members' parts restated at a longer log. Lean-first (no
Rocq counterpart).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccfull.WriterLemmas

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccfull

open Iris Iris.BI Iris.ProofMode github_com.mit_pdos.etcd_grove.examples.mvccfull mvcc mvcc.api

section model
variable [GooseExts]

theorem runM_snoc (ks : List GoString) (ops : List OpM) (o : OpM) (n : Nat) (hn : n ≤ ops.length) :
    runM ks (ops ++ [o]) n = runM ks ops n :=
  runM_prefix ks ops (ops ++ [o]) n (List.prefix_append _ _) hn

/-- **The log extended by an operation valid at its end is valid.** -/
theorem logOk_snoc (ks : List GoString) (ops : List OpM) (o : OpM) (h : logOk ks ops)
    (ho : opValid ks (runM ks ops ops.length) o) : logOk ks (ops ++ [o]) := by
  intro i o' hi
  by_cases hlt : i < ops.length
  · rw [List.getElem?_append_left hlt] at hi
    rw [runM_snoc ks ops o i (by omega)]
    exact h i o' hi
  · have hi' : i = ops.length := by
      have := (List.getElem?_eq_some_iff.1 hi).1
      simp at this; omega
    subst hi'
    rw [List.getElem?_append_right (by omega)] at hi
    simp at hi
    subst hi
    rw [runM_snoc ks ops o ops.length (by omega)]
    exact ho

end model

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccfull.Assumptions]
variable [mvcc_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **A member's part at a longer log** (its count within the shorter one). -/
theorem memCore_snoc (ks : List GoString) (γh : HistNames) (ops : List OpM) (o : OpM) (i : Nat)
    (mp : Loc) (m : MemberNames) (f : GoFunc) (v : MemS) (qw : Qp) (nw k : Nat)
    (hn : v.ops ≤ ops.length) :
    memCore (GF := GF) ks γh ops i mp m f v qw nw k ⊢ memCore ks γh (ops ++ [o]) i mp m f v qw nw k := by
  have h := runM_snoc ks ops o v.ops hn
  have hl : v.ops ≤ (ops ++ [o]).length := by simp; omega
  unfold memCore σOf histAt cmpAfter revAfter leasesAfter grantedAfter
  simp only [h, eq_true hn, eq_true hl]
  exact .rfl

theorem memW_snoc (ks : List GoString) (γh : HistNames) (ops : List OpM) (o : OpM) (i : Nat)
    (mp : Loc) (m : MemberNames) (f : GoFunc) (v : MemS) (qw : Qp) (nw k : Nat)
    (hn : v.ops ≤ ops.length) :
    memW (GF := GF) ks γh ops i mp m f v qw nw k ⊢ memW ks γh (ops ++ [o]) i mp m f v qw nw k := by
  unfold memW
  iintro ⟨Ho, Hh, Hc⟩
  iframe
  iapply memCore_snoc ks γh ops o i mp m f v qw nw k hn
  iexact Hc

end lemmas

end mvccfull
end EtcdGrove
end Perennial
