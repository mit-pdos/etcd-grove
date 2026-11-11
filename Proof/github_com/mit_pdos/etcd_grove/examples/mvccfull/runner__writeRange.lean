/- Lean-first (no Rocq counterpart). The proof of `runner.writeRange` (Draft's glue, as mvccrand's
`writeOp`'s range arm): `view`; `tw.Range` (`Txn.Range.contract` through `shapes.law`, its
`rangeOutcomeC` at the transaction's read log); `checkRangeAt` at the view's states, which match
the read log (`pendOk`, `HistRevs`), the pending map given back.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.runner__writeRange
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.runner__view
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.checkRangeAt
public import Spec.context.TODO
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.TxnRange
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.BucketLemmas

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccfull

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.mvccfull mvcc mvcc.api

section model
variable [GooseExts]

private theorem pendOk_rev {ks : List GoString} {σ : MvccState} {Hs : List HRev}
    {pend : List Change} {P : PendM} (hok : pendOk ks σ Hs pend P) :
    P.rev = W64 (Hs.length : Int) := by
  rw [hok.1]; exact pendOf_rev _ _ _

/-- The revision a read in the transaction sees is `view`'s. -/
private theorem viewRev_writeRev (ks : List GoString) (σ : MvccState) (Hs : List HRev)
    (pend : List Change) (P : PendM) (hok : pendOk ks σ Hs pend P) (hlen : Hs.length = σ.log.length)
    (h1 : 1 ≤ σ.log.length) (h63 : σ.log.length < 2 ^ 63) :
    viewRev P = W64 (writeRev σ.log pend : Int) := by
  have hnil : P.chs = [] ↔ pend = [] := by rw [hok.1]; exact pendOf_chs_nil_iff _ _ _
  unfold viewRev writeRev
  rw [pendOk_rev hok, hlen]
  by_cases hp : pend = []
  · simp only [hnil.2 hp, hp, ↓reduceIte]
    have : ((σ.log.length - 1 : Nat) : Int) = (σ.log.length : Int) - 1 := by omega
    rw [this]; word
  · have hc : P.chs ≠ [] := fun h => hp (hnil.1 h)
    simp only [hc, hp, ↓reduceIte]

/-- The states a read in the transaction sees are the store's at its read log. -/
private theorem viewSt_match (ks : List GoString) (σ : MvccState) (Hs : List HRev)
    (pend : List Change) (P : PendM) (hok : pendOk ks σ Hs pend P) (hlen : Hs.length = σ.log.length)
    (h1 : 1 ≤ σ.log.length) (hrev : HistRevs ks σ.log Hs) :
    ∀ r : Nat, r ≤ writeRev σ.log pend →
      ∃ M, (viewSt Hs P)[r]? = some M ∧ stMatch ks M (stateAt (σ.log ++ [pend]) r) := by
  have hnil : P.chs = [] ↔ pend = [] := by rw [hok.1]; exact pendOf_chs_nil_iff _ _ _
  intro r hr
  by_cases hlt : r < Hs.length
  · obtain ⟨e, he, hok', -⟩ := hrev r (by omega)
    refine ⟨e.1, ?_, ?_⟩
    · unfold viewSt
      rw [List.getElem?_append_left (by simp; omega), List.getElem?_map, he]; rfl
    · rw [stateAt_append_lt _ _ (by omega)]; exact hok'
  · have hp : pend ≠ [] := by
      intro hp; rw [writeRev, ite_eq_left hp] at hr; rw [hlen] at hlt; omega
    have hc : P.chs ≠ [] := fun h => hp (hnil.1 h)
    have hr' : r = Hs.length := by rw [writeRev, ite_eq_right hp] at hr; omega
    subst hr'
    refine ⟨P.st, ?_, ?_⟩
    · unfold viewSt; simp [hc]
    · rw [hlen, stateAt_pend]; exact hok.2

private theorem viewSt_length (Hs : List HRev) (P : PendM) :
    (viewSt Hs P).length = Hs.length + (if P.chs = [] then 0 else 1) := by
  unfold viewSt; split <;> simp

end model

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccfull.Assumptions]
variable [mvcc_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

theorem runner.writeRange.wp_proof
    (hsh : mvcc.api.shapes.law (GF := GF) (hG := hG))
    (wp_view : runner.view.spec (GF := GF) (hG := hG))
    (wp_ctxTODO : context.TODO.spec (GF := GF) (hG := hG))
    (wp_checkRangeAt : checkRangeAt.spec (GF := GF) (hG := hG)) :
    runner.writeRange.spec (GF := GF) (hG := hG) := by
  intro x ks h γh mp γk tw trace te σ pend Hs p P q qm hok hlen hrev hreach hLok h63
  wp_start as ⟨Hks, Hh, Hrd, Hlb, Hcmp, Htx, Htrc, Hp, Hq⟩
  icases (persistent_entails_right (hsh.2.2.1 tw γk trace (.write σ pend))) $$ Htx with ⟨%Hsht, Htx⟩
  obtain ⟨tty, tv, rfl, -, -, hRangeC, -, -, -, -⟩ := Hsht
  obtain ⟨hl2, hc1, hcr⟩ := reach_bounds σ hreach
  have hPrev := pendOk_rev hok
  iunfold runnerKeys at Hks
  icases Hks with ⟨%keys, #Hkeys, #Hksl, %Hsorted, -⟩
  iunfold rangeIs at Hq
  icases Hq with ⟨#Hk, #He, %Hqe, %Hqro⟩
  wp_auto
  wp_apply wp_view x h γh Hs p P hPrev (by omega) (by omega) $$ [$Hh $Hrd $Hlb $Hp]
    as %sts %cur ⟨Hrd, %Hcur, %dsl, %ms, Hsts, HstAt, Hback⟩
  rw [viewRev_writeRev ks σ Hs pend P hok hlen (by omega) (by omega)] at Hcur
  subst Hcur
  have hwr : writeRev σ.log pend ≤ σ.log.length := by unfold writeRev; split <;> omega
  have hcurZ : sint.Z (W64 ((writeRev σ.log pend : Nat) : Int)) = writeRev σ.log pend := by
    have : writeRev σ.log pend < 2 ^ 63 := by omega
    word
  have hcurN : sint.nat (W64 ((writeRev σ.log pend : Nat) : Int)) = writeRev σ.log pend := by
    have : sint.nat (W64 ((writeRev σ.log pend : Nat) : Int)) =
        (sint.Z (W64 ((writeRev σ.log pend : Nat) : Int))).toNat := rfl
    omega
  (try wp_auto)
  wp_apply wp_ctxTODO
  (try wp_auto)
  ihave #Hctxr : mvcc.rangeCtx true todoCtxVal
      ({ Values := GMap.empty, Deadline := none, Done_gn := ⟨0, 0⟩, PDone := iprop(True) } :
        context.ContextDesc (IProp GF)) $$ []
  · simp only [mvcc.rangeCtx, ↓reduceIte]; ileft; iapply mvcc.doneNil_todo
  wp_apply (hRangeC γk trace te (.write σ pend) todoCtxVal _ true q.key' q.end' qm.key qm.e q.ro')
      $$ [$Hpkg2 $Htx $Htrc $Hctxr $Hk $He]
    as %rr %err ⟨%Hrn, Htx, Htrc, Hout, -, -⟩
  have hrr : (MTxn.write σ pend).readRev = W64 ((writeRev σ.log pend : Nat) : Int) := rfl
  have hrl : (MTxn.write σ pend).readLog = σ.log ++ [pend] := rfl
  have hcs : (MTxn.write σ pend).state.crev = σ.crev := rfl
  have hcmpZ : sint.Z (W64 σ.crev) = σ.crev := by
    have : σ.crev < 2 ^ 63 := by unfold MvccState.rev at hcr; omega
    word
  rw [hrr, hrl, hcs]
  generalize hc : W64 σ.crev = c
  have hcZ : sint.Z c = σ.crev := by rw [← hc]; exact hcmpZ
  rw [← hcZ]
  iunfold statesAt at HstAt
  icases HstAt with ⟨%Hml, HstAt⟩
  have hnil : P.chs = [] ↔ pend = [] := by rw [hok.1]; exact pendOf_chs_nil_iff _ _ _
  have hcurlt : writeRev σ.log pend < ms.length := by
    rw [Hml.1, viewSt_length, hlen]
    unfold writeRev
    by_cases hp : pend = []
    · simp only [hp, hnil.2 hp, ↓reduceIte]; omega
    · have hc : P.chs ≠ [] := fun h => hp (hnil.1 h)
      simp only [hp, hc, ↓reduceIte]; omega
  (try wp_auto)
  wp_apply (wp_checkRangeAt keys ks DFrac.discard sts dsl ms (viewSt Hs P) (viewDq Hs P)
      (W64 ((writeRev σ.log pend : Nat) : Int)) c q qm.key qm.e DFrac.discard
      DFrac.discard rr err (σ.log ++ [pend]) Hsorted hLok (by omega) (by rw [hcurN]; exact hcurlt)
      (fun r _ hr => viewSt_match ks σ Hs pend P hok hlen (by omega) hrev r (by rw [hcurN] at hr; exact hr)))
    $$ [$Hpkg2 $Hksl $Hsts HstAt $Hk $He $Hout] as ⟨-, Hsts, HstAt, -, -⟩
  · iunfold statesAt; iframe HstAt
    ipureintro; exact ⟨Hml, Hrn rfl⟩
  ihave Hp := Hback $$ HstAt
  (try wp_auto)
  iapply HΦ
  iframe
end proof

end mvccfull
end EtcdGrove
end Perennial
