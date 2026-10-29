/- Lean-first (no Rocq counterpart).

**`Collect` over a plan of puts** (watchkv's and linkv3p's use, 2026-10-29): `Collect.spec` at the
per-event fact "a put at revision `2 + i` of a key and value of the plan `P`, the put `R` has at
it", the caller's `Hresp` saying each event is one (`evFactR`), and the result `collectOk`. What
`Collect.spec` said before it was made general in the events (`notes/authkv-main-plan.md`, round
1, F-H3).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.common.Collect

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace common

open Iris Iris.BI Iris.ProofMode
open go_etcd_io.etcd.server.v3.etcdserver github_com.mit_pdos.etcd_grove.examples.common

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.common.Assumptions]

/-- The per-event fact of a plan of puts: a put at revision `2 + i` of a key and value of `P`,
the put `R` has at it. -/
def planEvF (R : Nat → GoString → GoString → IProp GF) (P : List (GoString × GoString))
    (i : Nat) (e : wev) : IProp GF :=
  iprop(⌜e.Put' = true ∧ sint.Z e.Rev' = 2 + i ∧ (e.Key', e.Val') ∈ P⌝ ∗ R (2 + i) e.Key' e.Val')

/-- **`Collect(wch, upTo)` over a plan of puts** (see the file header). -/
theorem wp_Collect_plan (wp_Collect : Collect.spec (GF := GF) (hG := hG))
    [go_etcd_io.etcd.cache.v3.Assumptions] (Ok : RespOk GF)
    (R : Nat → GoString → GoString → IProp GF) (A : IProp GF) (P : List (GoString × GoString))
    (wch : Loc) (γ : EtcdWatchNames) (upTo : w64)
    (hP : ∀ (c c' : w64) (v : go_etcd_io.etcd.client.v3.WatchResponse) (r : RespModel),
      Persistent (Ok c c' v r))
    (Hce : ∀ (c c' : w64) (v : go_etcd_io.etcd.client.v3.WatchResponse) (r : RespModel),
      Ok c c' v r ⊢ go_etcd_io.etcd.cache.v3.statusErrOk v.closeErr')
    (Hresp : ∀ (n : Nat) (c c' : w64) (v : go_etcd_io.etcd.client.v3.WatchResponse)
      (r : RespModel), ¬ watchErr v → Cur n c →
      ⊢ □ A -∗ Ok c c' v r ={⊤}=∗
        ⌜Cur (n + r.events.length) c'⌝ ∗
        □ ∀ (j : Nat) (e : EvModel), ⌜r.events[j]? = some e⌝ -∗ evFactR R P (2 + n + j) e) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.common ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗
        isRespChan wch γ Ok ∗ etcdWatchConsumer γ 0 (W64 0) ∗ □ A }}
      (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.common.Collect)) (Val #wch))
        (Val #upTo))
    {{ (sl : GoSlice) (ok : Bool), RET (PairV #sl #ok);
        ⌜ok = true⌝ -∗ ∃ evs : List wev, sl ↦* evs ∗ collectOk R P upTo evs }} := by
  iintro %Φ Hpre HΦ
  have Hresp' : ∀ (n : Nat) (c c' : w64) (v : go_etcd_io.etcd.client.v3.WatchResponse)
      (r : RespModel), ¬ watchErr v → Cur n c →
      ⊢ □ A -∗ Ok c c' v r ={⊤}=∗
        ⌜Cur (n + r.events.length) c'⌝ ∗
        □ ∀ (j : Nat) (e : EvModel), ⌜r.events[j]? = some e⌝ -∗
          ∃ kvv : EtcdKv, kvValAt e.kv kvv ∗ planEvF R P (n + j) (evWev e kvv.value) := by
    intro n c c' v r hnw hc
    iintro #HA Hok
    imod (Hresp n c c' v r hnw hc) $$ HA Hok with ⟨%Hcur, #Hev⟩
    imodintro
    isplitr
    · ipureintro; exact Hcur
    iintro !> %j %e %he
    ihave Hf := Hev $$ %j %e %he
    iunfold evFactR at Hf
    icases Hf with ⟨%Hfe, %v', %kvv, #Hkvv, %Hval, Hr⟩
    iexists kvv
    isplitr
    · iexact Hkvv
    iunfold planEvF
    simp only [evWev, Hfe.1, _root_.decide_true]
    isplitr
    · ipureintro
      refine ⟨trivial, ?_, ?_⟩
      · rw [Hfe.2]; omega
      · rw [Hval.1]; exact Hval.2
    rw [show 2 + (n + j) = 2 + n + j by omega, Hval.1]
    iexact Hr
  wp_apply (wp_Collect Ok (planEvF R P) A wch γ upTo hP Hce Hresp') $$ [$Hpre]
    as %sl %ok Hpost
  iapply HΦ
  iintro %hok
  ispecialize Hpost $$ %hok
  icases Hpost with ⟨%evs, Hs, %Hup, #Hall⟩
  iexists evs
  iframe
  iunfold collectOk
  ihave %Hf : ⌜∀ (i : Nat) (e : wev), evs[i]? = some e →
      e.Put' = true ∧ sint.Z e.Rev' = 2 + i ∧ (e.Key', e.Val') ∈ P⌝ $$ []
  · iapply BI.pure_forall.2
    iintro %i
    iapply BI.pure_forall.2
    iintro %e
    by_cases hi : evs[i]? = some e
    · ihave H := Hall $$ %i %e %hi
      iunfold planEvF at H
      icases H with ⟨%H, -⟩
      ipureintro; intro _; exact H
    · ipureintro; intro h; exact absurd h hi
  isplitr
  · ipureintro
    have hlen : ∀ hne : evs ≠ [], evs.length + 1 < 2 ^ 63 ∧
        sint.Z (evs.getLast hne).Rev' = 1 + evs.length := by
      intro hne
      have hl : evs[evs.length - 1]? = some (evs.getLast hne) := by
        rw [List.getLast_eq_getElem]; exact List.getElem?_eq_getElem _
      have h := (Hf _ _ hl).2.1
      have hpos : 0 < evs.length := List.length_pos_iff.mpr hne
      generalize evs.getLast hne = x at h ⊢
      have hx : sint.Z x.Rev' < 2 ^ 63 := by word
      constructor <;> omega
    refine ⟨?_, ?_, Hf⟩
    · rcases Hup with h | ⟨e, he, hle⟩
      · exact Or.inl h
      · right
        have hne : evs ≠ [] := by intro h; rw [h] at he; simp at he
        rw [List.getLast?_eq_some_getLast hne] at he
        cases he
        have := (hlen hne).2
        omega
    · by_cases hne : evs = []
      · rw [hne]; simp
      · exact (hlen hne).1
  iintro !> %i %e %he
  ihave H := Hall $$ %i %e %he
  iunfold planEvF at H
  icases H with ⟨-, H⟩
  iexact H

end proof

end common
end EtcdGrove
end Perennial
