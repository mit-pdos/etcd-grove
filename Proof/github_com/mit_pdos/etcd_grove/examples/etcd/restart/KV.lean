/-
**restart3's KV ghost state** (restart3 C2, 2026-11-15): restart1's (`restart1/KV.lean`) at the
cluster's KV names and `N1 + N2 = 25` puts. Lean-first (no Rocq counterpart).

restart1's pure lemmas (`keyOf`, `valOf`, `r1Pairs`, `r1Ok`, `r1Ok_put`, `srvRangeOk_r1`) do not
depend on the number of puts; this file restates what does: the invariant (`r3Inv`, the counter
capped at `r3NPuts`), the put's update (`r3PutAu`), the read's (`r3ReadAu`) and the range by index
(`r3Ok_get`). The invariant reads only the KV state's ghost variable, which `restartNames` keeps
(`r3Inv_st`): it is the restarted member's too, and the cluster's (every member's `ρ.rd.kv` is the
cluster's KV names).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.restart1.KV

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_restart

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3
open etcd_restart1 (keyOf valOf inR1 r1Pairs r1Ok r1PutOp r1Ok_put r1RangeOp srvRangeOk_r1 monoNat_halves)

section pure

/-- `restart3`'s `N1`, `N2` and their sum. -/
abbrev r3N1 : Nat := 5
abbrev r3N2 : Nat := 20
abbrev r3NPuts : Nat := 25

/-- The range's key-values, by index: the `i`-th is `keyOf i ↦ valOf i`. -/
theorem r3Ok_get (σ : KVState) (h : r1Ok σ r3NPuts) :
    (σ.kvs.filter inR1).length = r3NPuts ∧
      ∀ i (hi : i < r3NPuts) v, (σ.kvs.filter inR1)[i]? = some v →
        v.key = keyOf i ∧ v.value = valOf i ∧ v.version = W64 1 := by
  have hl := congrArg List.length h.1
  simp only [List.length_map, r1Pairs, List.length_range] at hl
  refine ⟨hl, fun i hi v hv => ?_⟩
  have h2 := congrArg (fun l => l[i]?) h.1
  simp only [List.getElem?_map, hv, r1Pairs, List.getElem?_range hi, Option.map_some] at h2
  have h3 := Option.some.inj h2
  simp only [Prod.mk.injEq] at h3
  exact h3

end pure

section inv
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- The namespace of `restart3`'s KV invariant. -/
def r3N : Namespace := nroot .@ "restart3_kv"

theorem r3N_mask : (↑r3N : CoPset) ⊆ (⊤ \ ↑srvRaftN) \ ↑kvN := by
  intro p hp
  rw [Iris.Std.LawfulSet.mem_diff, Iris.Std.LawfulSet.mem_diff]
  exact ⟨⟨CoPset.mem_full, fun h => ndot_ne_disjoint nroot (by decide) p ⟨hp, h⟩⟩,
    fun h => ndot_ne_disjoint nroot (by decide) p ⟨hp, h⟩⟩

/-- **`restart3`'s KV invariant** (restart1's `r1Inv` at `r3NPuts`), at the KV names `γk` and the
counter `γc`. -/
def r3Inv (γk : KVNames) (γc : GName) : IProp GF :=
  inv r3N iprop(∃ (σ : KVState) (c : Nat), etcdKV γk σ ∗ monoNatAuthOwn γc (1 : Qp).half c ∗
    ⌜c ≤ r3NPuts ∧ r1Ok σ c⌝)

instance r3Inv_persistent (γk : KVNames) (γc : GName) : Persistent (r3Inv (GF := GF) γk γc) := by
  unfold r3Inv; infer_instance

/-- **The invariant reads only the KV state's ghost variable**: at KV names sharing it, the same. -/
theorem r3Inv_st (γk γk' : KVNames) (h : γk.st = γk'.st) (γc : GName) :
    r3Inv (GF := GF) γk γc = r3Inv γk' γc := by
  unfold r3Inv
  simp only [etcdKV_congr γk γk' h]

/-- **The invariant allocated** at a state with no key in the range and revision `1` (the
bootstrap log's: its entries are conf changes), the driver's half of the counter at `0`. -/
theorem r3Inv_alloc (γk : KVNames) (σ : KVState) (hσ : σ.kvs.filter inR1 = [])
    (hrev : σ.rev = 1) (E : CoPset) :
    etcdKV (GF := GF) γk σ ⊢ |={E}=> ∃ γc, r3Inv γk γc ∗ monoNatAuthOwn γc (1 : Qp).half 0 := by
  iintro Hσ
  imod (mono_nat_own_alloc (GF := GF) 0) with ⟨%γc, Hc, -⟩
  icases (monoNat_halves γc 0).1 $$ Hc with ⟨Hc1, Hc2⟩
  imod inv_alloc r3N E iprop(∃ (σ : KVState) (c : Nat), etcdKV γk σ ∗
      monoNatAuthOwn γc (1 : Qp).half c ∗ ⌜c ≤ r3NPuts ∧ r1Ok σ c⌝) $$ [Hσ Hc1] with Hinv
  · inext; iexists σ, 0; iframe Hσ Hc1; ipureintro
    exact ⟨Nat.zero_le _, by simp [r1Ok, hσ, r1Pairs, hrev]⟩
  imodintro
  iexists γc
  iframe Hc2
  iunfold r3Inv
  iexact Hinv

/-- **The update of the put of index `c`**: it carries the driver's half of the counter at `c`, and
its result is the half at `c + 1`. -/
theorem r3PutAu (γk : KVNames) (γc : GName) (c : Nat) (hc : c < r3NPuts) :
    r3Inv (GF := GF) γk γc ∗ monoNatAuthOwn γc (1 : Qp).half c ⊢
      kvOpAu1 γk (.put (r1PutOp c)) (fun _ => monoNatAuthOwn γc (1 : Qp).half (c + 1)) := by
  have Hm := r3N_mask
  iintro ⟨#Hinv, Hd⟩
  unfold kvOpAu1 kvAu1
  iauintro
  unfold atomic_acc
  iunfold r3Inv at Hinv
  iinv Hinv with >Hi Hclose
  icases Hi with ⟨%σ, %c', Hσ, Hc, %Hok⟩
  ihave %Hag := monoNatAuthOwn_agree γc (1 : Qp).half (1 : Qp).half c c' $$ Hd Hc
  obtain ⟨-, rfl⟩ := Hag
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ ((⊤ \ ↑srvRaftN) \ ↑kvN) \ ↑r3N from
    Std.LawfulSet.empty_subset)
  iintro Hclose2
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
  iexists σ
  iframe Hσ
  isplit
  · iintro Hσ
    imod Hclose2 with -
    imod Hclose $$ [Hσ Hc] with -
    · inext; iexists σ, c; iframe; ipureintro; exact Hok
    imodintro
    iframe
  · iintro ⟨Hσ, -⟩
    imod Hclose2 with -
    imod (mono_nat_own_update (GF := GF) (γ := γc) (c + 1) (Nat.le_succ c))
      $$ [Hd Hc] with ⟨Hf, -⟩
    · iapply (monoNat_halves γc c).2; iframe
    icases (monoNat_halves γc (c + 1)).1 $$ Hf with ⟨Hc, Hd⟩
    imod Hclose $$ [Hσ Hc] with -
    · inext; iexists _, (c + 1); iframe Hσ Hc; ipureintro
      exact ⟨hc, r1Ok_put σ c (by simp only [r3NPuts] at hc; omega) Hok.2⟩
    imodintro
    iexact Hd

/-- **The read update after the `NPuts` puts fired**: its result is that the state's range is
exactly the `NPuts` pairs. -/
theorem r3ReadAu (γk : KVNames) (γc : GName) :
    r3Inv (GF := GF) γk γc ∗ monoNatLbOwn γc r3NPuts ⊢
      kvReadAu γk (fun σ => iprop(⌜r1Ok σ r3NPuts⌝)) := by
  have Hm := r3N_mask
  iintro ⟨#Hinv, #Hlb⟩
  unfold kvReadAu kvAu
  imodintro
  iauintro
  unfold atomic_acc
  iunfold r3Inv at Hinv
  iinv Hinv with >Hi Hclose
  icases Hi with ⟨%σ, %c, Hσ, Hc, %Hok⟩
  ihave %Hv := monoNatLbOwn_valid γc _ c r3NPuts $$ Hc Hlb
  have hc : c = r3NPuts := by omega
  subst hc
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ ((⊤ \ ↑srvRaftN) \ ↑kvN) \ ↑r3N from
    Std.LawfulSet.empty_subset)
  iintro Hclose2
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
  iexists σ
  iframe Hσ
  isplit
  · iintro Hσ
    imod Hclose2 with -
    imod Hclose $$ [Hσ Hc] with -
    · inext; iexists σ, r3NPuts; iframe; ipureintro; exact Hok
    imodintro
    iempintro
  · iintro ⟨Hσ, -⟩
    imod Hclose2 with -
    imod Hclose $$ [Hσ Hc] with -
    · inext; iexists σ, r3NPuts; iframe; ipureintro; exact Hok
    imodintro
    iintro !>
    ipureintro; exact Hok.2
end inv

end etcd_restart
end EtcdGrove
end Perennial
