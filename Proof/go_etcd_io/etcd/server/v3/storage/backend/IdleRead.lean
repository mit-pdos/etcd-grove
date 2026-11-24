/-
**A reader of an idle unclaimed tracked bucket sees the writer's contents** (prove-ps2-v3alarm,
2026-11-24; the read model's version of `rbOwnIn`'s promise, which its docstring calls option (a)): a
held shared read transaction at the readers' state `rv`, the client's idle part of one tracked bucket
`n` of the table at contents `r` (`rbOwnIn γ (· = n) r`) and the bucket's claim token
(`rbClaimToks γ P (· = n)`): the readers see `bktOf r n` there. The claim invariant's unclaimed branch
links the readers' element to the writer's while the bucket's flag is clear (`rbClaimU`), the idle part's
quarter of the bucket's element says the flag is clear and the contents are `r`'s, and the token refutes
the claimed branch. Nothing changes: every resource is handed back. For `v3alarm.AlarmStore.restore`'s
read of the alarm bucket (`schema.alarmBackend.GetAllAlarms`). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.backend.ClaimedLemmas
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.ReadLemmas
import all Proof.go_etcd_io.etcd.server.v3.storage.backend.InvBackend

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace backend

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.backend

section idle
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]

/-- **The idle-read law**: a reader holding the shared read transaction at `rv`, with the idle part of
a tracked bucket `n` of the table at `r` and its claim token, sees `bktOf r n` in `n`
(`rvBkt P rv n`); everything is handed back. -/
theorem rtHeldF_rbOwnIn_idle (γ : BNames) (P : BParams) (b rtx : Loc) (rv : RView) (p : Qp)
    (n : GoString) (r : GMap GoString BktData) (hBT : ∃ i, P.BT.lookup n = some i)
    (hRB : P.RB n = true) (E : CoPset) (hE : ↑rbClaimN ⊆ E) :
    iprop(rtHeldF (GF := GF) γ P b rtx rv p ∗ rbOwnIn γ (fun k => k = n) r ∗
      rbClaimToks γ P (fun k => k = n)) ⊢
      |={E}=> iprop(rtHeldF γ P b rtx rv p ∗ rbOwnIn γ (fun k => k = n) r ∗
        rbClaimToks γ P (fun k => k = n) ∗ ⌜rvBkt P rv n = bktOf r n⌝) := by
  iintro ⟨Hh, Hc, Htk⟩
  unfold rbClaimToks
  icases Htk with ⟨#Hinv, Ht⟩
  iinv Hinv with >Hb Hclose
  iunfold rbClaimInv at Hb
  icases Hb with ⟨%Mc, %Cl, Hac, %Hbt, Hm⟩
  have hd : γ.rbD.lookup n ≠ none := by obtain ⟨i, hi⟩ := hBT; exact Hbt n i hi hRB
  unfold rbOwnIn
  ihave Hc := (rbPartF_one γ n r _ hd).1 $$ Hc
  ihave Ht := (mapIf_one γ.rbD (fun k => k = n) n (fun _ => Iff.rfl) hd (fun k =>
    ghostMapElem (GF := GF) γ.rbc k (DFrac.own (1 : Qp).half) (none : Option (Option BktData × Bool)))).2
    $$ Ht
  icases mapAcc γ.rbD (fun k => rbClaimOne (GF := GF) γ k (Cl k))
    (fun k => rbClaimOne (GF := GF) γ k (Cl k)) n hd (fun _ _ => .rfl) $$ Hm with ⟨Hn, Hm⟩
  cases hcl : Cl n
  · ihave Hn := (rbClaimOne_U γ n false rfl).1 $$ Hn
    iunfold rbClaimU at Hn
    icases Hn with ⟨%c, %f, %v, Hk, Hr, Hcn, %HL⟩
    ihave %Hke := ghostMapElem_agree n γ.rbk _ _ _ _ $$ Hk Hc
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj Hke
    have hv : v = bktOf r n := HL rfl
    -- the bucket's readers' quarter as a claimed bucket's share, for the readers' law
    ihave Hrd : rbRd γ n (1 : Qp).half v $$ [Hr]
    · unfold rbRd
      isplitr
      · ipureintro; exact hd
      iexact Hr
    icases rtHeldF_rbRd γ P b rtx rv p n (1 : Qp).half v $$ [$Hh $Hrd] with ⟨Hh, Hrd, %Hrv⟩
    unfold rbRd
    icases Hrd with ⟨-, Hr⟩
    imod Hclose $$ [Hac Hm Hk Hr Hcn] with -
    · inext
      iunfold rbClaimInv
      iexists Mc, Cl
      iframe Hac
      isplitr
      · ipureintro; exact Hbt
      iapply Hm
      iapply (rbClaimOne_U γ n false rfl).2
      iunfold rbClaimU
      iexists r.lookup n, false, v
      iframe Hk Hr Hcn
      ipureintro; intro _; exact hv
    imodintro
    iframe Hh
    isplitl [Hc]
    · iapply (rbPartF_one γ n r (fun _ => false) hd).2 $$ Hc
    isplitl [Ht]
    · iframe Hinv
      iapply (mapIf_one γ.rbD (fun k => k = n) n (fun _ => Iff.rfl) hd (fun k =>
        ghostMapElem (GF := GF) γ.rbc k (DFrac.own (1 : Qp).half)
          (none : Option (Option BktData × Bool)))).1 $$ Ht
    ipureintro; rw [Hrv, hv]
  · ihave Hn := (rbClaimOne_C γ n true rfl).1 $$ Hn
    iunfold rbClaimC at Hn
    icases Hn with ⟨%c, %w, -, Hcn, -⟩
    ihave %Hv := ghostMapElem_agree n γ.rbc _ _ _ _ $$ Hcn Ht
    cases Hv

/-- The same of `rtHeld` (`rtHeldF` at `readTx`'s own share). -/
theorem rtHeld_rbOwnIn_idle (γ : BNames) (P : BParams) (b rtx : Loc) (rv : RView)
    (n : GoString) (r : GMap GoString BktData) (hBT : ∃ i, P.BT.lookup n = some i)
    (hRB : P.RB n = true) (E : CoPset) (hE : ↑rbClaimN ⊆ E) :
    iprop(rtHeld (GF := GF) γ P b rtx rv ∗ rbOwnIn γ (fun k => k = n) r ∗
      rbClaimToks γ P (fun k => k = n)) ⊢
      |={E}=> iprop(rtHeld γ P b rtx rv ∗ rbOwnIn γ (fun k => k = n) r ∗
        rbClaimToks γ P (fun k => k = n) ∗ ⌜rvBkt P rv n = bktOf r n⌝) := by
  rw [rtHeld_eq]
  exact rtHeldF_rbOwnIn_idle γ P b rtx rv _ n r hBT hRB E hE

end idle

end backend
end EtcdGrove
end Perennial
