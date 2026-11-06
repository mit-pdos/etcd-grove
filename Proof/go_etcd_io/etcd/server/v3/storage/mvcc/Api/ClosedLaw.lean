/-
**The shutdown law and the reader tokens' split** (the reader tokens, 2026-11-06; `notes/decisions.md`,
"mvcc's API: the store's readers as client-held tokens"). Lean-first (no Rocq counterpart). Over the
sealed definitions of `Api.lean` (imported with `import all`).

* `mvccReaders_split.law_holds`: the tokens are the readers' pool's tickets (`ownToks_add`).
* `mvccClosed_rest.law_holds`: `Close`'s post pins the store's current names (its part of `curAt`,
  agreeing with the backend share's); every ticket (the client's `mvccReaderN` and the two `Close`
  regained) retires from the readers' pool at once (`readerPool_retireN`, one later credit, the one
  `mvccClosed` holds), giving their backend reader tokens; with the open token's two (the compactor's
  and the writer's) and the compaction job's (`compactJobResM`), every reader slot's share of the
  backend's open token (`storeRTs_shares`): the storage's rest.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.Api
import all Spec.go_etcd_io.etcd.server.v3.storage.mvcc.Api
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.ReaderRetire

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvcc
namespace api

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

theorem mvccReaders_split.law_holds : mvccReaders_split.law (GF := GF) := by
  intro γ n m
  unfold mvccReaders
  exact ownToks_add m n _

private theorem rep_cons1 (P : IProp GF) (n : Nat) :
    P ∗ ([∗list] _x ∈ List.replicate n (), P) ⊢ [∗list] _x ∈ List.replicate (n + 1) (), P := by
  rw [List.replicate_succ]
  iintro ⟨H1, H⟩
  iapply BigSepL.bigSepL_cons.2
  iframe H1 H

theorem mvccClosed_rest.law_holds : mvccClosed_rest.law (GF := GF) := by
  intro (γ : StoreNames) q B Pk
  iintro ⟨Hcl, Hrd, HB⟩
  iunfold mvccClosed at Hcl
  icases Hcl with ⟨%p, %dq, %o, Hlc, Hpool, Hcur, Hret, HRT1, HRT2, Ht2, Hjob⟩
  iunfold mvccBackend at HB
  icases HB with ⟨HF, %p', %o', %d, Hcur', %Hd, #Hbk, #Hrg, #Hhp, #Hwts, %Hlp⟩
  obtain ⟨hpk, hcm, hdB⟩ := Hd
  subst hdB
  -- the closed store's names are the share's
  iunfold curAt at Hcur Hcur'
  simp only [StoreNames.withPhys_cur]
  icombine Hcur Hcur' gives %Hv
  obtain ⟨-, Hv⟩ := Hv
  simp only [Prod.mk.injEq, StoreNames.withPhys_phys] at Hv
  obtain ⟨-, rfl⟩ := Hv
  ihave Hcur : curAt (GF := GF) (γ.withPhys p) dq o $$ [Hcur]
  · iunfold curAt; simp only [StoreNames.withPhys_cur]; iexact Hcur
  ihave Hcur' : curAt (GF := GF) (γ.withPhys p) (DFrac.own q.half.half.half) o' $$ [Hcur']
  · iunfold curAt; simp only [StoreNames.withPhys_cur]; iexact Hcur'
  have hk : (γ.withPhys p).kb = some d := hpk
  have hj : nJobRd (γ.withPhys p).kb = 1 := by rw [hk]; simp [nJobRd, hcm]
  -- every ticket retired
  iunfold mvccReaders at Hrd
  ihave Hts : ownToks (GF := GF) (γ.withPhys p).tk (mvccReaderN + 2) $$ [Hrd Ht2]
  · rw [StoreNames.withPhys_tk]
    iapply (ownToks_add 2 mvccReaderN _).2
    iframe Hrd Ht2
  ihave Hpool' : readerPool (GF := GF) (γ.withPhys p) $$ [Hpool]
  · rw [readerPool_withPhys]; iexact Hpool
  imod readerPool_retireN (γ.withPhys p) dq o (2 + nJobRd (γ.withPhys p).kb) (mvccReaderN + 2)
    $$ Hlc Hpool' Hcur Hts Hret with ⟨Hrts, -, -⟩
  -- with the open token's two, the store's stock but the job's
  have hN : nReaders - nJobRd (γ.withPhys p).kb = mvccReaderN + 2 + 1 + 1 := by
    rw [hj]
    have h1 : mvccReaderN = backend.rdStockN - 7 := rfl
    have h2 : nReaders = backend.rdStockN - 2 := rfl
    have : 7 ≤ backend.rdStockN := by rw [backend.rdStockN_val]; omega
    omega
  ihave Hrts : [∗list] _x ∈ List.replicate (nReaders - nJobRd (γ.withPhys p).kb) (),
      storeRT (GF := GF) (γ.withPhys p) $$ [Hrts HRT1 HRT2]
  · rw [hN]
    iapply rep_cons1
    iframe HRT1
    iapply rep_cons1
    iframe HRT2 Hrts
  ihave Hst := storeRTs_shares (γ.withPhys p) d hk $$ [$Hrts $Hjob]
  imodintro
  isplitl [Hst]
  · iunfold storageRest
    iexact Hst
  iunfold mvccBackend
  iframe HF
  iexists p, o', d
  iframe Hcur' Hbk Hrg Hhp Hwts
  ipureintro; exact ⟨⟨hpk, hcm, rfl⟩, Hlp⟩

end laws

end api
end mvcc
end EtcdGrove
end Perennial
