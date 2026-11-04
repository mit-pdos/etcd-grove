/-
**Idle readers retire together** (stage R-D1, 2026-11-04): the store's readers' tickets traded for
backend tokens of their own in bulk, at one later credit (`storeReaders_retire`, the bulk form of
`storeReader_retire`, `InvStore.lean`), for `NewServer`'s transport-start failure, where the backend's
`Close` needs every share of the open token back (its ~8·10⁸ idle readers retired at once). And the
law the loops use to leave their reader of the inner store (`watchReader_storeReader`,
`InvWatchSync.lean`). And every retired reader's open share back (`storeRTs_shares`). Lean-first
(no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvStore

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

namespace mvcc

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

section retire
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

private theorem rep_mono (P Q : IProp GF) (h : P ⊢ Q) : ∀ n : Nat,
    ([∗list] _x ∈ List.replicate n (), P) ⊢ [∗list] _x ∈ List.replicate n (), Q
  | 0 => by rw [List.replicate_zero]; iintro -; iapply BigSepL.bigSepL_nil_intro; iempintro
  | n + 1 => by
    rw [List.replicate_succ]
    iintro H
    icases BigSepL.bigSepL_cons.1 $$ H with ⟨H1, H⟩
    iapply BigSepL.bigSepL_cons.2
    isplitl [H1]
    · iapply h $$ H1
    iapply rep_mono P Q h n $$ H

private theorem toks_of_rep (γ : GName) : ∀ n : Nat,
    ([∗list] _x ∈ List.replicate n (), ownToks (GF := GF) γ 1) ⊢ |==> ownToks γ n
  | 0 => by iintro -; iapply ownToks_0
  | n + 1 => by
    rw [List.replicate_succ]
    iintro H
    icases BigSepL.bigSepL_cons.1 $$ H with ⟨H1, H⟩
    imod toks_of_rep γ n $$ H with H
    imodintro
    iapply (ownToks_add 1 n γ).2
    iframe H H1

/-- **`m` tickets of the readers' pool retire together** (one later credit; `readerPool_retire`'s
bulk form), at a pin: `m` slots out of the pool for good, their index slots dropped. -/
theorem readerPool_retireN (γ : StoreNames) (dq : DFrac) (o : StoreObjs) (n m : Nat) :
    ⊢ £ 1 -∗ readerPool (GF := GF) γ -∗ curAt γ dq o -∗ ownToks γ.tk m -∗ retiredAt γ n ={⊤}=∗
      ([∗list] _x ∈ List.replicate m (), storeRT γ) ∗ retiredAt γ (n + m) ∗ curAt γ dq o := by
  iintro Hlc #Hp Hpin Ht Hret
  iunfold readerPool at Hp
  imod inv_acc (E := ⊤) (N := poolN) (P := iprop(∃ (p : PhysNames) (o : StoreObjs),
      curAt (GF := GF) (γ.withPhys p) (DFrac.own (1 : Qp).half.half.half) o ∗
        poolBody (γ.withPhys p) o))
    (by exact CoPset.subseteq_top) $$ Hp with ⟨HP, Hclose⟩
  imod (lc_fupd_elim_later (P := iprop(∃ (p : PhysNames) (o : StoreObjs),
      curAt (GF := GF) (γ.withPhys p) (DFrac.own (1 : Qp).half.half.half) o ∗
        poolBody (γ.withPhys p) o))) $$ Hlc HP with HP
  icases HP with ⟨%p, %o', Hc, HP⟩
  ihave %Hv := curAt_pin γ p _ _ o o' $$ [Hpin Hc]
  · iframe Hpin Hc
  obtain ⟨rfl, rfl⟩ := Hv
  rw [StoreNames.withPhys_self]
  iunfold poolBody at HP
  icases HP with ⟨%k, %j, %w, %r, Ha, Hao, Haw, Har, Hs, Hds, Hws, %Hk⟩
  icombine Ha Ht gives %Hle
  obtain ⟨k', rfl⟩ : ∃ k', k = m + k' := ⟨k - m, by omega⟩
  imod ownTokAuth_sub m γ.tk (m + k') $$ Ha Ht with Ha
  rw [show m + k' - m = k' by omega]
  iunfold retiredAt at Hret
  ihave %Hrn := ghostVar_agree (GF := GF) γ.tkr r _ n _ $$ Har Hret
  subst Hrn
  imod ghostVar_update_halves (GF := GF) (r + m) γ.tkr r r $$ Har Hret with ⟨Har, Htr⟩
  rw [← List.replicate_append_replicate]
  icases BigSepL.bigSepL_append.1 $$ Hs with ⟨H1, Hs⟩
  imod Hclose $$ [Hc Ha Hao Haw Har Hs Hds Hws] with -
  · inext
    iexists γ.phys, o'
    rw [StoreNames.withPhys_self]
    iframe Hc
    iunfold poolBody
    iexists k', j, w, r + m
    iframe Ha Hao Haw Har Hs Hds Hws
    ipureintro; omega
  imodintro
  iframe Hpin
  isplitl [H1]
  · iapply rep_mono (idxSlot γ o') (storeRT γ) ?_ m $$ H1
    iintro H
    iunfold idxSlot at H
    icases H with ⟨-, H⟩
    iexact H
  iunfold retiredAt
  iexact Htr

/-- **Idle readers retire together** (R-D1, 2026-11-04; one later credit): `m` idle readers' tickets
for `m` backend tokens of their own, the retired count up by `m`, at the caller's pin (`writerFrag`,
which fixes the current names); their slots of the store's locks dropped. `storeReader_retire` is the
one-reader form, at a pin of the objects. -/
theorem storeReaders_retire (s : Loc) (γ : StoreNames) (m n : Nat) :
    ⊢ £ 1 -∗ isStore (GF := GF) s γ -∗ writerFrag γ -∗
      ([∗list] _x ∈ List.replicate m (), storeReader s γ) -∗ retiredAt γ n ={⊤}=∗
      ([∗list] _x ∈ List.replicate m (), storeRT γ) ∗ retiredAt γ (n + m) ∗ writerFrag γ := by
  iintro Hlc #Hs Hfrag Hrs Hret
  iunfold isStore at Hs
  iNamed Hs
  iunfold writerFrag at Hfrag
  icases Hfrag with ⟨%o, Hpin⟩
  ihave Hts := rep_mono (storeReader s γ) (ownToks γ.tk 1) ?_ m $$ Hrs
  · iintro H
    iunfold storeReader at H
    iNamed H
    iexact Htk
  imod toks_of_rep γ.tk m $$ Hts with Ht
  imod readerPool_retireN γ _ o n m $$ Hlc Hpool Hpin Ht Hret with ⟨Hrt, Hret, Hpin⟩
  imodintro
  iframe Hrt Hret
  iunfold writerFrag
  iexists o
  iexact Hpin

/-- **Every reader retired, with the compaction job's resource, gives the backend's stock of open
shares** (R-D1, 2026-11-04): the store's `nReaders - nJobRd` readers' backend tokens and, compacting,
the job's reader (`compactJobResM`'s), each with the share `rdOpen` of the backend open, for its
`Close` (`backend.bOpen_one_pool`). -/
theorem storeRTs_shares (γ : StoreNames) (dk : KBReal) (hk : γ.kb = some dk) :
    ([∗list] _x ∈ List.replicate (backend.rdStockN - nJobRd γ.kb) (), storeRT (GF := GF) γ) ∗
      compactJobResM γ.kb ⊢
      [∗list] _x ∈ List.replicate backend.rdStockN (), backend.bOpen dk.γB backend.rdOpen := by
  have hsh : storeRT (GF := GF) γ ⊢ backend.bOpen dk.γB backend.rdOpen := by
    unfold storeRT; rw [hk]; unfold kbRT; iintro ⟨-, H⟩; iexact H
  unfold compactJobResM nJobRd
  rw [hk]
  cases hcm : dk.cm with
  | false =>
    have hoff : ¬ kbCmpM (some dk) := by unfold kbCmpM; simp [hcm]
    simp only [hoff, hcm, ↓reduceIte, Nat.sub_zero, Bool.false_eq_true]
    iintro ⟨H, -⟩
    iapply rep_mono _ _ hsh _ $$ H
  | true =>
    have hon : kbCmpM (some dk) := by unfold kbCmpM; simp [hcm]
    simp only [hon, hcm, ↓reduceIte]
    obtain ⟨k, hk1⟩ : ∃ k, backend.rdStockN = k + 1 :=
      ⟨backend.rdStockN - 1, by rw [backend.rdStockN_val]⟩
    rw [hk1, Nat.add_sub_cancel, List.replicate_succ]
    iintro ⟨H, Hrt, -⟩
    iapply BigSepL.bigSepL_cons.2
    isplitl [Hrt]
    · unfold kbRT; icases Hrt with ⟨-, Hrt⟩; iexact Hrt
    iapply rep_mono _ _ hsh _ $$ H

end retire

end mvcc

end EtcdGrove
end Perennial
