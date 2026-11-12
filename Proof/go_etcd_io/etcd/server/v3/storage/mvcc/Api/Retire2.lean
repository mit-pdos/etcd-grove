/-
**Two readers retired with one later credit** (2026-11-06; for the constructors' open token, which
keeps the compactor's reader and the writer's own, `writerOwn`, for `Restore`). Lean-first (no
Rocq counterpart). `readerPool_retire` twice under one opening of the pool's invariant.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvStore

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvcc

open Iris Iris.BI Iris.ProofMode

section retire
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- **Two idle tickets retired** (one later credit): two backend tokens, the retired count up by
two. -/
theorem readerPool_retire2 (γ : StoreNames) (dq : DFrac) (o : StoreObjs) (n : Nat) :
    ⊢ £ 1 -∗ readerPool (GF := GF) γ -∗ curAt γ dq o -∗ ownToks γ.tk 1 -∗ ownToks γ.tk 1 -∗
      retiredAt γ n ={⊤}=∗
      storeRT γ ∗ storeRT γ ∗ retiredAt γ (n + 2) ∗ curAt γ dq o := by
  iintro Hlc #Hp Hpin Ht Ht2 Hret
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
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  imod ownTokAuth_delete_S γ.tk k' $$ Ha Ht with Ha
  icombine Ha Ht2 gives %Hle2
  obtain ⟨k'', rfl⟩ : ∃ k'', k' = k'' + 1 := ⟨k' - 1, by omega⟩
  imod ownTokAuth_delete_S γ.tk k'' $$ Ha Ht2 with Ha
  iunfold retiredAt at Hret
  ihave %Hrn := ghostVar_agree (GF := GF) γ.tkr r _ n _ $$ Har Hret
  subst Hrn
  imod ghostVar_update_halves (GF := GF) (r + 2) γ.tkr r r $$ Har Hret with ⟨Har, Htr⟩
  rw [List.replicate_succ, List.replicate_succ]
  icases BigSepL.bigSepL_cons.1 $$ Hs with ⟨H1, Hs⟩
  icases BigSepL.bigSepL_cons.1 $$ Hs with ⟨H2, Hs⟩
  imod Hclose $$ [Hc Ha Hao Haw Har Hs Hds Hws] with -
  · inext
    iexists γ.phys, o'
    rw [StoreNames.withPhys_self]
    iframe Hc
    iunfold poolBody
    iexists k'', j, w, r + 2
    iframe Ha Hao Haw Har Hs Hds Hws
    ipureintro; omega
  iunfold idxSlot at H1 H2
  icases H1 with ⟨-, Hrt⟩
  icases H2 with ⟨-, Hrt2⟩
  imodintro
  iframe Hrt Hrt2 Hpin
  iunfold retiredAt
  iexact Htr

/-- **Two idle readers retire their tickets** (one later credit; `readerPool_retire2`). -/
theorem storeReader_retire2 (s : Loc) (γ : StoreNames) (dq : DFrac) (o : StoreObjs) (n : Nat) :
    ⊢ £ 1 -∗ isStore (GF := GF) s γ -∗ curAt γ dq o -∗ storeReader s γ -∗ storeReader s γ -∗
      retiredAt γ n ={⊤}=∗
      storeRT γ ∗ storeRT γ ∗ retiredAt γ (n + 2) ∗ curAt γ dq o := by
  iintro Hlc #Hs Hpin Hr Hr2 Hret
  iunfold isStore at Hs
  iNamed Hs
  iunfold storeReader at Hr Hr2
  iNamedSuffix Hr2 "2"
  iNamed Hr
  iapply readerPool_retire2 γ dq o n $$ Hlc Hpool Hpin Htk Htk2 Hret

end retire

end mvcc
end EtcdGrove
end Perennial
