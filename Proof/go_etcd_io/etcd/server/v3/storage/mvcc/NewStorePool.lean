/-
**B3 (mvccfull F1): a retired reader slot back in the pool** (`NewStore` over an image). `NewStore`'s
`restore()` lends a reader's token to the compaction it resumes, after the store (and its readers'
pool) is made: the pool is made with that token counted retired, then given it back as a slot
(`readerPool_unretire`, the inverse of `readerPool_retire`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvStore

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvcc

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- **A retired slot back** (one later credit), at a pin: a slot of the current objects (an index
slot and a backend token) put in the pool, a ticket for it, the retired count one less. -/
theorem readerPool_unretire (γ : StoreNames) (dq : DFrac) (o : StoreObjs) (n : Nat) :
    ⊢ £ 1 -∗ readerPool (GF := GF) γ -∗ curAt γ dq o -∗ idxSlot γ o -∗ retiredAt γ (n + 1) ={⊤}=∗
      ownToks γ.tk 1 ∗ retiredAt γ n ∗ curAt γ dq o := by
  iintro Hlc #Hp Hpin H1 Hret
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
  imod ownTokAuth_add 1 γ.tk k $$ Ha with ⟨Ha, Ht⟩
  iunfold retiredAt at Hret
  ihave %Hrn := ghostVar_agree (GF := GF) γ.tkr r _ (n + 1) _ $$ Har Hret
  subst Hrn
  imod ghostVar_update_halves (GF := GF) n γ.tkr (n + 1) (n + 1) $$ Har Hret with ⟨Har, Htr⟩
  imod Hclose $$ [Hc Ha Hao Haw Har Hs Hds Hws H1] with -
  · inext
    iexists γ.phys, o'
    rw [StoreNames.withPhys_self]
    iframe Hc
    iunfold poolBody
    iexists k + 1, j, w, n
    rw [List.replicate_succ]
    iframe Ha Hao Haw Har Hds Hws
    isplitl [H1 Hs]
    · iapply BigSepL.bigSepL_cons.2; iframe H1 Hs
    ipureintro; omega
  imodintro
  iframe Ht Hpin
  iunfold retiredAt
  iexact Htr

end lemmas

end mvcc
end EtcdGrove
end Perennial
