/-
The watchable store's right to close in compaction mode (M2, the storage side, the approval's items
20 and 23, 2026-10-30): the watchable store's own stop channel's close and waiter (as `wsCloser`)
with the inner store's restorable compaction right (`compactRightR`, `InvCompact.lean`) in place of
its closer, made from `wsCloser` and the authority's half `New` gives in compaction mode
(`wsCloserR_of_wsCloser`); and the right to close by the mode (`wsCloserM`), what
`watchableStore.Close` takes.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvWatchSync
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvCompact

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvcc

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

section closer
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- **The watchable store's closer, a compacting store's** (the approval's item 20; what the server
keeps in compaction mode, D22's `srvKVCloser` by the mode): the watchable store's own stop channel's
close and waiter (as `wsCloser`), and the inner store's restorable compaction right at `c` in place
of its closer. -/
@[no_expose] def wsCloserR (s st : Loc) (γs : StoreNames) (c : Int) : IProp GF :=
  iprop(∃ stc : Loc, s.[watchableStore, go!"stopc"] ↦□ stc ∗ stopCloser stc ∗ wsWaiter s ∗
    compactRightR st γs c)

/-- **The watchable store's closer and the inner store's right, apart** (for the store's own proofs
and the restore's drafts). -/
theorem wsCloserR_iff (s st : Loc) (γs : StoreNames) (c : Int) :
    wsCloserR (GF := GF) s st γs c ⊣⊢
      ∃ stc : Loc, s.[watchableStore, go!"stopc"] ↦□ stc ∗ stopCloser stc ∗ wsWaiter s ∗
        compactRightR st γs c := by
  unfold wsCloserR; exact .rfl

/-- **The compaction right from the watchable store's closer** (the approval's item 20, in place
of step 1's discarding `compactRight_of_wsCloser`: the closer is kept; the step after `NewServer`'s
last error return): the inner closer and the authority's half (`crevRightM`, on) make the
restorable right at `-1`; the watchable store's own parts are kept. -/
theorem wsCloserR_of_wsCloser (s st : Loc) (γs : StoreNames) (h : γs.cm = true) (E : CoPset) :
    ⊢ wsCloser (GF := GF) s st γs -∗ crevRightM γs ={E}=∗ wsCloserR s st γs (-1) := by
  unfold crevRightM
  simp only [h, ↓reduceIte]
  iintro Hcl Hcr
  iunfold wsCloser at Hcl
  icases Hcl with ⟨%stc, #Hstc, Hsc, Hw, Hcl⟩
  imod compactRightR_of_closer st γs E $$ Hcl Hcr with Hr
  imodintro
  iunfold wsCloserR
  iexists stc
  iframe Hstc Hsc Hw Hr

/-- **The watchable store's right to close, by the mode** (the approval's item 23, "alike"
`store.Close`'s `storeCloserM`, by the backend instance's mode): off, `wsCloser`; on, `wsCloserR`
at the inner store's compaction revision `c`. -/
def wsCloserM (s st : Loc) (γs : StoreNames) (c : Int) : IProp GF :=
  if kbCmpM γs.kb then wsCloserR s st γs c else wsCloser s st γs

theorem wsCloserM_off (s st : Loc) (γs : StoreNames) (c : Int) (h : ¬ kbCmpM γs.kb) :
    wsCloserM (GF := GF) s st γs c ⊣⊢ wsCloser s st γs := by
  unfold wsCloserM; simp only [h, ↓reduceIte]; exact .rfl

theorem wsCloserM_on (s st : Loc) (γs : StoreNames) (c : Int) (h : kbCmpM γs.kb) :
    wsCloserM (GF := GF) s st γs c ⊣⊢ wsCloserR s st γs c := by
  unfold wsCloserM; simp only [h, ↓reduceIte]; exact .rfl

/-- **What `watchableStore.Close` uses, in either mode**: its stop channel's close and waiter, and
the inner store's right to close by the mode (`storeCloserM`, what `store.Close` takes). -/
theorem wsCloserM_close (s st : Loc) (γs : StoreNames) (c : Int) :
    wsCloserM (GF := GF) s st γs c ⊢
      ∃ stc : Loc, s.[watchableStore, go!"stopc"] ↦□ stc ∗ stopCloser stc ∗ wsWaiter s ∗
        storeCloserM st γs c := by
  iintro H
  by_cases hm : kbCmpM γs.kb
  · icases (wsCloserM_on s st γs c hm).1 $$ H with H
    icases (wsCloserR_iff s st γs c).1 $$ H with ⟨%stc, #Hstc, Hsc, Hw, Hr⟩
    iexists stc
    iframe Hstc Hsc Hw
    iapply (storeCloserM_on st γs c hm).2
    iexact Hr
  · icases (wsCloserM_off s st γs c hm).1 $$ H with H
    iunfold wsCloser at H
    icases H with ⟨%stc, #Hstc, Hsc, Hw, Hcl⟩
    iexists stc
    iframe Hstc Hsc Hw
    iapply (storeCloserM_off st γs c hm).2
    iexact Hcl

end closer

end mvcc
end EtcdGrove
end Perennial
