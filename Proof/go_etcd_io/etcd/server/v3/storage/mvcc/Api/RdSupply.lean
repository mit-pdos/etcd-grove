/-
**The store handle's readers' supply** (track A, request 3, 2026-11-06; `notes/mvcc-api-invariants.md`,
"M4, track A, request 3"). Lean-first (no Rocq counterpart). `Api.lean` imports it non-publicly:
its `isMvccPlain` holds a `rdSupply`.

* `rdSupply`: a thread pool whose copies each lend a reader of the store (`storeReaderC`) and take
  it back. A plain store's pool is of `storeReaderC` itself; a watchable store's inner store's is
  the watchable store's pool of `watchReader`s (the outer lock's slot stays in the wand), so the two
  handles share one pool.

* `rdSupply_init`: a readers' supply from `n` readers of the store (`threadBound ≤ n + 1`: a plain
  store's pool, `NewStoreApi`); `rdSupply_watch`: the inner store's supply from the watchable
  store's pool of `watchReader`s (one pool for both handles; `KV.Compact`'s watchable arm).
* `rdSupply_lend`: a reader of the store for a thread token, with the token's way back
  (`tokBack`); the reader is not timeless (its locks' guards hold invariants), so the borrow costs a
  later credit.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Api.TxnHandle

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvcc

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- **The store's readers' supply** (see the header). -/
def rdSupply (s : Loc) (γ : StoreNames) : IProp GF :=
  iprop(∃ (N : Namespace) (γp : GName) (R : IProp GF), threadPool.isThreadPool N γp R ∗
    □ (R -∗ storeReaderC s γ ∗ (storeReaderC s γ -∗ R)))

instance rdSupply_persistent (s : Loc) (γ : StoreNames) :
    Persistent (rdSupply (GF := GF) s γ) := by
  unfold rdSupply; infer_instance

/-- **A plain store's readers' supply**, from `n` of its readers, enough for every thread but one. -/
theorem rdSupply_init (N : Namespace) (s : Loc) (γ : StoreNames) (n : Nat)
    (hn : threadBound GF ≤ n + 1) :
    ([∗list] _x ∈ List.replicate n (), storeReaderC (GF := GF) s γ) ⊢ |={⊤}=> rdSupply s γ := by
  iintro H
  imod threadPool.init N (storeReaderC (GF := GF) s γ) ⊤ n hn $$ H with ⟨%γp, #Hp⟩
  imodintro
  iunfold rdSupply
  iexists N, γp, storeReaderC s γ
  iframe Hp
  iintro !> HR
  iframe HR
  iintro HR; iexact HR

/-- **The inner store's readers' supply is the watchable store's pool** (each `watchReader` lends
its inner store's reader, the watchable store's lock slot kept in the wand). -/
theorem rdSupply_watch (γp : GName) (s st : Loc) (γw : WsNames) :
    threadPool.isThreadPool (GF := GF) watchRdPoolN γp (watchReader s st γw) ⊢
      rdSupply st γw.st := by
  iintro #Hp
  iunfold rdSupply
  iexists watchRdPoolN, γp, watchReader s st γw
  iframe Hp
  iintro !> HR
  iunfold watchReader at HR
  icases HR with ⟨HR, Hmu⟩
  iunfold storeReader at HR
  iframe HR
  iintro HR
  iunfold watchReader
  iframe Hmu
  iunfold storeReader
  iexact HR

/-- **A reader for a thread token**, with the token's way back (`tokBack`). -/
theorem rdSupply_lend (s : Loc) (γ : StoreNames) :
    rdSupply (GF := GF) s γ ∗ £ 1 ∗ threadTok ⊢ |={⊤}=> storeReaderC s γ ∗ api.tokBack s γ := by
  iintro ⟨#Hsup, Hlc, Htok⟩
  iunfold rdSupply at Hsup
  icases Hsup with ⟨%N, %γp, %R, #Hp, #Hw⟩
  imod threadPool.borrow_lc N γp R ⊤ (fun _ _ => CoPset.mem_full) $$ [$Hlc $Hp $Htok]
    with ⟨HR, Hloan⟩
  icases Hw $$ HR with ⟨Hrd, Hback⟩
  imodintro
  iframe Hrd
  iunfold api.tokBack
  iintro Hrd
  ihave HR := Hback $$ Hrd
  iapply threadPool.giveBack N γp R ⊤ (fun _ _ => CoPset.mem_full)
  iframe Hp Hloan HR

end proof

end mvcc
end EtcdGrove
end Perennial
