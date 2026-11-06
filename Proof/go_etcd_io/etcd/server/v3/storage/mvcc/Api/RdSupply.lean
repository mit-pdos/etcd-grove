/-
**The store handle's readers' supply** (track A, request 3, 2026-11-06; `notes/mvcc-api-invariants.md`,
"M4, track A, request 3"; the reader tokens, 2026-11-06, `notes/decisions.md`, "mvcc's API: the
store's readers as client-held tokens"). Lean-first (no Rocq counterpart). `Api.lean` imports it
non-publicly: its `isMvccPlain` holds a `rdSupply`.

A reader of the store (`storeReaderC`) is its locks' slots (`storeSlots`: a reader slot of each of
`s.mu` and `s.revMu`) and a ticket of the readers' pool (`ownToks γ.tk 1`), the right to borrow one
of the backend's reader slots the pool holds at the current storage. The handles keep the locks'
slots in a thread pool (the store's own locks, paid for by a thread token); the tickets are the
client's (the API's `mvccReaders`), so that a client holding all of them knows no read is in flight.

* `rdSupply`: a thread pool whose copies each lend the store's locks' slots and take them back. A
  plain store's pool is of `storeSlots` itself; a watchable store's inner store's is the watchable
  store's pool of `watchSlots` (with the watchable store's `s.mu` slot, kept in the wand), so the two
  handles share one pool.
* `rdSupply_init`: a readers' supply from `n` readers of the store (`threadBound ≤ n + 1`: a plain
  store's pool, `NewStoreApi`), their `n` tickets apart; `rdSupply_watch`: the inner store's supply
  from the watchable store's pool.
* `rdSupply_lend`: a reader of the store for a thread token and a ticket, with their way back
  (`tokBack`); the slots are not timeless (their locks' guards hold invariants), so the borrow costs
  a later credit (`rdSupply_lendL`: under a later instead). `watchReader_lend`: the same of the
  watchable store's pool, a whole `watchReader` (a stream's calls of its store).
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

/-- **The store's locks' slots a reader holds** (a `storeReaderC` without its ticket). -/
def storeSlots (s : Loc) (γ : StoreNames) : IProp GF :=
  iprop(sync.ownRWMutex (muAddr s) (muInv s γ) ∗ sync.ownRWMutex (revMuAddr s) (revMuInv s γ))

/-- A reader is its slots and its ticket. -/
theorem storeReaderC_split (s : Loc) (γ : StoreNames) :
    storeReaderC (GF := GF) s γ ⊣⊢ storeSlots s γ ∗ ownToks γ.tk 1 := by
  constructor
  · iintro H
    iunfold storeReaderC at H
    iNamed H
    iunfold storeSlots
    iframe Hmu HrevMu Htk
  · iintro ⟨H, Htk⟩
    iunfold storeSlots at H
    icases H with ⟨Hmu, HrevMu⟩
    iunfold storeReaderC
    simp only [named]
    iframe Hmu HrevMu Htk

/-- **The watchable store's slots a reader of it holds** (a `watchReader` without its ticket). -/
def watchSlots (s st : Loc) (γ : WsNames) : IProp GF :=
  iprop(storeSlots st γ.st ∗ sync.ownRWMutex (wsMuAddr s) (watchStoreInv s γ))

/-- A reader of the watchable store is its slots and its ticket. -/
theorem watchReader_split (s st : Loc) (γ : WsNames) :
    watchReader (GF := GF) s st γ ⊣⊢ watchSlots s st γ ∗ ownToks γ.st.tk 1 := by
  constructor
  · iintro H
    iunfold watchReader at H
    icases H with ⟨Hr, Hw⟩
    iunfold storeReader at Hr
    icases (storeReaderC_split st γ.st).1 $$ Hr with ⟨Hs, Ht⟩
    iunfold watchSlots
    iframe Hs Hw Ht
  · iintro ⟨H, Ht⟩
    iunfold watchSlots at H
    icases H with ⟨Hs, Hw⟩
    iunfold watchReader
    iframe Hw
    iunfold storeReader
    iapply (storeReaderC_split st γ.st).2
    iframe Hs Ht

/-- `n` readers are their slots and `n` tickets. -/
theorem storeReaders_split (s : Loc) (γ : StoreNames) : ∀ n : Nat,
    ([∗list] _x ∈ List.replicate n (), storeReaderC (GF := GF) s γ) ⊢ |==> (
      ([∗list] _x ∈ List.replicate n (), storeSlots s γ) ∗ ownToks γ.tk n)
  | 0 => by
    rw [List.replicate_zero]
    iintro -
    imod ownToks_0 γ.tk with Ht
    imodintro
    iframe Ht
    iapply BigSepL.bigSepL_nil_intro; iempintro
  | n + 1 => by
    rw [List.replicate_succ]
    iintro H
    icases BigSepL.bigSepL_cons.1 $$ H with ⟨H1, H⟩
    imod storeReaders_split s γ n $$ H with ⟨Hs, Ht⟩
    icases (storeReaderC_split s γ).1 $$ H1 with ⟨Hs1, Ht1⟩
    imodintro
    isplitl [Hs Hs1]
    · iapply BigSepL.bigSepL_cons.2; iframe Hs Hs1
    rw [Nat.add_comm]
    iapply (ownToks_add n 1 γ.tk).2
    iframe Ht1 Ht

/-- `n` readers of the watchable store are their slots and `n` tickets. -/
theorem watchReaders_split (s st : Loc) (γ : WsNames) : ∀ n : Nat,
    ([∗list] _x ∈ List.replicate n (), watchReader (GF := GF) s st γ) ⊢ |==> (
      ([∗list] _x ∈ List.replicate n (), watchSlots s st γ) ∗ ownToks γ.st.tk n)
  | 0 => by
    rw [List.replicate_zero]
    iintro -
    imod ownToks_0 γ.st.tk with Ht
    imodintro
    iframe Ht
    iapply BigSepL.bigSepL_nil_intro; iempintro
  | n + 1 => by
    rw [List.replicate_succ]
    iintro H
    icases BigSepL.bigSepL_cons.1 $$ H with ⟨H1, H⟩
    imod watchReaders_split s st γ n $$ H with ⟨Hs, Ht⟩
    icases (watchReader_split s st γ).1 $$ H1 with ⟨Hs1, Ht1⟩
    imodintro
    isplitl [Hs Hs1]
    · iapply BigSepL.bigSepL_cons.2; iframe Hs Hs1
    rw [Nat.add_comm]
    iapply (ownToks_add n 1 γ.st.tk).2
    iframe Ht1 Ht

/-- **The store's readers' supply** (see the header). -/
def rdSupply (s : Loc) (γ : StoreNames) : IProp GF :=
  iprop(∃ (N : Namespace) (γp : GName) (R : IProp GF), threadPool.isThreadPool N γp R ∗
    □ (R -∗ storeSlots s γ ∗ (storeSlots s γ -∗ R)))

instance rdSupply_persistent (s : Loc) (γ : StoreNames) :
    Persistent (rdSupply (GF := GF) s γ) := by
  unfold rdSupply; infer_instance

/-- **A plain store's readers' supply**, from `n` of its readers, enough for every thread but one;
their tickets apart. -/
theorem rdSupply_init (N : Namespace) (s : Loc) (γ : StoreNames) (n : Nat)
    (hn : threadBound GF ≤ n + 1) :
    ([∗list] _x ∈ List.replicate n (), storeReaderC (GF := GF) s γ) ⊢ |={⊤}=> (
      rdSupply s γ ∗ ownToks γ.tk n) := by
  iintro H
  imod storeReaders_split s γ n $$ H with ⟨H, Ht⟩
  imod threadPool.init N (storeSlots (GF := GF) s γ) ⊤ n hn $$ H with ⟨%γp, #Hp⟩
  imodintro
  iframe Ht
  iunfold rdSupply
  iexists N, γp, storeSlots s γ
  iframe Hp
  iintro !> HR
  iframe HR
  iintro HR; iexact HR

/-- **The inner store's readers' supply is the watchable store's pool** (each `watchSlots` lends
its inner store's slots, the watchable store's lock slot kept in the wand). -/
theorem rdSupply_watch (γp : GName) (s st : Loc) (γw : WsNames) :
    threadPool.isThreadPool (GF := GF) watchRdPoolN γp (watchSlots s st γw) ⊢
      rdSupply st γw.st := by
  iintro #Hp
  iunfold rdSupply
  iexists watchRdPoolN, γp, watchSlots s st γw
  iframe Hp
  iintro !> HR
  iunfold watchSlots at HR
  icases HR with ⟨HR, Hmu⟩
  iframe HR
  iintro HR
  iunfold watchSlots
  iframe Hmu HR

/-- **A reader for a thread token and a ticket**, with their way back (`tokBack`). -/
theorem rdSupply_lend (s : Loc) (γ : StoreNames) :
    rdSupply (GF := GF) s γ ∗ £ 1 ∗ threadTok ∗ ownToks γ.tk 1 ⊢
      |={⊤}=> (storeReaderC s γ ∗ api.tokBack s γ) := by
  iintro ⟨#Hsup, Hlc, Htok, Htk⟩
  iunfold rdSupply at Hsup
  icases Hsup with ⟨%N, %γp, %R, #Hp, #Hw⟩
  imod threadPool.borrow_lc N γp R ⊤ (fun _ _ => CoPset.mem_full) $$ [$Hlc $Hp $Htok]
    with ⟨HR, Hloan⟩
  icases Hw $$ HR with ⟨Hsl, Hback⟩
  imodintro
  isplitl [Hsl Htk]
  · iapply (storeReaderC_split s γ).2; iframe Hsl Htk
  iunfold api.tokBack
  iintro Hrd
  icases (storeReaderC_split s γ).1 $$ Hrd with ⟨Hsl, Htk⟩
  ihave HR := Hback $$ Hsl
  imod threadPool.giveBack N γp R ⊤ (fun _ _ => CoPset.mem_full) $$ [$Hp $Hloan $HR] with Htok
  imodintro
  iframe Htok Htk

/-- **A reader under a later for a thread token and a ticket**, with their way back (`tokBack`),
without a later credit: `store.Read`/`store.Write` take the reader under a later (their first step
strips it). The slots go back into the pool under the later (the pool's invariant is). -/
theorem rdSupply_lendL (s : Loc) (γ : StoreNames) :
    rdSupply (GF := GF) s γ ∗ threadTok ∗ ownToks γ.tk 1 ⊢
      |={⊤}=> (▷ storeReaderC s γ ∗ api.tokBack s γ) := by
  iintro ⟨#Hsup, Htok, Htk⟩
  iunfold rdSupply at Hsup
  icases Hsup with ⟨%N, %γp, %R, #Hp, #Hw⟩
  imod threadPool.borrow N γp R ⊤ (fun _ _ => CoPset.mem_full) $$ [$Hp $Htok] with ⟨HR, Hloan⟩
  ihave HR : ▷ (storeSlots s γ ∗ (storeSlots s γ -∗ R)) $$ [HR]
  · inext; iapply Hw; iexact HR
  icases HR with ⟨Hsl, Hback⟩
  imodintro
  isplitl [Hsl Htk]
  · inext; iapply (storeReaderC_split s γ).2; iframe Hsl Htk
  iunfold api.tokBack
  iintro Hrd
  icases (storeReaderC_split s γ).1 $$ Hrd with ⟨Hsl, Htk⟩
  ihave HR : ▷ R $$ [Hback Hsl]
  · inext; iapply Hback; iexact Hsl
  iunfold threadPool.isThreadPool at Hp
  iunfold threadPool.ownThreadLoan at Hloan
  iinv Hp with Hi Hclose
  iunfold threadPool.poolInv at Hi
  icases Hi with ⟨%b, %m, >Hauth, >Htoks, HRs, >%Hle⟩
  icombine Hauth Hloan gives %Hb
  obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
  imod ownTokAuth_delete_S γp b' $$ Hauth Hloan with Hauth
  icases (threadToks_add b' 1).1 $$ Htoks with ⟨Htoks, Htok⟩
  imod Hclose $$ [Hauth Htoks HR HRs] with _
  · inext
    iunfold threadPool.poolInv
    iexists b', m + 1
    simp only [List.replicate]
    iframe
    ipureintro; omega
  imodintro
  iframe Htok Htk

/-- **A reader of the watchable store for a thread token and a ticket** (a stream's call of its
store, which lends it the whole `watchReader`), with their way back. -/
theorem watchReader_lend (s st : Loc) (γw : WsNames) (γp : GName) :
    £ 1 ∗ threadPool.isThreadPool (GF := GF) watchRdPoolN γp (watchSlots s st γw) ∗ threadTok ∗
      ownToks γw.st.tk 1 ⊢
      |={⊤}=> (watchReader s st γw ∗
        (watchReader s st γw ={⊤}=∗ threadTok ∗ ownToks γw.st.tk 1)) := by
  iintro ⟨Hlc, #Hp, Htok, Htk⟩
  imod threadPool.borrow_lc watchRdPoolN γp _ ⊤ (fun _ _ => CoPset.mem_full) $$ [$Hlc $Hp $Htok]
    with ⟨Hsl, Hloan⟩
  imodintro
  isplitl [Hsl Htk]
  · iapply (watchReader_split s st γw).2; iframe Hsl Htk
  iintro Hrd
  icases (watchReader_split s st γw).1 $$ Hrd with ⟨Hsl, Htk⟩
  imod threadPool.giveBack watchRdPoolN γp _ ⊤ (fun _ _ => CoPset.mem_full) $$ [$Hp $Hloan $Hsl]
    with Htok
  imodintro
  iframe Htok Htk

end proof

end mvcc
end EtcdGrove
end Perennial
