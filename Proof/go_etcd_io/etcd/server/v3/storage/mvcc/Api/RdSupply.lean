/-
**The store handle's readers' supply** (track A, request 3, 2026-11-06; `notes/mvcc-api-invariants.md`,
"M4, track A, request 3"; the reader tokens, 2026-11-06, `notes/decisions.md`, "mvcc's API: the
store's readers as client-held tokens"). Lean-first (no Rocq counterpart). `Api.lean` imports it
non-publicly: its `isMvccPlain` holds a `rdSupply`.

A reader of the store (`storeReaderC`) is its locks' slots (`storeSlots`: a reader slot of each of
`s.mu` and `s.revMu`) and a ticket of the readers' pool (`ownToks γ.tk 1`), the right to borrow one
of the backend's reader slots the pool holds at the current storage. (2026-11-07, `notes/decisions.md`,
"mvcc's reader token carries the store's lock slots") The client's reader token (`ownToks γ.api.rdk
1`, the API's `mvccReaders γ 1`) is the right to a whole reader: the handle's pool (`rdkPool`) holds,
for each token out, its locks' slots (and, of a watchable store, its `s.mu` slot) and its ticket. No
thread token: the store's locks have a reader slot for each token. A client holding all the tokens
knows no read is in flight.

* `rdkPool`: the pool (`rdkPool_init`, `_borrow[L]`, `_giveBack`, `_take`: the census).
* `rdSupply`: a pool whose copies each lend the store's locks' slots and take them back. A plain
  store's pool is of `storeSlots` itself; a watchable store's inner store's is the watchable
  store's pool of `watchSlots` (with the watchable store's `s.mu` slot, kept in the wand), so the two
  handles share one pool.
* `rdSupply_init`: a readers' supply from `n` readers of the store, `n` tokens;
  `rdSupply_watch`: the inner store's supply from the watchable store's pool.
* `rdSupply_lend`: a reader of the store for a token, with its way back (`tokBack`); the slots are
  not timeless (their locks' guards hold invariants), so the borrow costs a later credit
  (`rdSupply_lendL`: under a later instead). `watchReader_lend`: the same of the watchable store's
  pool, a whole `watchReader` (a stream's calls of its store).
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

/-- The readers' pool's namespace. -/
def rdkPoolN : Namespace := (nroot .@ "mvcc") .@ "rdkPool"

/-- **The readers' pool of the client's reader tokens** (the reader token carries the store's lock
slots, 2026-11-07): for each of the `k` reader tokens out (`ownToks γ.api.rdk`, the API's
`mvccReaders`; the authority here counts them exactly), a copy of `R` (a reader's lock slots) and a
ticket of the store's readers' pool (`ownToks γ.tk`, kept together: timeless). A token is the right
to one copy and one ticket, without a thread token: the store's locks have a reader slot for each
token, so their number is not the threads'. -/
def rdkPool (γ : StoreNames) (R : IProp GF) : IProp GF :=
  inv rdkPoolN iprop(∃ k : Nat, ownTokAuth γ.api.rdk k ∗ ownToks γ.tk k ∗
    [∗list] _x ∈ List.replicate k (), R)

instance rdkPool_persistent (γ : StoreNames) (R : IProp GF) :
    Persistent (rdkPool (GF := GF) γ R) := by
  unfold rdkPool; infer_instance

theorem rdkPool_withPhys (γ : StoreNames) (p : PhysNames) (R : IProp GF) :
    rdkPool (GF := GF) (γ.withPhys p) R = rdkPool γ R := rfl

/-- A pool from `n` copies of `R` and `n` tickets, at the tokens' authority at none: the `n` tokens. -/
theorem rdkPool_init (γ : StoreNames) (R : IProp GF) (n : Nat) :
    ownTokAuth (GF := GF) γ.api.rdk 0 ∗ ownToks γ.tk n ∗ ([∗list] _x ∈ List.replicate n (), R) ⊢
      |={⊤}=> rdkPool γ R ∗ ownToks γ.api.rdk n := by
  iintro ⟨Hauth, Htk, HR⟩
  imod ownTokAuth_add n γ.api.rdk 0 $$ Hauth with ⟨Hauth, Htoks⟩
  rw [Nat.zero_add]
  imod inv_alloc rdkPoolN ⊤ iprop(∃ k : Nat, ownTokAuth γ.api.rdk k ∗ ownToks γ.tk k ∗
      [∗list] _x ∈ List.replicate k (), R) $$ [Hauth Htk HR] with #Hinv
  · inext
    iexists n
    iframe
  imodintro
  iframe Htoks
  iunfold rdkPool
  iexact Hinv

/-- **A copy and a ticket under a later for a token.** -/
theorem rdkPool_borrowL (γ : StoreNames) (R : IProp GF) :
    rdkPool (GF := GF) γ R ∗ ownToks γ.api.rdk 1 ⊢ |={⊤}=> ▷ R ∗ ownToks γ.tk 1 := by
  iintro ⟨#Hinv, Hrk⟩
  iunfold rdkPool at Hinv
  iinv Hinv with Hi Hclose
  icases Hi with ⟨%k, >Hauth, >Htk, HRs⟩
  icombine Hauth Hrk gives %Hk
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  imod ownTokAuth_delete_S γ.api.rdk k' $$ Hauth Hrk with Hauth
  icases (ownToks_add 1 k' γ.tk).1 $$ Htk with ⟨Htk, Htk1⟩
  simp only [List.replicate]
  icases HRs with ⟨HR, HRs⟩
  imod Hclose $$ [Hauth Htk HRs] with _
  · inext
    iexists k'
    iframe
  imodintro
  iframe HR Htk1

/-- **A copy and a ticket for a token and a later credit.** -/
theorem rdkPool_borrow (γ : StoreNames) (R : IProp GF) :
    rdkPool (GF := GF) γ R ∗ £ 1 ∗ ownToks γ.api.rdk 1 ⊢ |={⊤}=> R ∗ ownToks γ.tk 1 := by
  iintro ⟨#Hinv, Hlc, Hrk⟩
  imod rdkPool_borrowL γ R $$ [Hinv Hrk] with ⟨HR, Htk⟩
  · iframe Hinv Hrk
  imod (lc_fupd_elim_later (E := ⊤) (P := R)) $$ Hlc HR with HR
  imodintro
  iframe HR Htk

/-- **A copy (under a later) and a ticket back, for the token.** -/
theorem rdkPool_giveBack (γ : StoreNames) (R : IProp GF) :
    rdkPool (GF := GF) γ R ∗ ▷ R ∗ ownToks γ.tk 1 ⊢ |={⊤}=> ownToks γ.api.rdk 1 := by
  iintro ⟨#Hinv, HR, Htk1⟩
  iunfold rdkPool at Hinv
  iinv Hinv with Hi Hclose
  icases Hi with ⟨%k, >Hauth, >Htk, HRs⟩
  imod ownTokAuth_S γ.api.rdk k $$ Hauth with ⟨Hauth, Hrk⟩
  imod Hclose $$ [Hauth Htk Htk1 HR HRs] with _
  · inext
    iexists k + 1
    iframe Hauth
    isplitl [Htk Htk1]
    · iapply (ownToks_add 1 k γ.tk).2; iframe Htk Htk1
    rw [List.replicate_succ]
    iapply BigSepL.bigSepL_cons.2
    iframe HR HRs
  imodintro
  iexact Hrk

/-- **The tickets of `n` tokens, for good** (`mvccClosed_rest.law`'s census: the copies, the locks'
slots, are left in the pool). -/
theorem rdkPool_take (γ : StoreNames) (R : IProp GF) (n : Nat) :
    rdkPool (GF := GF) γ R ∗ ownToks γ.api.rdk n ⊢ |={⊤}=> ownToks γ.tk n := by
  iintro ⟨#Hinv, Hrk⟩
  iunfold rdkPool at Hinv
  iinv Hinv with Hi Hclose
  icases Hi with ⟨%k, >Hauth, >Htk, HRs⟩
  icombine Hauth Hrk gives %Hk
  imod ownTokAuth_sub n γ.api.rdk k $$ Hauth Hrk with Hauth
  obtain ⟨j, rfl⟩ : ∃ j, k = j + n := ⟨k - n, by omega⟩
  icases (ownToks_add n j γ.tk).1 $$ Htk with ⟨Htk, Htkn⟩
  rw [show List.replicate (j + n) () = List.replicate j () ++ List.replicate n () from
    List.replicate_append_replicate.symm]
  ihave HRs : ▷ ([∗list] _x ∈ List.replicate j (), R) $$ [HRs]
  · inext
    icases BigSepL.bigSepL_append.1 $$ HRs with ⟨HRs, -⟩
    iexact HRs
  imod Hclose $$ [Hauth Htk HRs] with _
  · inext
    iexists j
    rw [Nat.add_sub_cancel]
    iframe
  imodintro
  iexact Htkn

/-- **The store's readers' supply** (see the header). -/
def rdSupply (s : Loc) (γ : StoreNames) : IProp GF :=
  iprop(∃ R : IProp GF, rdkPool γ R ∗ □ (R -∗ storeSlots s γ ∗ (storeSlots s γ -∗ R)))

instance rdSupply_persistent (s : Loc) (γ : StoreNames) :
    Persistent (rdSupply (GF := GF) s γ) := by
  unfold rdSupply; infer_instance

/-- **A plain store's readers' supply**, from `n` of its readers, at the tokens' authority at none:
`n` reader tokens. -/
theorem rdSupply_init (s : Loc) (γ : StoreNames) (n : Nat) :
    ownTokAuth (GF := GF) γ.api.rdk 0 ∗
      ([∗list] _x ∈ List.replicate n (), storeReaderC (GF := GF) s γ) ⊢ |={⊤}=> (
      rdSupply s γ ∗ ownToks γ.api.rdk n) := by
  iintro ⟨Ha, H⟩
  imod storeReaders_split s γ n $$ H with ⟨H, Ht⟩
  imod rdkPool_init γ (storeSlots (GF := GF) s γ) n $$ [Ha Ht H] with ⟨#Hp, Hrk⟩
  · iframe Ha Ht H
  imodintro
  iframe Hrk
  iunfold rdSupply
  iexists storeSlots s γ
  iframe Hp
  iintro !> HR
  iframe HR
  iintro HR; iexact HR

/-- **The inner store's readers' supply is the watchable store's pool** (each `watchSlots` lends
its inner store's slots, the watchable store's lock slot kept in the wand). -/
theorem rdSupply_watch (s st : Loc) (γw : WsNames) :
    rdkPool (GF := GF) γw.st (watchSlots s st γw) ⊢ rdSupply st γw.st := by
  iintro #Hp
  iunfold rdSupply
  iexists watchSlots s st γw
  iframe Hp
  iintro !> HR
  iunfold watchSlots at HR
  icases HR with ⟨HR, Hmu⟩
  iframe HR
  iintro HR
  iunfold watchSlots
  iframe Hmu HR

/-- **A reader for a reader token**, with its way back (`tokBack`). -/
theorem rdSupply_lend (s : Loc) (γ : StoreNames) :
    rdSupply (GF := GF) s γ ∗ £ 1 ∗ ownToks γ.api.rdk 1 ⊢
      |={⊤}=> (storeReaderC s γ ∗ api.tokBack s γ) := by
  iintro ⟨#Hsup, Hlc, Hrk⟩
  iunfold rdSupply at Hsup
  icases Hsup with ⟨%R, #Hp, #Hw⟩
  imod rdkPool_borrow γ R $$ [Hp Hlc Hrk] with ⟨HR, Htk⟩
  · iframe Hp Hlc Hrk
  icases Hw $$ HR with ⟨Hsl, Hback⟩
  imodintro
  isplitl [Hsl Htk]
  · iapply (storeReaderC_split s γ).2; iframe Hsl Htk
  iunfold api.tokBack
  iintro Hrd
  icases (storeReaderC_split s γ).1 $$ Hrd with ⟨Hsl, Htk⟩
  ihave HR := Hback $$ Hsl
  iapply rdkPool_giveBack γ R
  iframe Hp HR Htk

/-- **A reader under a later for a reader token**, with its way back (`tokBack`), without a later
credit: `store.Read`/`store.Write` take the reader under a later (their first step strips it). -/
theorem rdSupply_lendL (s : Loc) (γ : StoreNames) :
    rdSupply (GF := GF) s γ ∗ ownToks γ.api.rdk 1 ⊢
      |={⊤}=> (▷ storeReaderC s γ ∗ api.tokBack s γ) := by
  iintro ⟨#Hsup, Hrk⟩
  iunfold rdSupply at Hsup
  icases Hsup with ⟨%R, #Hp, #Hw⟩
  imod rdkPool_borrowL γ R $$ [Hp Hrk] with ⟨HR, Htk⟩
  · iframe Hp Hrk
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
  iapply rdkPool_giveBack γ R
  iframe Hp HR Htk

/-- **A reader of the watchable store for a reader token** (a stream's call of its store, which
lends it the whole `watchReader`), with its way back. -/
theorem watchReader_lend (s st : Loc) (γw : WsNames) :
    £ 1 ∗ rdkPool (GF := GF) γw.st (watchSlots s st γw) ∗ ownToks γw.st.api.rdk 1 ⊢
      |={⊤}=> (watchReader s st γw ∗
        (watchReader s st γw ={⊤}=∗ ownToks γw.st.api.rdk 1)) := by
  iintro ⟨Hlc, #Hp, Hrk⟩
  imod rdkPool_borrow γw.st _ $$ [Hp Hlc Hrk] with ⟨Hsl, Htk⟩
  · iframe Hp Hlc Hrk
  imodintro
  isplitl [Hsl Htk]
  · iapply (watchReader_split s st γw).2; iframe Hsl Htk
  iintro Hrd
  icases (watchReader_split s st γw).1 $$ Hrd with ⟨Hsl, Htk⟩
  iapply rdkPool_giveBack γw.st _
  iframe Hp Hsl Htk

end proof

end mvcc
end EtcdGrove
end Perennial
