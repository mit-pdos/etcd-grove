/-
The peer streams' ghost vocabulary and protocol (`notes/stage1-plan.md`, "Connection roles",
"Delivery"), over the global ghost state:

* **Sent messages.** For each direction `f → t` (replica ids), the protocol messages `f` has
  sent to `t`, in order: an append-only list (a mono-list at `γ.rep.sent f t`) whose authority is
  split in two halves, `sentHalf γ f t ms`: one is the sender's framework's (in `fwLockInv`,
  under `r.M`, with the writer of that peer's stream), the other the protocol layer's (where it
  likes: its lock or its invariant). Appending needs both (`sentHalf_append`). The persistent
  index facts `msgSent γ f t k m` ("`m` is the `k`-th protocol message from `f` to `t`") are what
  the stream protocol carries; one message per position (`msgSent_agree`), and a half knows them
  all (`sentHalf_lookup`), so the protocol layer can relate the list to its model (every
  `msgSent` message is one its model sent, at that position).
* **How a sender gets `msgSent` for its next position**: `SendMsg` (`Epaxos/Interface/Replica.lean`)
  takes a *send update* `sendUpd γ f t m Ψ`: given the framework's half with list `ms` (the
  framework knows `ms` under `r.M`), it returns the half with `ms ++ [m]` (and `Ψ` to the caller);
  inside, the protocol layer combines it with its own half and appends (and records `m` as sent in
  its model). The simplest instance: the caller holds its half (`sendUpd_half`), e.g. in the
  instance lock's invariant, which every handler holds while it sends. The beacons
  (`SendBeacon`, `ReplyBeacon`, the framework's own) are not protocol messages: they take no
  position (`protoMsgs`) and need no update.
* **Delivery tokens.** `delivTok γ t f k` (exclusive): the right to deliver the `k`-th protocol
  message from `f` at `t`, once. Replica `t`'s reader goroutine for peer `f` mints them in order
  from `delivFrom γ t f n` (`delivFrom_mint`); the protocol layer's ghost step consumes them
  (its invariant keeps the tokens of what was delivered: at most once).
* **Dial tokens.** `dialTok γ d i` (exclusive, one-shot): replica `d`'s right to register one
  connection to replica `i`'s address as `peer d`; registering it (only for `i < d < nRep`: a
  replica dials the lower ids) leaves `peerConn γ d i cid` (persistent, agreeing, and carrying
  `i < d < nRep`): that connection is the only one with that role at that address, and the
  acceptor's classification (`id > r.Id && id < N`) accepts it as a peer.
* **Replica ids of addresses.** `addrId γ a i` (persistent): the final node list puts `a` at `i`
  (the master's write-once list; `listFinal_addrId` in `Epaxos/Interface/Replica.lean`).
* **The peer protocol** `peerStreamOk γ a d side cid bs` (used by `repDialP`/`repAccP`,
  `Epaxos/Interface/Client.lean`) for a connection whose role is `peer d` to the address `a` of
  replica `i`: written by the dialer (`side = false`): a prefix of `encId d` then whole messages
  `ws`, whose protocol messages are the `msgSent` ones from `d` to `i` at positions `0, 1, ...`
  (and the connection is `d`'s only one to `i`, `peerConn`); written by the acceptor
  (`side = true`): a prefix of whole messages whose protocol messages are the `msgSent` ones from
  `i` to `d`. Prefix-closed (`peerStreamOk_prefix`).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Interface.PeerWire
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Interface.Names
public import Perennial.Ghost.MonoList
public import Perennial.GooseLang.Countable
public import Perennial.Ghost.GhostVar
public import Perennial.Ghost.GhostMap
public import GooseLang.Ext.Net.Proto

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos

open Iris Iris.BI github_com.imdea_software.swiftpaxos_epaxos.kvs model

attribute [local instance] GooseGlobalGS.gooseInvGS

/-- The number of replicas (`NReplicas`). -/
def nRep : Nat := 5

section ghost
variable [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext]
variable {GF : BundledGFunctors} [G : GooseGlobalGS .hasLC GF]

/-! ## Sent messages -/

/-- `m` is the `k`-th protocol message replica `f` sent to replica `t` (persistent). -/
def msgSentDef (γ : EpNames) (f t k : Nat) (m : Msg) : IProp GF :=
  monoListIdxOwn (γ.rep.sent f t) k m

@[irreducible] def msgSent (γ : EpNames) (f t k : Nat) (m : Msg) : IProp GF :=
  msgSentDef γ f t k m

theorem msgSent_unseal : @msgSent = @msgSentDef := by funext; with_unfolding_all rfl

/-- Half of the authority of the list `ms` of protocol messages sent from `f` to `t`, with its
index facts. -/
def sentHalfDef (γ : EpNames) (f t : Nat) (ms : List Msg) : IProp GF :=
  monoListAuthOwn (γ.rep.sent f t) (1 : Qp).half ms

@[irreducible] def sentHalf (γ : EpNames) (f t : Nat) (ms : List Msg) : IProp GF :=
  sentHalfDef γ f t ms

theorem sentHalf_unseal : @sentHalf = @sentHalfDef := by funext; with_unfolding_all rfl

instance msgSent_persistent (γ : EpNames) (f t k : Nat) (m : Msg) :
    Persistent (msgSent (GF := GF) γ f t k m) := by
  rw [msgSent_unseal]; unfold msgSentDef; infer_instance
instance msgSent_timeless (γ : EpNames) (f t k : Nat) (m : Msg) :
    Timeless (msgSent (GF := GF) γ f t k m) := by
  rw [msgSent_unseal]; unfold msgSentDef; infer_instance
instance sentHalf_timeless (γ : EpNames) (f t : Nat) (ms : List Msg) :
    Timeless (sentHalf (GF := GF) γ f t ms) := by
  rw [sentHalf_unseal]; unfold sentHalfDef; infer_instance

/-- One message per position. -/
theorem msgSent_agree (γ : EpNames) (f t k : Nat) (m m' : Msg) :
    msgSent (GF := GF) γ f t k m -∗ msgSent γ f t k m' -∗ ⌜m = m'⌝ := by
  rw [msgSent_unseal]; unfold msgSentDef
  iintro H1 H2
  iapply mono_list_idx_agree $$ H1 H2

/-- The two halves agree. -/
theorem sentHalf_agree (γ : EpNames) (f t : Nat) (ms ms' : List Msg) :
    sentHalf (GF := GF) γ f t ms -∗ sentHalf γ f t ms' -∗ ⌜ms = ms'⌝ := by
  rw [sentHalf_unseal]; unfold sentHalfDef
  iintro H1 H2
  ihave %h := monoListAuthOwn_agree $$ H1 H2
  ipureintro; exact h.2

/-- A half knows the positions. -/
theorem sentHalf_lookup (γ : EpNames) (f t k : Nat) (ms : List Msg) (m : Msg) :
    sentHalf (GF := GF) γ f t ms -∗ msgSent γ f t k m -∗ ⌜ms[k]? = some m⌝ := by
  rw [sentHalf_unseal, msgSent_unseal]; unfold sentHalfDef msgSentDef
  iintro H1 #H2
  iapply mono_list_auth_idx_lookup $$ H1 H2

/-- A half gives the index facts of its list. -/
theorem sentHalf_msgSent (γ : EpNames) (f t k : Nat) (ms : List Msg) (m : Msg)
    (h : ms[k]? = some m) :
    sentHalf (GF := GF) γ f t ms ⊢ sentHalf γ f t ms ∗ msgSent γ f t k m := by
  rw [sentHalf_unseal, msgSent_unseal]; unfold sentHalfDef msgSentDef
  iintro H
  ihave #Hlb := monoListLbOwn_get $$ H
  iframe H
  iapply monoListIdxOwn_get k m h $$ Hlb

/-- The two halves of a mono-list of messages (package-internal helper). -/
private theorem monoListMsg_halves (γ : GName) (ms : List Msg) :
    monoListAuthOwn (GF := GF) γ 1 ms ⊣⊢
      monoListAuthOwn γ (1 : Qp).half ms ∗ monoListAuthOwn γ (1 : Qp).half ms := by
  have := (monoListAuthOwn_fractional (GF := GF) γ ms).fractional (1 : Qp).half (1 : Qp).half
  rwa [Qp.half_add_half] at this

/-- Both halves append a message (at position `ms.length`). -/
theorem sentHalf_append (γ : EpNames) (f t : Nat) (ms : List Msg) (m : Msg) :
    sentHalf (GF := GF) γ f t ms -∗ sentHalf γ f t ms ==∗
      sentHalf γ f t (ms ++ [m]) ∗ sentHalf γ f t (ms ++ [m]) := by
  rw [sentHalf_unseal]; unfold sentHalfDef
  iintro H1 H2
  ihave H := (monoListMsg_halves _ ms).2 $$ [H1 H2]
  · isplitl [H1]
    · iexact H1
    · iexact H2
  imod monoListAuthOwn_update_app [m] $$ H with ⟨H, -⟩
  imodintro
  iapply (monoListMsg_halves _ _).1 $$ H

/-- The send update a sender of `m` from `f` to `t` hands to `SendMsg`: from the framework's
half (list `ms`), the framework's half with `m` appended and `Ψ` for the caller (at `⊤`: the
framework runs it holding `r.M`, no invariant open). -/
def sendUpd (γ : EpNames) (f t : Nat) (m : Msg) (Ψ : IProp GF) : IProp GF :=
  iprop(∀ ms, sentHalf γ f t ms ={⊤}=∗ sentHalf γ f t (ms ++ [m]) ∗ Ψ)

/-- The simplest send update: the caller's own half (returned with `m` appended). -/
theorem sendUpd_half (γ : EpNames) (f t : Nat) (ms : List Msg) (m : Msg) :
    sentHalf (GF := GF) γ f t ms ⊢ sendUpd γ f t m (sentHalf γ f t (ms ++ [m])) := by
  unfold sendUpd
  iintro H %ms' H'
  ihave %Heq := sentHalf_agree $$ H H'
  subst Heq
  imod sentHalf_append $$ H H' with ⟨H, H'⟩
  imodintro
  iframe

/-! ## Delivery tokens -/

/-- The right to deliver, once, the `k`-th protocol message from `f` at `t` (exclusive). -/
def delivTokDef (γ : EpNames) (t f k : Nat) : IProp GF :=
  ghostMapElem (γ.rep.deliv t f) k (DFrac.own 1) ()

@[irreducible] def delivTok (γ : EpNames) (t f k : Nat) : IProp GF := delivTokDef γ t f k

theorem delivTok_unseal : @delivTok = @delivTokDef := by funext; with_unfolding_all rfl

/-- The right to mint the delivery tokens of the stream from `f` at `t` from position `n` on
(exclusive; the reader goroutine's). -/
def delivFromDef (γ : EpNames) (t f n : Nat) : IProp GF :=
  iprop(∃ M : GMap Nat Unit, ghostMapAuth (γ.rep.deliv t f) 1 M ∗
    ⌜∀ k, M.lookup k ≠ none → k < n⌝)

@[irreducible] def delivFrom (γ : EpNames) (t f n : Nat) : IProp GF := delivFromDef γ t f n

theorem delivFrom_unseal : @delivFrom = @delivFromDef := by funext; with_unfolding_all rfl

instance delivTok_timeless (γ : EpNames) (t f k : Nat) : Timeless (delivTok (GF := GF) γ t f k) := by
  rw [delivTok_unseal]; unfold delivTokDef; infer_instance
instance delivFrom_timeless (γ : EpNames) (t f n : Nat) : Timeless (delivFrom (GF := GF) γ t f n) := by
  rw [delivFrom_unseal]; unfold delivFromDef; infer_instance

theorem delivTok_excl (γ : EpNames) (t f k : Nat) :
    delivTok (GF := GF) γ t f k -∗ delivTok γ t f k -∗ False := by
  rw [delivTok_unseal]; unfold delivTokDef
  iintro H1 H2
  icases ghostMapElem_ne _ k k _ () () $$ H1 H2 with %Hne
  exact absurd rfl Hne

/-- Mint the next delivery token. -/
theorem delivFrom_mint (γ : EpNames) (t f n : Nat) :
    delivFrom (GF := GF) γ t f n ==∗ delivFrom γ t f (n + 1) ∗ delivTok γ t f n := by
  rw [delivFrom_unseal, delivTok_unseal]; unfold delivFromDef delivTokDef
  iintro ⟨%M, H, %HM⟩
  have hn : M.lookup n = none := by
    cases h : M.lookup n with
    | none => rfl
    | some _ => exact absurd (HM n (by simp [h])) (Nat.lt_irrefl n)
  imod ghost_map_insert n () hn $$ H with ⟨H, Ht⟩
  imodintro
  iframe Ht
  iexists M.insert n ()
  iframe H
  ipureintro
  intro k hk
  by_cases hkn : k = n
  · omega
  · have : (M.insert n ()).lookup k = M.lookup k := GMap.lookup_insert_ne M () (Ne.symm hkn)
    rw [this] at hk
    have := HM k hk; omega

/-! ## Dial tokens -/

/-- Replica `d`'s one-shot right to register a connection to replica `i`'s address as its peer
connection (exclusive). -/
def dialTokDef (γ : EpNames) (d i : Nat) : IProp GF :=
  dghostVar (γ.rep.dials d i) (DFrac.own 1) (none : Option Nat)

@[irreducible] def dialTok (γ : EpNames) (d i : Nat) : IProp GF := dialTokDef γ d i

theorem dialTok_unseal : @dialTok = @dialTokDef := by funext; with_unfolding_all rfl

/-- Connection `cid` is replica `d`'s (only) peer connection to replica `i`'s address, a lower
id (persistent). -/
def peerConnDef (γ : EpNames) (d i : Nat) (cid : Nat) : IProp GF :=
  iprop(dghostVar (γ.rep.dials d i) DFrac.discard (some cid) ∗ ⌜i < d ∧ d < nRep⌝)

@[irreducible] def peerConn (γ : EpNames) (d i : Nat) (cid : Nat) : IProp GF :=
  peerConnDef γ d i cid

theorem peerConn_unseal : @peerConn = @peerConnDef := by funext; with_unfolding_all rfl

instance peerConn_persistent (γ : EpNames) (d i : Nat) (cid : Nat) :
    Persistent (peerConn (GF := GF) γ d i cid) := by
  rw [peerConn_unseal]; unfold peerConnDef; infer_instance
instance peerConn_timeless (γ : EpNames) (d i : Nat) (cid : Nat) :
    Timeless (peerConn (GF := GF) γ d i cid) := by
  rw [peerConn_unseal]; unfold peerConnDef; infer_instance
instance dialTok_timeless (γ : EpNames) (d i : Nat) : Timeless (dialTok (GF := GF) γ d i) := by
  rw [dialTok_unseal]; unfold dialTokDef; infer_instance

/-- Use the dial token for connection `cid` (to a lower id). -/
theorem dialTok_use (γ : EpNames) (d i : Nat) (cid : Nat) :
    ⌜i < d ∧ d < nRep⌝ -∗ dialTok (GF := GF) γ d i ==∗ peerConn γ d i cid := by
  rw [dialTok_unseal, peerConn_unseal]; unfold dialTokDef peerConnDef
  iintro %Hids H
  imod dghostVar_update (some cid) $$ H with H
  imod dghostVar_persist $$ H with H
  imodintro
  iframe H
  ipureintro; exact Hids

/-- The ids of a peer connection. -/
theorem peerConn_ids (γ : EpNames) (d i : Nat) (cid : Nat) :
    peerConn (GF := GF) γ d i cid ⊢ ⌜i < d ∧ d < nRep⌝ := by
  rw [peerConn_unseal]; unfold peerConnDef
  iintro ⟨-, %H⟩
  ipureintro; exact H

/-- One peer connection per pair. -/
theorem peerConn_agree (γ : EpNames) (d i : Nat) (cid cid' : Nat) :
    peerConn (GF := GF) γ d i cid -∗ peerConn γ d i cid' -∗ ⌜cid = cid'⌝ := by
  rw [peerConn_unseal]; unfold peerConnDef
  iintro ⟨H1, -⟩ ⟨H2, -⟩
  ihave %H := dghostVar_agree $$ H1 H2
  ipureintro; exact Option.some.inj H

theorem dialTok_peerConn (γ : EpNames) (d i : Nat) (cid : Nat) :
    dialTok (GF := GF) γ d i -∗ peerConn γ d i cid -∗ False := by
  rw [peerConn_unseal, dialTok_unseal]; unfold dialTokDef peerConnDef
  iintro H1 ⟨H2, -⟩
  ihave %H := dghostVar_agree $$ H1 H2
  exact absurd H (by simp)

/-! ## Replica ids of addresses -/

/-- The final node list puts address `a` at index `i` (persistent; the list's elements are
distinct). -/
def addrIdDef (γ : EpNames) (a : GoString) (i : Nat) : IProp GF :=
  iprop(∃ L : List GoString, ghostMapElem γ.master.list () DFrac.discard L ∗
    ⌜L.Nodup ∧ L[i]? = some a⌝)

@[irreducible] def addrId (γ : EpNames) (a : GoString) (i : Nat) : IProp GF :=
  addrIdDef γ a i

theorem addrId_unseal : @addrId = @addrIdDef := by funext; with_unfolding_all rfl

instance addrId_persistent (γ : EpNames) (a : GoString) (i : Nat) :
    Persistent (addrId (GF := GF) γ a i) := by
  rw [addrId_unseal]; unfold addrIdDef; infer_instance
instance addrId_timeless (γ : EpNames) (a : GoString) (i : Nat) : Timeless (addrId (GF := GF) γ a i) := by
  rw [addrId_unseal]; unfold addrIdDef; infer_instance

theorem addrId_agree (γ : EpNames) (a : GoString) (i i' : Nat) :
    addrId (GF := GF) γ a i -∗ addrId γ a i' -∗ ⌜i = i'⌝ := by
  rw [addrId_unseal]; unfold addrIdDef
  iintro ⟨%L, H1, %HL⟩ ⟨%L', H2, %HL'⟩
  ihave %H := ghostMapElem_agree $$ H1 H2
  subst H
  ipureintro
  obtain ⟨hnd, hi⟩ := HL
  obtain ⟨-, hi'⟩ := HL'
  have hlt : i < L.length := (List.getElem?_eq_some_iff.mp hi).1
  exact (hnd.getElem?_inj hlt).mp (hi.trans hi'.symm)

/-! ## The ghost state, fresh -/

/-- Fresh resources `R i (g i)` for each of a list of distinct indices, from a fresh `R i b` for
each index (package-internal helper). -/
private theorem alloc_fun {B : Type} (b0 : B) (R : Nat → B → IProp GF)
    (h : ∀ i, ⊢ |==> ∃ b, R i b) : ∀ (l : List Nat), l.Nodup →
    ⊢ |==> ∃ g : Nat → B, [∗list] i ∈ l, R i (g i)
  | [], _ => by
    iapply bupd_intro
    iexists (fun _ => b0)
    iapply BigSepL.bigSepL_nil.2
    iempintro
  | a :: l, hl => by
    obtain ⟨ha, hl⟩ := List.nodup_cons.mp hl
    imod alloc_fun b0 R h l hl with ⟨%g, Hl⟩
    imod h a with ⟨%b, Ha⟩
    imodintro
    iexists (fun x => if x = a then b else g x)
    iapply BigSepL.bigSepL_cons.2
    isplitl [Ha]
    · simp only [ite_true]; iexact Ha
    · iapply BigSepL.bigSepL_mono (Φ := fun _ x => R x (g x)) ?_ $$ Hl
      intro k x hx
      have : x ≠ a := fun h => ha (h ▸ List.mem_of_getElem? hx)
      simp only [this, ite_false]
      exact .rfl

/-- The raw fresh ghost state of one direction `f → t` (package-internal helper): the two halves
of the empty sent list, the delivery map's authority, the dial variable. -/
private def netRaw (n : GName × GName × GName) : IProp GF :=
  iprop(monoListAuthOwn n.1 (1 : Qp).half ([] : List Msg) ∗
    monoListAuthOwn n.1 (1 : Qp).half ([] : List Msg) ∗
    ghostMapAuth n.2.1 1 (∅ : GMap Nat Unit) ∗ dghostVar n.2.2 (DFrac.own 1) (none : Option Nat))

private theorem netRaw_alloc : ⊢ |==> ∃ n, netRaw (GF := GF) n := by
  imod mono_list_own_alloc (GF := GF) ([] : List Msg) with ⟨%γ1, H1, -⟩
  imod ghost_map_alloc_empty (GF := GF) (K := Nat) (V := Unit) with ⟨%γ2, H2⟩
  imod dghostVar_alloc (GF := GF) (none : Option Nat) with ⟨%γ3, H3⟩
  imodintro
  iexists (γ1, γ2, γ3)
  unfold netRaw
  ihave ⟨H1, H1'⟩ := (monoListMsg_halves γ1 []).1 $$ H1
  iframe

/-- The peer streams' ghost state for `n` replicas, fresh: for every direction `f → t`, both
halves of the empty list, the minting right from 0 at `t`, and every dial token. -/
theorem net_alloc (n : Nat) :
    ⊢ |==> ∃ (sent deliv dials : Nat → Nat → GName), ∀ γ : EpNames,
      ⌜γ.rep.sent = sent ∧ γ.rep.deliv = deliv ∧ γ.rep.dials = dials⌝ -∗
        [∗list] f ∈ List.range n, [∗list] t ∈ List.range n,
          sentHalf (GF := GF) γ f t [] ∗ sentHalf γ f t [] ∗ delivFrom γ t f 0 ∗ dialTok γ f t := by
  have hrow : ∀ f : Nat, ⊢ |==> ∃ g : Nat → GName × GName × GName,
      [∗list] t ∈ List.range n, netRaw (g t) := fun _ =>
    alloc_fun (0, 0, 0) (fun _ b => netRaw (GF := GF) b) (fun _ => netRaw_alloc) _ List.nodup_range
  imod alloc_fun (fun _ => (0, 0, 0)) (fun _ g => iprop([∗list] t ∈ List.range n, netRaw (g t)))
    hrow (List.range n) List.nodup_range with ⟨%G, H⟩
  imodintro
  iexists (fun f t => (G f t).1), (fun t f => (G f t).2.1), (fun f t => (G f t).2.2)
  iintro %γ %Hγ
  obtain ⟨Hs, Hd, Hx⟩ := Hγ
  iapply BigSepL.bigSepL_mono ?_ $$ H
  intro _ f _
  apply BigSepL.bigSepL_mono
  intro _ t _
  rw [sentHalf_unseal, delivFrom_unseal, dialTok_unseal]
  unfold sentHalfDef delivFromDef dialTokDef netRaw
  rw [Hs, Hd, Hx]
  iintro ⟨H1, H2, H3, H4⟩
  iframe
  ipureintro
  intro k hk; exact absurd rfl hk

/-- The replicas' client-writer and reply-token maps for `n` replicas, fresh: for each replica
`i`, both maps' (empty) authorities. -/
theorem fw_alloc (n : Nat) :
    ⊢ |==> ∃ (cw rp : Nat → GName), ∀ γ : EpNames, ⌜γ.rep.cwriters = cw ∧ γ.rep.replies = rp⌝ -∗
      [∗list] i ∈ List.range n, ghostMapAuth (γ.rep.cwriters i) 1 (∅ : GMap Loc Nat) ∗
        ghostMapAuth (γ.rep.replies i) 1 (∅ : GMap Loc Unit) := by
  have h1 : ∀ _ : Nat, ⊢ |==> ∃ g : GName × GName,
      iprop(ghostMapAuth g.1 1 (∅ : GMap Loc Nat) ∗ ghostMapAuth g.2 1 (∅ : GMap Loc Unit)) :=
    fun _ => by
      imod ghost_map_alloc_empty (GF := GF) (K := Loc) (V := Nat) with ⟨%g1, H1⟩
      imod ghost_map_alloc_empty (GF := GF) (K := Loc) (V := Unit) with ⟨%g2, H2⟩
      imodintro
      iexists (g1, g2)
      iframe
  imod alloc_fun (0, 0) (fun _ g => iprop(ghostMapAuth g.1 1 (∅ : GMap Loc Nat) ∗
      ghostMapAuth g.2 1 (∅ : GMap Loc Unit))) h1 (List.range n) List.nodup_range with ⟨%G, H⟩
  imodintro
  iexists (fun i => (G i).1), (fun i => (G i).2)
  iintro %γ %Hγ
  obtain ⟨Hc, Hr⟩ := Hγ
  rw [Hc, Hr]
  iexact H

/-! ## The peer protocol -/

/-- The direction of a stream of a `peer d` connection to replica `i`'s address: the dialer's
(`side = false`) goes from `d` to `i`, the acceptor's from `i` to `d`. -/
def streamDir (d i : Nat) (side : Bool) : Nat × Nat := if side then (i, d) else (d, i)

/-- The header of a stream: the dialer's id handshake (dialer's side only). -/
def streamHdr (d : Nat) (side : Bool) : List w8 := if side then [] else encId d

/-- The bytes `bs` written on the stream of connection `cid` (role `peer d`, to address `a`) by
the dialer (`side = false`) or the acceptor (`side = true`): see the file header. -/
def peerStreamOk (γ : EpNames) (a : GoString) (d : w64) (side : Bool) (cid : Nat)
    (bs : List w8) : IProp GF :=
  iprop(∃ (i : Nat) (ws : List Msg), addrId γ a i ∗
    (if side then iprop(True) else peerConn γ (uint.nat d) i cid) ∗
    ⌜(∀ m ∈ ws, m.wf) ∧ bs <+: streamHdr (uint.nat d) side ++ ws.flatMap encMsg⌝ ∗
    [∗list] k ↦ m ∈ protoMsgs ws,
      msgSent γ (streamDir (uint.nat d) i side).1 (streamDir (uint.nat d) i side).2 k m)

instance peerStreamOk_timeless (γ : EpNames) (a : GoString) (d : w64) (side : Bool) (cid : Nat)
    (bs : List w8) : Timeless (peerStreamOk (GF := GF) γ a d side cid bs) := by
  unfold peerStreamOk; cases side <;> simp only [ite_true, ite_false, Bool.false_eq_true] <;> infer_instance

instance peerStreamOk_persistent (γ : EpNames) (a : GoString) (d : w64) (side : Bool)
    (cid : Nat) (bs : List w8) : Persistent (peerStreamOk (GF := GF) γ a d side cid bs) := by
  unfold peerStreamOk; cases side <;> simp only [ite_true, ite_false, Bool.false_eq_true] <;> infer_instance

/-- The peer protocol is prefix-closed. -/
theorem peerStreamOk_prefix (γ : EpNames) (a : GoString) (d : w64) (side : Bool) (cid : Nat)
    (x y : List w8) :
    peerStreamOk (GF := GF) γ a d side cid (x ++ y) ⊢ peerStreamOk γ a d side cid x := by
  unfold peerStreamOk
  iintro ⟨%i, %ws, #Ha, Hc, %Hp, Hs⟩
  iexists i, ws
  iframe Ha Hc Hs
  ipureintro
  exact ⟨Hp.1, (List.prefix_append x y).trans Hp.2⟩

private theorem protoMsgs_snoc (ws : List Msg) (m : Msg) :
    protoMsgs (ws ++ [m]) = protoMsgs ws ++ (if m.isProto then [m] else []) := by
  unfold protoMsgs; rw [List.filter_append]; cases h : m.isProto <;> simp [List.filter, h]

/-- A writer's step: from whole messages `ws` (`msgSent` for the protocol ones), appending a
beacon or the next protocol message `m` with its `msgSent` fact at position
`(protoMsgs ws).length` keeps the stream allowed. -/
theorem peerStreamOk_snoc (γ : EpNames) (a : GoString) (d : w64) (side : Bool) (cid : Nat)
    (i : Nat) (ws : List Msg) (m : Msg) (hwf : m.wf) :
    addrId (GF := GF) γ a i -∗
    (if side then iprop(True) else peerConn γ (uint.nat d) i cid) -∗
    ⌜∀ m ∈ ws, m.wf⌝ -∗
    ([∗list] k ↦ m ∈ protoMsgs ws,
      msgSent γ (streamDir (uint.nat d) i side).1 (streamDir (uint.nat d) i side).2 k m) -∗
    (if m.isProto then msgSent γ (streamDir (uint.nat d) i side).1
      (streamDir (uint.nat d) i side).2 (protoMsgs ws).length m else iprop(True)) -∗
    peerStreamOk γ a d side cid (streamHdr (uint.nat d) side ++ (ws ++ [m]).flatMap encMsg) := by
  unfold peerStreamOk
  iintro #Ha Hc %Hws Hs Hm
  iexists i, ws ++ [m]
  iframe Ha Hc
  isplitr
  · ipureintro
    refine ⟨?_, List.prefix_refl _⟩
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact Hws x hx
    · simp at hx; subst hx; exact hwf
  rw [protoMsgs_snoc]
  cases hp : m.isProto
  · simp only [hp, Bool.false_eq_true, ite_false, List.append_nil]
    iexact Hs
  · simp only [hp, ite_true]
    iapply (BigSepL.bigSepL_snoc).2
    iframe

/-- A reader's step: what was read so far is the header, whole messages `ws` and then a prefix
of the next message's encoding. If a whole next message `m` was read, it is the `k`-th protocol
message of the stream, with `k = (protoMsgs ws).length`, and its `msgSent` fact is known. -/
theorem peerStreamOk_next (γ : EpNames) (a : GoString) (d : w64) (side : Bool) (cid : Nat)
    (ws : List Msg) (m : Msg) (hwf : ∀ m ∈ ws, m.wf) (hm : m.wf) :
    peerStreamOk (GF := GF) γ a d side cid (streamHdr (uint.nat d) side ++ (ws ++ [m]).flatMap encMsg) ⊢
      ∃ i : Nat, addrId γ a i ∗
        (if m.isProto then msgSent γ (streamDir (uint.nat d) i side).1
          (streamDir (uint.nat d) i side).2 (protoMsgs ws).length m else iprop(True)) := by
  unfold peerStreamOk
  iintro ⟨%i, %ws', #Ha, -, %Hp, #Hs⟩
  iexists i
  iframe Ha
  obtain ⟨hwf', hpre⟩ := Hp
  -- the bytes read are whole messages `ws ++ [m]`, so `ws ++ [m]` is a prefix of `ws'`
  have hpre' : (ws ++ [m]).flatMap encMsg <+: ws'.flatMap encMsg :=
    (List.prefix_append_right_inj _).mp hpre
  obtain ⟨rest, hrest⟩ := hpre'
  have hwfa : ∀ x ∈ ws ++ [m], x.wf := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact hwf x hx
    · simp at hx; subst hx; exact hm
  have hws : ws ++ [m] <+: ws' := by
    rcases encMsg_prefix_inj (ws ++ [m]) ws' rest [] hwfa hwf' (by simpa using hrest) with h | h
    · exact h
    · obtain ⟨t, ht⟩ := h
      rw [← ht, List.flatMap_append, List.append_assoc] at hrest
      have h0 : t.flatMap encMsg ++ rest = [] := by
        have := congrArg List.length hrest
        simp only [List.length_append] at this
        exact List.eq_nil_of_length_eq_zero (by simp only [List.length_append]; omega)
      have ht0 : t = [] := by
        cases t with
        | nil => rfl
        | cons x t => simp [encMsg] at h0
      subst ht0; simp at ht; rw [ht]; exact List.prefix_refl _
  have hpp : protoMsgs (ws ++ [m]) <+: protoMsgs ws' := List.IsPrefix.filter _ hws
  rw [protoMsgs_snoc] at hpp
  cases hp : m.isProto
  · simp only [hp, Bool.false_eq_true, ite_false]
    itrivial
  · simp only [hp, ite_true] at hpp ⊢
    have hlk : (protoMsgs ws')[(protoMsgs ws).length]? = some m := by
      obtain ⟨u, hu⟩ := hpp
      rw [← hu]; simp
    iapply (BigSepL.bigSepL_lookup hlk) $$ Hs

end ghost

end Perennial.github_com.imdea_software.swiftpaxos_epaxos
