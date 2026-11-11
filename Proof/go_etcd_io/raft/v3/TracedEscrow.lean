/-
Lean-first (no Rocq counterpart). **Probe B of the trace-check design** (2026-11-11,
`notes/trace-check-design.md` §8, `notes/decisions.md`, "Probe B (the escrow)"): the per-node token
escrow `rtkInv` (§3.2 items 2-4) as real definitions, and the lemmas the gated `node.run` and the
traced `node.Advance` will call, each arm's step given its loop resource:

- the `readyc` commit (`readyc_send_rtk`): the key allocated in the `|={⊤}=>` prefix of `run`'s send
  AU (`handshake_send_au_fupd`), the driver's claim into the payload;
- the deposit after `acceptReady` (`rtk_deposit`);
- the `advancec` rendezvous in both orders, over a channel protocol carrying only the escrow's part of
  `advInv` (`escInv`; the real `advInv` gains these payloads beside its own): `run`'s receive
  (`esc_recv_au`) and the driver's send (`esc_send_au`), each opening `rtkInv` inside the channel's
  invariant (`rtkN_sub_advN`); a claim-less driver (`ms = []`) and a stale claim (`rtk_scenario`);
- `stepIn`'s traced split into the gated `fwdP`/`netP` clauses and the `recvc` arm's premises of
  `raft.Step.tracedTriple` (`trTokR_fwd`, `trTokR_net`, `netGate_step`).

**Departure from the design (the probe's first finding).** The design's `run`-side token was an
exclusive `np` with a Boolean `pend` in the invariant. With it `run` cannot do its deposit: holding
nothing of the escrow after the commit, it can neither learn that a deposit is pending nor which
messages the pending key's slot records. Here `np` and `pend` are one agreement variable in halves,
`pk : Option (List QMsg)` (`rtkRun`): the invariant holds one half, `run` the other (lent at the
`RcvPending` rendezvous as `np` was), `some ms` while key `a - 1`'s tokens, for `ms`, are not yet in.
Raft-internal, not on `etc/api/raft.txt`; not yet threaded into `isNodeChan` (which sits below
`TrNetTy`'s module: `TrNetTy` moves down at threading).
-/
module

public import Proof.go_etcd_io.raft.v3.InvNodeRun
public import Proof.go_etcd_io.raft.v3.TracedRawNode
public import Proof.go_etcd_io.raft.v3.TracedNodeApi
import all Proof.go_etcd_io.raft.v3.TracedNodeApi

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section countable
variable [GooseExts]

/-- A message's scalars (the escrow's slots record messages). -/
instance messageM_countable : Pos.Countable MessageM :=
  countableOfLeftInverse
    (fun m : MessageM => (m.Type', m.To', m.From', m.Term', m.LogTerm', m.Index', m.Commit', m.Vote',
      m.Reject', m.RejectHint'))
    (fun p => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2.1, p.2.2.2.2.2.1, p.2.2.2.2.2.2.1,
      p.2.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2.2.2⟩) (fun _ => rfl)

instance msgSt_countable : Pos.Countable MsgSt :=
  countableOfLeftInverse (fun s : MsgSt => (s.msg, s.ents, s.snap, s.ctx, s.resps))
    (fun p => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2⟩) (fun _ => rfl)

instance qMsg_countable : Pos.Countable QMsg :=
  countableOfLeftInverse (fun q : QMsg => (q.loc, q.st)) (fun p => ⟨p.1, p.2⟩) (fun _ => rfl)

end countable

section pure
variable [GooseExts]

/-- **The types a traced node hands out** (§3.6): a traced network type, or a forwarded proposal of
normal entries. -/
def TrSent (st : MsgSt) : Prop :=
  TrNetTy st.msg.Type' ∨ (st.msg.Type' = MsgProp ∧ ∀ e ∈ st.ents, e.Type' = EntryNormal)

/-- The escrow's namespace (§3.2 item 2, revision 3's S1). -/
def rtkN : Namespace := nroot.@"raft_rtk"

theorem rtkN_sub_advN : (↑rtkN : CoPset) ⊆ ⊤ \ ↑advN := fun p hp => by
  rw [Iris.Std.LawfulSet.mem_diff]
  exact ⟨CoPset.mem_full, fun h => ndot_ne_disjoint nroot (by decide) p ⟨hp, h⟩⟩

/-- The escrow's ghost names (at threading: fields of `NodeNames`). -/
structure RtkNames where
  /-- the keys: a ghost map `Nat ↦ List QMsg`, each `Ready`'s handed-out messages -/
  rtk : GName
  /-- `run`'s pending deposit, in halves (the invariant's and `run`'s): replaces the design's `np`
  and `pend` -/
  pk : GName
  /-- the keys deposited, a monotone count -/
  dep : GName
  /-- the keys allocated, a monotone count (revision 2's A1) -/
  al : GName

/-- The keys deposited: all allocated, but the pending one. -/
def depCount (L : List (List QMsg)) (p : Option (List QMsg)) : Nat :=
  match p with
  | none => L.length
  | some _ => L.length - 1

end pure

section escrow
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- **A handed-out message's token, as the driver holds it** (§3.1's `trTok` body over a
`RaftNames`): untraced nothing; traced, its type handed-out (`TrSent`) and the receiver's token. -/
def trTokR (ρ : RaftNames) (st : MsgSt) : IProp GF :=
  match ρ.reTrace with
  | none => iprop(True)
  | some γd => iprop(⌜TrSent st⌝ ∗ recvTokOf γd st.msg st.ents st.ctx)

/-- The driver's escrowed token is today's client token (`trTok`, without `TrSent`), at a cluster
whose trace is the node's (`NodeOk γ γn` gives `γn.raft = γ.raft`, `InvApi.lean`). -/
theorem trTokR_trTok (ρ : RaftNames) (γ : Cluster) (st : MsgSt) (h : Cluster.trace γ = ρ.reTrace) :
    trTokR (GF := GF) ρ st ⊢ trTok γ st := by
  unfold trTokR trTok
  rw [h]
  cases ρ.reTrace with
  | none => iintro _; itrivial
  | some γd => iintro ⟨_, H⟩; iexact H

/-- `acceptReady`'s token (`readyTok`), with its type handed out (`TrSent`: step 3's `rnTrace` 1(b)
with `XfOk`'s clause), is the escrow's. -/
theorem readyTok_trTokR (ρ : RaftNames) (st : MsgSt) (h : TrSent st) :
    readyTok (GF := GF) ρ st ⊢ trTokR ρ st := by
  unfold readyTok trTokR
  rcases ρ.reTrace with _ | γd
  · iintro _; itrivial
  · dsimp only
    iintro H; iframe H; ipureintro; exact h

/-- A key's slot: below the deposited count, the tokens, or the driver's element swapped in. -/
def rtkSlot (ρ : RaftNames) (γe : RtkNames) (dc j : Nat) (ms : List QMsg) : IProp GF :=
  iprop(⌜j < dc⌝ -∗ (([∗list] q ∈ ms, trTokR ρ q.st) ∨ ghostMapElem γe.rtk j (DFrac.own 1) ms))

/-- **The escrow's body** (§3.2 item 2, with `pk` for `np`/`pend`): the keys `L` (key `j` at
position `j`), the pending deposit `p` (the last key's), the counts, the slots. -/
def rtkBody (ρ : RaftNames) (γe : RtkNames) : IProp GF :=
  iprop(∃ (L : List (List QMsg)) (M : GMap Nat (List QMsg)) (p : Option (List QMsg)),
    ghostMapAuth γe.rtk 1 M ∗ ⌜∀ j, M.lookup j = L[j]?⌝ ∗
    dghostVar γe.pk (DFrac.own (1 : Qp).half) p ∗
    ⌜∀ ms, p = some ms → L.getLast? = some ms⌝ ∗
    monoNatAuthOwn γe.al 1 L.length ∗
    monoNatAuthOwn γe.dep 1 (depCount L p) ∗
    [∗list] j ↦ ms ∈ L, rtkSlot ρ γe (depCount L p) j ms)

instance recvTokOf_timeless (γd : GName) (m : MessageM) (ents : List EntryM) (ctx : List w8) :
    Timeless (recvTokOf (GF := GF) γd m ents ctx) := by
  unfold recvTokOf TraceSim.traceDir TraceSim.inFlight; infer_instance

instance trTokR_timeless (ρ : RaftNames) (st : MsgSt) : Timeless (trTokR (GF := GF) ρ st) := by
  unfold trTokR; cases ρ.reTrace <;> dsimp only <;> infer_instance

instance rtkSlot_timeless (ρ : RaftNames) (γe : RtkNames) (dc j : Nat) (ms : List QMsg) :
    Timeless (rtkSlot (GF := GF) ρ γe dc j ms) := by
  unfold rtkSlot; infer_instance

instance rtkBody_timeless (ρ : RaftNames) (γe : RtkNames) : Timeless (rtkBody (GF := GF) ρ γe) := by
  unfold rtkBody; infer_instance

/-- **The escrow** (persistent; in `isNodeChan` at threading). -/
def rtkInv (ρ : RaftNames) (γe : RtkNames) : IProp GF := inv rtkN (rtkBody ρ γe)

instance rtkInv_persistent (ρ : RaftNames) (γe : RtkNames) :
    Persistent (rtkInv (GF := GF) ρ γe) := by
  unfold rtkInv; infer_instance

/-- **`run`'s part** (its loop invariant's): its half of the pending deposit. `none` in the idle and
busy states (§8 item 2), `some ms` between the `readyc` commit and the deposit. -/
def rtkRun (γe : RtkNames) (p : Option (List QMsg)) : IProp GF :=
  dghostVar γe.pk (DFrac.own (1 : Qp).half) p

/-- **The driver's claim** on a received `Ready`'s messages `ms` (§3.1's `readyToksClaim`'s traced
body): nothing claimed (`ms = []`), or key `j`'s element with its allocation bound. -/
def rtkClaim (γe : RtkNames) (ms : List QMsg) : IProp GF :=
  iprop(⌜ms = []⌝ ∨ ∃ j, ghostMapElem γe.rtk j (DFrac.own 1) ms ∗ monoNatLbOwn γe.al (j + 1))

theorem rtkClaim_nil (γe : RtkNames) : ⊢ rtkClaim (GF := GF) γe [] := by
  unfold rtkClaim; ileft; ipureintro; rfl

/-! ### Allocation -/

/-- The escrow, empty, with `run`'s half at `none` (at `newNode`/`setupNode`). -/
theorem rtk_alloc (ρ : RaftNames) (E : CoPset) :
    ⊢ |={E}=> ∃ γe : RtkNames, rtkInv (GF := GF) ρ γe ∗ rtkRun γe none := by
  imod ghost_map_alloc_empty (K := Nat) (V := List QMsg) (GF := GF) with ⟨%γr, Hm⟩
  imod dghostVar_alloc (GF := GF) (none : Option (List QMsg)) with ⟨%γp, Hp⟩
  imod mono_nat_own_alloc (GF := GF) 0 with ⟨%γd, Hd, -⟩
  imod mono_nat_own_alloc (GF := GF) 0 with ⟨%γa, Ha, -⟩
  icases dghostVar_split γp (none : Option (List QMsg)) (DFrac.own (1 : Qp).half)
    (DFrac.own (1 : Qp).half) $$ [Hp] with ⟨Hp1, Hp2⟩
  · rw [DFrac.op_own, Qp.half_add_half]; iexact Hp
  imod inv_alloc rtkN E (rtkBody (GF := GF) ρ ⟨γr, γp, γd, γa⟩) $$ [Hm Hp1 Hd Ha] with #Hi
  · inext
    unfold rtkBody
    iexists [], ∅, none
    simp only [depCount, List.length_nil]
    iframe Hm Hp1
    isplitr
    · ipureintro; intro j; rfl
    isplitr
    · ipureintro; intro _ h; cases h
    iframe Ha Hd
    iapply BigSepL.bigSepL_nil.2
    iempintro
  imodintro
  iexists ⟨γr, γp, γd, γa⟩
  unfold rtkInv rtkRun
  iframe Hi Hp2

/-! ### The `readyc` commit and the deposit (§8 item 1) -/

/-- **A key allocated** (the `readyc` commit): `run`'s half from `none` to `some ms`, the key `a` (the
count allocated) recording `ms`, its element with `monoNatLb al (a + 1)` (the claim). -/
theorem rtk_key (ρ : RaftNames) (γe : RtkNames) (ms : List QMsg) (E : CoPset) (hE : ↑rtkN ⊆ E) :
    ⊢ rtkInv (GF := GF) ρ γe -∗ rtkRun γe none ={E}=∗
      rtkRun γe (some ms) ∗ ∃ j, ghostMapElem γe.rtk j (DFrac.own 1) ms ∗ monoNatLbOwn γe.al (j + 1) := by
  iintro #Hi Hr
  unfold rtkInv
  iinv Hi with >Hb Hclose
  unfold rtkBody
  icases Hb with ⟨%L, %M, %p, Hm, %HML, Hp, %Hpl, Ha, Hd, Hs⟩
  unfold rtkRun
  ihave %Heq := dghostVar_agree _ _ _ _ _ $$ Hp Hr
  subst Heq
  imod dghostVar_update_halves (some ms) γe.pk none none $$ Hp Hr with ⟨Hp, Hr⟩
  have Hfresh : M.lookup L.length = none := by rw [HML]; simp
  imod ghost_map_insert L.length ms Hfresh $$ Hm with ⟨Hm, He⟩
  imod mono_nat_own_update (L.length + 1) (by omega) $$ Ha with ⟨Ha, #Halb⟩
  imod Hclose $$ [Hm Hp Ha Hd Hs] with -
  · inext
    iexists L ++ [ms], M.insert L.length ms, some ms
    iframe Hm Hp
    isplitr
    · ipureintro
      intro j
      rw [GMap.lookup_insert_eq_iff]
      by_cases h : L.length = j
      · subst h; simp
      · rw [ite_eq_right_iff.2 (fun h' => absurd h' h), HML]
        rcases Nat.lt_or_ge j L.length with h' | h'
        · rw [List.getElem?_append_left h']
        · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by simp; omega)]
    isplitr
    · ipureintro; intro _ h; cases h; simp
    simp only [depCount, List.length_append, List.length_singleton, Nat.add_sub_cancel]
    iframe Ha Hd
    iapply BigSepL.bigSepL_snoc.2
    iframe Hs
    unfold rtkSlot
    iintro %h; omega
  imodintro
  iframe Hr
  iexists L.length
  iframe He Halb

/-- **The deposit** (after `acceptReady`, before `advancec` is armed): the pending key's tokens in,
`run`'s half back at `none`, the deposited count up by one. -/
theorem rtk_deposit (ρ : RaftNames) (γe : RtkNames) (ms : List QMsg) (E : CoPset) (hE : ↑rtkN ⊆ E) :
    ⊢ rtkInv (GF := GF) ρ γe -∗ rtkRun γe (some ms) -∗ ([∗list] q ∈ ms, trTokR ρ q.st) ={E}=∗
      rtkRun γe none := by
  iintro #Hi Hr Ht
  unfold rtkInv
  iinv Hi with >Hb Hclose
  unfold rtkBody
  icases Hb with ⟨%L, %M, %p, Hm, %HML, Hp, %Hpl, Ha, Hd, Hs⟩
  unfold rtkRun
  ihave %Heq := dghostVar_agree _ _ _ _ _ $$ Hp Hr
  subst Heq
  obtain ⟨L', rfl⟩ : ∃ L', L = L' ++ [ms] := List.getLast?_eq_some_iff.1 (Hpl ms rfl)
  imod dghostVar_update_halves none γe.pk (some ms) (some ms) $$ Hp Hr with ⟨Hp, Hr⟩
  have hdc : depCount (L' ++ [ms]) (some ms) = L'.length := by simp [depCount]
  rw [hdc]
  imod mono_nat_own_update (L'.length + 1) (by omega) $$ Hd with ⟨Hd, -⟩
  icases BigSepL.bigSepL_snoc.1 $$ Hs with ⟨Hs, -⟩
  imod Hclose $$ [Hm Hp Ha Hd Hs Ht] with -
  · inext
    iexists L' ++ [ms], M, none
    iframe Hm Hp
    isplitr
    · ipureintro; exact HML
    isplitr
    · ipureintro; intro _ h; cases h
    simp only [depCount, List.length_append, List.length_singleton]
    iframe Ha Hd
    iapply BigSepL.bigSepL_snoc.2
    isplitl [Hs]
    · have hmono : ([∗list] k ↦ x ∈ L', rtkSlot (GF := GF) ρ γe L'.length k x) ⊢
          [∗list] k ↦ x ∈ L', rtkSlot ρ γe (L'.length + 1) k x := by
        apply BigSepL.bigSepL_mono
        intro k x hk
        unfold rtkSlot
        iintro H %h
        iapply H
        ipureintro
        have := (List.getElem?_eq_some_iff.mp hk).1
        omega
      iapply hmono
      iexact Hs
    unfold rtkSlot
    iintro %_
    ileft
    iexact Ht
  imodintro
  iexact Hr

/-- The handshake's send with a `|={⊤}=>` prefix (revision 3's S1). Note: `run` already allocates in
such a prefix today (`sendAu_fupd`, `InvNodeRun.lean`, before `ownRawNodeReady_handout ⊤`), so this is
`sendAu_fupd` composed with `handshake_send_au_upd`. -/
theorem handshake_send_au_fupd {V : Type} [Pos.Countable V] [ZeroVal V]
    [TypedPointsto (GF := GF) V] {t : go.GoType} [IntoValTyped (GF := GF) V t]
    (γc : ChanNames) (ch : Loc) (v : V) (P : V → IProp GF) (Q : IProp GF) (Φ : IProp GF) :
    ⊢ £ 1 ∗ £ 1 ∗ £ 1 -∗ isHandshake γc ch P Q -∗ (|={⊤}=> (P v ∗ ▷ (Q -∗ Φ))) -∗
      sendAu γc v Φ := by
  iintro Hlc #His Hupd
  iapply sendAu_fupd
  imod Hupd with ⟨HP, HQ⟩
  imodintro
  iapply handshake_send_au_upd (t := t) γc ch v P Q Φ $$ Hlc His
  imodintro
  iframe HP HQ

/-- **`run`'s `readyc` send** (§8 item 1): the key is allocated only when the send commits, inside the
send AU's `|={⊤}=>` prefix (a `select` firing another case never runs this AU: `run` keeps its
`rtkRun γe none` in that case's conjunct of `wp_select_blocking`'s `[∧list]`); the driver's claim goes
into the payload and `run`'s half at `some ms` into its continuation. -/
theorem readyc_send_rtk {V : Type} [Pos.Countable V] [ZeroVal V]
    [TypedPointsto (GF := GF) V] {t : go.GoType} [IntoValTyped (GF := GF) V t]
    (ρ : RaftNames) (γe : RtkNames) (ms : List QMsg)
    (γc : ChanNames) (ch : Loc) (v : V) (P : V → IProp GF) (Q : IProp GF) (Φ : IProp GF) :
    ⊢ £ 1 ∗ £ 1 ∗ £ 1 -∗ isHandshake γc ch P Q -∗ rtkInv ρ γe -∗ rtkRun γe none -∗
      (rtkRun γe (some ms) -∗ rtkClaim γe ms -∗ |={⊤}=> (P v ∗ ▷ (Q -∗ Φ))) -∗
      sendAu γc v Φ := by
  iintro Hlc #His #Hi Hr Hk
  iapply handshake_send_au_fupd (t := t) γc ch v P Q Φ $$ Hlc His
  imod rtk_key ρ γe ms ⊤ (fun _ _ => CoPset.mem_full) $$ Hi Hr with ⟨Hr, %j, He, #Hlb⟩
  iapply Hk $$ Hr
  unfold rtkClaim
  iright
  iexists j
  iframe He Hlb

/-! ### The `advancec` rendezvous (§8 item 3) -/

/-- **`run`'s commit meeting a waiting driver** (`SndPending`): `run`, its half at `none` (it receives
on `advancec` only after its deposit), turns the payload's allocation bound into a deposit bound. -/
theorem rtk_depLb (ρ : RaftNames) (γe : RtkNames) (j : Nat) (E : CoPset) (hE : ↑rtkN ⊆ E) :
    ⊢ rtkInv (GF := GF) ρ γe -∗ rtkRun γe none -∗ monoNatLbOwn γe.al (j + 1) ={E}=∗
      rtkRun γe none ∗ monoNatLbOwn γe.dep (j + 1) := by
  iintro #Hi Hr #Hlb
  unfold rtkInv
  iinv Hi with >Hb Hclose
  unfold rtkBody
  icases Hb with ⟨%L, %M, %p, Hm, %HML, Hp, %Hpl, Ha, Hd, Hs⟩
  unfold rtkRun
  ihave %Heq := dghostVar_agree _ _ _ _ _ $$ Hp Hr
  subst Heq
  ihave %Hle := monoNatLbOwn_valid _ _ _ _ $$ Ha Hlb
  ihave #Hdlb := monoNatLbOwn_get _ _ _ $$ Hd
  ihave #Hdlb' := monoNatLbOwn_le (j + 1) (by simp only [depCount]; omega) $$ Hdlb
  imod Hclose $$ [Hm Hp Ha Hd Hs] with -
  · inext
    iexists L, M, none
    iframe Hm Hp Ha Hd Hs
    ipureintro; exact ⟨HML, Hpl⟩
  imodintro
  iframe Hr Hdlb'

/-- **The driver's swap** (`node.Advance.tracedSpec`'s tokens): its element of a deposited key in, the
key's tokens out. At any time after `RcvCommit`, whatever `run` allocated since (`p` may be `some`
again for a later key), and for a stale claim. -/
theorem rtk_take (ρ : RaftNames) (γe : RtkNames) (j : Nat) (ms : List QMsg) (E : CoPset)
    (hE : ↑rtkN ⊆ E) :
    ⊢ rtkInv (GF := GF) ρ γe -∗ ghostMapElem γe.rtk j (DFrac.own 1) ms -∗
      monoNatLbOwn γe.dep (j + 1) ={E}=∗ [∗list] q ∈ ms, trTokR ρ q.st := by
  iintro #Hi He #Hlb
  unfold rtkInv
  iinv Hi with >Hb Hclose
  unfold rtkBody
  icases Hb with ⟨%L, %M, %p, Hm, %HML, Hp, %Hpl, Ha, Hd, Hs⟩
  ihave %Hlk := ghost_map_lookup $$ Hm He
  ihave %Hle := monoNatLbOwn_valid _ _ _ _ $$ Hd Hlb
  have HL : L[j]? = some ms := by rw [← HML]; exact Hlk
  icases (BigSepL.bigSepL_lookup_acc HL).1 $$ Hs with ⟨Hsl, Hback⟩
  unfold rtkSlot
  ihave Hsl := Hsl $$ %(by omega)
  icases Hsl with (Ht | He')
  · have Hj := (List.getElem?_eq_some_iff.mp HL)
    have Hset : L.set j ms = L := by
      rw [← Hj.2]; exact List.set_getElem_self Hj.1
    ihave Hs := Hback $$ %ms [He]
    · iintro %_; iright; iexact He
    rw [Hset]
    imod Hclose $$ [Hm Hp Ha Hd Hs] with -
    · inext
      iexists L, M, p
      iframe Hm Hp Ha Hd Hs
      ipureintro; exact ⟨HML, Hpl⟩
    imodintro
    iexact Ht
  · ihave %Hne := ghostMapElem_ne _ _ _ _ _ _ $$ He He'
    exact absurd rfl Hne

/-- **The driver meeting `run`'s offer** (`RcvPending`): with `run`'s lent half (`none`), its element's
key is below the deposited count. -/
theorem rtk_depLb_elem (ρ : RaftNames) (γe : RtkNames) (j : Nat) (ms : List QMsg) (E : CoPset)
    (hE : ↑rtkN ⊆ E) :
    ⊢ rtkInv (GF := GF) ρ γe -∗ rtkRun γe none -∗ ghostMapElem γe.rtk j (DFrac.own 1) ms ={E}=∗
      rtkRun γe none ∗ ghostMapElem γe.rtk j (DFrac.own 1) ms ∗ monoNatLbOwn γe.dep (j + 1) := by
  iintro #Hi Hr He
  unfold rtkInv
  iinv Hi with >Hb Hclose
  unfold rtkBody
  icases Hb with ⟨%L, %M, %p, Hm, %HML, Hp, %Hpl, Ha, Hd, Hs⟩
  unfold rtkRun
  ihave %Heq := dghostVar_agree _ _ _ _ _ $$ Hp Hr
  subst Heq
  ihave %Hlk := ghost_map_lookup $$ Hm He
  have Hj : j < L.length := by
    have : L[j]? = some ms := by rw [← HML]; exact Hlk
    exact (List.getElem?_eq_some_iff.mp this).1
  ihave #Hdlb := monoNatLbOwn_get _ _ _ $$ Hd
  ihave #Hdlb' := monoNatLbOwn_le (j + 1) (by simp only [depCount]; omega) $$ Hdlb
  imod Hclose $$ [Hm Hp Ha Hd Hs] with -
  · inext
    iexists L, M, none
    iframe Hm Hp Ha Hd Hs
    ipureintro; exact ⟨HML, Hpl⟩
  imodintro
  iframe Hr He Hdlb'

/-- **The claim's tokens**, given a deposit bound for any claimed key (the claim-less driver, `ms = []`,
takes nothing). -/
theorem rtkClaim_take (ρ : RaftNames) (γe : RtkNames) (ms : List QMsg) (E : CoPset)
    (hE : ↑rtkN ⊆ E) :
    ⊢ rtkInv (GF := GF) ρ γe -∗ rtkClaim γe ms -∗
      (∀ j, ghostMapElem γe.rtk j (DFrac.own 1) ms -∗ monoNatLbOwn γe.al (j + 1) ={E}=∗
        ghostMapElem γe.rtk j (DFrac.own 1) ms ∗ monoNatLbOwn γe.dep (j + 1)) ={E}=∗
      [∗list] q ∈ ms, trTokR ρ q.st := by
  iintro #Hi Hc Hdep
  unfold rtkClaim
  icases Hc with (%Hnil | ⟨%j, He, #Hal⟩)
  · subst Hnil
    imodintro
    iapply BigSepL.bigSepL_nil.2
    iempintro
  · imod Hdep $$ %j He Hal with ⟨He, #Hd⟩
    iapply rtk_take ρ γe j ms E hE $$ Hi He Hd

/-! #### The rendezvous over a channel: the escrow's part of `advInv`

`escInv` is `advInv` restricted to what the escrow adds to each state (§3.2 item 4): the driver's
`SndPending` payload, its request (`rq`, at threading `AdvReq`'s new `Option Nat`) with the claimed
key's allocation bound; `run`'s `RcvPending` deposit (`advDep`), its half at `none`, which the driver
leaves in `SndCommit` (`advRet`); `run`'s `RcvCommit` answer, the deposit bound for the requested key.
At threading each case is `advInv`'s payload `∗` this one, and the proofs below are the escrow's steps
in `adv_recv_au`/`adv_send_au`. -/

/-- The driver's request's escrow payload: for a claimed key `j`, a bound `B (j + 1)`. -/
def rqPay (B : Nat → IProp GF) : Option Nat → IProp GF
  | none => iprop(True)
  | some j => B (j + 1)

instance rqPay_persistent (B : Nat → IProp GF) [∀ n, Persistent (B n)] (q : Option Nat) :
    Persistent (rqPay B q) := by
  cases q <;> unfold rqPay <;> infer_instance

def escInv (γe : RtkNames) (γc : ChanNames) (rq : GName) : IProp GF :=
  iprop(∃ s, ownChan γc Unit s ∗
    (match s with
     | .Idle => iprop(True)
     | .SndPending _ => iprop(∃ q : Option Nat, dghostVar rq (DFrac.own (1 : Qp).half) q ∗
         rqPay (monoNatLbOwn γe.al) q)
     | .RcvPending => rtkRun γe none
     | .SndCommit _ => rtkRun γe none
     | .RcvCommit => iprop(∃ q : Option Nat, dghostVar rq (DFrac.own (1 : Qp).half) q ∗
         rqPay (monoNatLbOwn γe.dep) q)
     | _ => iprop(False)))

/-- **`run`'s receive on `advancec`** (both orders): its half lent at `none`, back at `none`; meeting a
waiting driver it opens `rtkInv` inside `advInv` (at `⊤ ∖ ↑advN`) and answers the deposit bound. -/
theorem esc_recv_au (ρ : RaftNames) (γe : RtkNames) (γc : ChanNames) (rq : GName)
    (Φ : Unit → Bool → IProp GF) :
    ⊢ £ 1 ∗ £ 1 -∗ inv advN (escInv γe γc rq) -∗ rtkInv ρ γe -∗ rtkRun γe none -∗
      ▷ (rtkRun γe none -∗ Φ () true) -∗ recvAu γc Unit Φ := by
  unfold recvAu
  iintro ⟨Hlc1, Hlc2⟩ #Hinv #Hi Hr Hau
  iinv Hinv with Hx Hclose
  imod lc_fupd_elim_later (E := ⊤ \ ↑advN) $$ Hlc1 Hx with Hx
  unfold escInv
  icases Hx with ⟨%s, Hch, Hx⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  iexists s
  iframe Hch
  rcases s with (_ | ⟨_, _⟩) | _ | v | _ | _ | _ | (_ | ⟨_, _⟩)
  all_goals dsimp only
  case Idle =>
    iintro H
    imod Hmask with -
    imod Hclose $$ [H Hr] with -
    · inext
      iexists .RcvPending
      iframe
    imodintro
    unfold recvNestedAu
    iinv Hinv with Hx Hclose
    imod lc_fupd_elim_later (E := ⊤ \ ↑advN) $$ Hlc2 Hx with Hx
    icases Hx with ⟨%s, Hch, Hx⟩
    iapply fupd_mask_intro Std.LawfulSet.empty_subset
    iintro Hmask
    inext
    iexists s
    iframe Hch
    rcases s with _ | _ | _ | _ | v | _ | (_ | ⟨_, _⟩)
    all_goals dsimp only
    case SndCommit =>
      iintro Hid
      imod Hmask with -
      imod Hclose $$ [Hid] with -
      · inext
        iexists .Idle
        iframe
      imodintro
      iapply Hau $$ Hx
    all_goals first | itrivial | (iexfalso; iexact Hx)
  case SndPending =>
    iintro H
    imod Hmask with -
    icases Hx with ⟨%q, Hrq, #Hpay⟩
    -- `run`'s commit: inside `advInv`, at `⊤ ∖ ↑advN`
    ihave Hans : iprop(|={⊤ \ ↑advN}=> rtkRun γe none ∗ rqPay (monoNatLbOwn γe.dep) q) $$ [Hr]
    · cases q with
      | none => imodintro; iframe Hr; unfold rqPay; itrivial
      | some j =>
        unfold rqPay
        iapply rtk_depLb ρ γe j (⊤ \ ↑advN) rtkN_sub_advN $$ Hi Hr Hpay
    imod Hans with ⟨Hr, #Hans⟩
    imod Hclose $$ [H Hrq Hans] with -
    · inext
      iexists .RcvCommit
      iframe H
      iexists q
      iframe Hrq Hans
    imodintro
    iapply Hau $$ Hr
  all_goals first | itrivial | (iexfalso; iexact Hx)

/-- **The driver's send on `advancec`** (`node.Advance`, both orders), with its claim on `ms`: back with
`ms`'s tokens. Meeting `run`'s offer (`RcvPending`) it swaps inside `advInv` with `run`'s lent half;
waiting (`SndPending`, its payload the persistent allocation bound) it swaps after `RcvCommit`, at
`⊤`, from `run`'s deposit bound. A claim-less driver (`ms = []`, `node.Advance.spec`'s instance)
requests `none` and takes nothing; `run`'s half comes back to it in either order. -/
theorem esc_send_au (ρ : RaftNames) (γe : RtkNames) (γc : ChanNames) (rq : GName) (ms : List QMsg)
    (q0 : Option Nat) (Φ : IProp GF) :
    ⊢ £ 1 ∗ £ 1 ∗ £ 1 -∗ inv advN (escInv γe γc rq) -∗ rtkInv ρ γe -∗ rtkClaim γe ms -∗
      dghostVar rq (DFrac.own (1 : Qp).half) q0 -∗ dghostVar rq (DFrac.own (1 : Qp).half) q0 -∗
      ▷ (([∗list] q ∈ ms, trTokR ρ q.st) -∗
          (∃ q : Option Nat, dghostVar rq (DFrac.own (1 : Qp).half) q ∗
            dghostVar rq (DFrac.own (1 : Qp).half) q) -∗ Φ) -∗
      sendAu γc () Φ := by
  unfold sendAu
  iintro ⟨Hlc1, Hlc2, Hlc3⟩ #Hinv #Hi Hc Hr1 Hr2 Hau
  -- the request: the claimed key, or `none`
  unfold rtkClaim
  ihave Hc' : iprop(∃ q : Option Nat, rqPay (monoNatLbOwn γe.al) q ∗
      ((⌜q = none⌝ ∗ ⌜ms = []⌝) ∨
        ∃ j, ⌜q = some j⌝ ∗ ghostMapElem γe.rtk j (DFrac.own 1) ms)) $$ [Hc]
  · icases Hc with (%Hnil | ⟨%j, He, #Hal⟩)
    · iexists none
      unfold rqPay
      isplitr
      · itrivial
      ileft; ipureintro; exact ⟨rfl, Hnil⟩
    · iexists some j
      unfold rqPay
      iframe Hal
      iright
      iexists j
      iframe He
      ipureintro; rfl
  icases Hc' with ⟨%q, #Hpay, Hcl⟩
  imod dghostVar_update_halves q rq q0 q0 $$ Hr1 Hr2 with ⟨Hr1, Hr2⟩
  iinv Hinv with Hx Hclose
  imod lc_fupd_elim_later (E := ⊤ \ ↑advN) $$ Hlc1 Hx with Hx
  unfold escInv
  icases Hx with ⟨%s, Hch, Hx⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  iexists s
  iframe Hch
  rcases s with b | _ | _ | _ | _ | _ | d
  all_goals dsimp only
  case Idle =>
    iintro H
    imod Hmask with -
    imod Hclose $$ [H Hr1] with -
    · inext
      iexists .SndPending ()
      isplitl [H]
      · iexact H
      iexists q
      iframe Hr1 Hpay
    imodintro
    unfold sendNestedAu
    iinv Hinv with Hx Hclose
    imod lc_fupd_elim_later (E := ⊤ \ ↑advN) $$ Hlc2 Hx with Hx
    icases Hx with ⟨%s, Hch, Hx⟩
    iapply fupd_mask_intro Std.LawfulSet.empty_subset
    iintro Hmask
    inext
    iexists s
    iframe Hch
    rcases s with _ | _ | _ | _ | _ | _ | _
    all_goals dsimp only
    case RcvCommit =>
      iintro Hid
      imod Hmask with -
      icases Hx with ⟨%q', Hr1, #Hans⟩
      ihave %Hk := dghostVar_agree _ _ _ _ _ $$ Hr1 Hr2
      subst Hk
      imod Hclose $$ [Hid] with -
      · inext
        iexists .Idle
        iframe
      -- the swap, at `⊤`, from `run`'s deposit bound
      icases Hcl with (⟨%Hq, %Hnil⟩ | ⟨%j, %Hq, He⟩)
      · subst Hnil
        imodintro
        iapply Hau $$ [] [Hr1 Hr2]
        · iapply BigSepL.bigSepL_nil.2; iempintro
        iexists q'
        iframe Hr1 Hr2
      · subst Hq
        unfold rqPay
        imod rtk_take ρ γe j ms ⊤ (fun _ _ => CoPset.mem_full) $$ Hi He Hans with Ht
        imodintro
        iapply Hau $$ Ht [Hr1 Hr2]
        iexists some j
        iframe Hr1 Hr2
    all_goals itrivial
  case RcvPending =>
    iintro H
    imod Hmask with -
    -- meeting `run`'s offer: the swap inside `advInv`, with `run`'s lent half
    ihave Ht : iprop(|={⊤ \ ↑advN}=> rtkRun γe none ∗ [∗list] q ∈ ms, trTokR ρ q.st) $$ [Hx Hcl]
    · icases Hcl with (⟨%Hq, %Hnil⟩ | ⟨%j, %Hq, He⟩)
      · subst Hnil
        imodintro
        iframe Hx
        iapply BigSepL.bigSepL_nil.2; iempintro
      · imod rtk_depLb_elem ρ γe j ms (⊤ \ ↑advN) rtkN_sub_advN $$ Hi Hx He with ⟨Hx, He, #Hd⟩
        imod rtk_take ρ γe j ms (⊤ \ ↑advN) rtkN_sub_advN $$ Hi He Hd with Ht
        imodintro
        iframe Hx Ht
    imod Ht with ⟨Hx, Ht⟩
    imod Hclose $$ [H Hx] with -
    · inext
      iexists .SndCommit ()
      iframe
    imodintro
    iapply Hau $$ Ht [Hr1 Hr2]
    iexists q
    iframe Hr1 Hr2
  all_goals first | itrivial | (iexfalso; iexact Hx)

/-- **A run of the escrow** (§8 item 3's stale claim, ghost-level): key 0 allocated and deposited, its
`Advance` without the claim (nothing taken), key 1 allocated (`run`'s half `some` again), then the
driver's stale claim on key 0 swapped while key 1 is pending; then key 1's deposit. -/
theorem rtk_scenario (ρ : RaftNames) (γe : RtkNames) (ms0 ms1 : List QMsg) :
    ⊢ rtkInv (GF := GF) ρ γe -∗ rtkRun γe none -∗ ([∗list] q ∈ ms0, trTokR ρ q.st) -∗
      ([∗list] q ∈ ms1, trTokR ρ q.st) -∗
      |={⊤}=> rtkRun γe none ∗ ([∗list] q ∈ ms0, trTokR ρ q.st) := by
  have hT : (↑rtkN : CoPset) ⊆ ⊤ := fun _ _ => CoPset.mem_full
  iintro #Hi Hr Ht0 Ht1
  imod rtk_key ρ γe ms0 ⊤ hT $$ Hi Hr with ⟨Hr, %j0, He0, #Hal0⟩
  imod rtk_deposit ρ γe ms0 ⊤ hT $$ Hi Hr Ht0 with Hr
  -- key 0's `Advance`, by a driver without its claim (`ms = []`): `run`'s commit answers a deposit
  -- bound only for a requested key, and its half comes back as it was; here the bound for key 0 is
  -- minted as `run`'s answer to a request for it would be
  imod rtk_depLb ρ γe j0 ⊤ hT $$ Hi Hr Hal0 with ⟨Hr, #Hd0⟩
  -- key 1 allocated: `run`'s half `some` again
  imod rtk_key ρ γe ms1 ⊤ hT $$ Hi Hr with ⟨Hr, %j1, -, -⟩
  -- the stale claim on key 0, swapped while key 1 is pending
  imod rtk_take ρ γe j0 ms0 ⊤ hT $$ Hi He0 Hd0 with Ht0
  -- key 1's deposit
  imod rtk_deposit ρ γe ms1 ⊤ hT $$ Hi Hr Ht1 with Hr
  imodintro
  iframe Hr Ht0

/-! ### The receiver (§8 item 4) -/

/-- (§3.2 item 6) `fwdP`'s traced clause: a forwarded proposal's entries normal. -/
def fwdGate (ρ : RaftNames) (st : MsgSt) : IProp GF :=
  match ρ.reTrace with
  | none => iprop(True)
  | some _ => iprop(⌜∀ e ∈ st.ents, e.Type' = EntryNormal⌝)

/-- (§3.2 item 5) `netP`'s traced clause: a traced network type with its token, or `MsgUnreachable`. -/
def netGate (ρ : RaftNames) (st : MsgSt) : IProp GF :=
  match ρ.reTrace with
  | none => iprop(True)
  | some γd => iprop((⌜TrNetTy st.msg.Type'⌝ ∗ recvTokOf γd st.msg st.ents st.ctx) ∨
      ⌜st.msg.Type' = MsgUnreachable⌝)

/-- `stepIn_intro`'s traced split, a proposal: to `fwdP`. -/
theorem trTokR_fwd (ρ : RaftNames) (st : MsgSt) (h : st.msg.Type' = MsgProp) :
    trTokR (GF := GF) ρ st ⊢ fwdGate ρ st := by
  unfold trTokR fwdGate
  cases ρ.reTrace with
  | none => iintro _; itrivial
  | some γd =>
    iintro ⟨%Hs, -⟩
    ipureintro
    rcases Hs with Hn | ⟨_, He⟩
    · exfalso
      rcases Hn with h' | h' | h' | h' | h' | h' <;> rw [h'] at h <;>
        simp [MsgProp, MsgApp, MsgAppResp, MsgVote, MsgVoteResp, MsgHeartbeat, MsgHeartbeatResp] at h
    · exact He

/-- `stepIn_intro`'s traced split, anything else: to `netP`, with its token. -/
theorem trTokR_net (ρ : RaftNames) (st : MsgSt) (h : st.msg.Type' ≠ MsgProp) :
    trTokR (GF := GF) ρ st ⊢ netGate ρ st := by
  unfold trTokR netGate
  cases ρ.reTrace with
  | none => iintro _; itrivial
  | some γd =>
    iintro ⟨%Hs, Ht⟩
    rcases Hs with Hn | ⟨Hp, _⟩
    · ileft; iframe Ht; ipureintro; exact Hn
    · exact absurd Hp h

/-- A message of a type without abstraction carries a token vacuously. -/
theorem recvTokOf_untyped (γd : GName) (m : MessageM) (ents : List EntryM) (ctx : List w8)
    (h : mtypeOf m.Type' = none) : ⊢ recvTokOf (GF := GF) γd m ents ctx := by
  unfold recvTokOf
  iintro %ty %hty
  rw [h] at hty
  exact absurd hty.1 (by simp)

/-- **The `recvc` arm's premises of `raft.Step.tracedTriple`** from `netP`'s traced clause: the type
(`StepEndTy`) and the received message's token (vacuous for `MsgUnreachable`). `Campaign`'s `MsgHup`
(`hupP`) is the same by `recvTokOf_untyped`. `StepNodeOk` comes from the guard's `Progress` lookup as
in `RawNode.Step.traced` (`ownRaftPhysC_prvals_ok`), unchanged. -/
theorem netGate_step (ρ : RaftNames) (γd : GName) (st : MsgSt) (htr : ρ.reTrace = some γd) :
    netGate (GF := GF) ρ st ⊢
      ⌜StepEndTy st.msg.Type' ∨ AckTy st.msg.Type'⌝ ∗ recvTokOf γd st.msg st.ents st.ctx := by
  unfold netGate
  rw [htr]
  iintro (⟨%Hn, Ht⟩ | %Hu)
  · iframe Ht; ipureintro; exact .inl Hn.stepEndTy
  · isplitr
    · ipureintro; left; unfold StepEndTy; simp [Hu]
    iapply recvTokOf_untyped γd st.msg st.ents st.ctx (by rw [Hu]; rfl)

end escrow

end EtcdGrove
end Perennial
