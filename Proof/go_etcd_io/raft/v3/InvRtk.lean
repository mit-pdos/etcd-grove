/-
Lean-first (no Rocq counterpart). **The node's token escrow** (trace-check implementation step 1,
2026-11-12; `notes/trace-check-design.md` §3.2 items 2-4 with Probe B's P1; `notes/decisions.md`,
"Implementation step 1 (gates)"): Probe B's `TracedEscrow.lean` escrow, moved below `InvNodeChan`
(which threads it: `NodeNames.esc`, `isAdvChan`'s `rtkInv`, `readyP`'s element, `advInv`'s request,
`advDep`/`advRet`'s `run` half) and gated on the trace (`gateTr`: `True` untraced, so that every
untraced proof is today's).

- `rtkInv ρ γe` (in `rtkN`): the keys `L` (key `j` at position `j`, each a `Ready`'s handed-out
  messages), `run`'s pending deposit `pk` in halves (`rtkRun`, Probe B's P1: one agreement variable in
  place of the design's exclusive `np` and Boolean `pend`), the counts allocated (`al`) and deposited
  (`dep`), each slot below the deposited count holding its tokens (`trTokR`) or the driver's element.
- `rtkElem γe ms`: the driver's element of a key recording `ms`, with the key's allocation bound
  (`readyP`'s gated payload); `rtkClaim γe ms`: nothing claimed (`ms = []`) or that element.
- the steps: allocation (`rtk_alloc`), the `readyc` commit's key (`rtk_key`), the deposit
  (`rtk_deposit`), `run`'s answer to a waiting driver (`rtk_depLb`), the driver's swap (`rtk_take`),
  the driver meeting `run`'s offer (`rtk_depLb_elem`);
- the `advancec` rendezvous's gated steps over `advInv`'s escrow payloads (`escPay`, `escHeld`):
  `esc_recv_commit` (`run` meets a waiting driver), `esc_send_prep` (the driver's request from its
  claim), `esc_send_rcvPending` (the driver meets `run`'s offer), `esc_send_rcvCommit` (the driver's
  swap after `run`'s answer).
-/
module

public import Proof.go_etcd_io.raft.v3.InvRawnodeReady
public import Proof.go_etcd_io.raft.v3.TracedRecvTok
public import Perennial.Ghost.MonoNat

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

/-- The escrow's namespace (the design's §3.2 item 2, revision 3's S1). -/
def rtkN : Namespace := nroot.@"raft_rtk"

/-- The escrow's ghost names (`NodeNames.esc`). Each defaults to `0`: an untraced node allocates none
(its escrow is `True`, `gateTr`). -/
structure RtkNames where
  /-- the keys: a ghost map `Nat ↦ List QMsg`, each `Ready`'s handed-out messages -/
  rtk : GName := 0
  /-- `run`'s pending deposit, in halves (the invariant's and `run`'s): Probe B's P1, in place of the
  design's `np` and `pend` -/
  pk : GName := 0
  /-- the keys deposited, a monotone count -/
  dep : GName := 0
  /-- the keys allocated, a monotone count (revision 2's A1) -/
  al : GName := 0
  /-- the driver's request at `advancec`: the claimed key, or `none` (halves: the driver's and, while
  its offer waits or `run`'s answer does, `advInv`'s). The design's `AdvReq` gaining `Option Nat`, as
  a name of its own (implementation step 1): `AdvReq`'s users stay as they are. -/
  rq : GName := 0

/-- The names as a tuple (the node table's `cfgNamesOf` records them, so that a claim names the escrow
of the node the driver advances). -/
def RtkNames.tup (γe : RtkNames) : GName × GName × GName × GName × GName :=
  (γe.rtk, γe.pk, γe.dep, γe.al, γe.rq)

theorem RtkNames.tup_inj {γ1 γ2 : RtkNames} (h : γ1.tup = γ2.tup) : γ1 = γ2 := by
  cases γ1; cases γ2; simp only [RtkNames.tup, Prod.mk.injEq] at h
  obtain ⟨h1, h2, h3, h4, h5⟩ := h; subst h1 h2 h3 h4 h5; rfl

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

/-! ### The gate -/

/-- **A traced-only resource**: `True` untraced (`o = none`), `P` traced. Every escrow piece the node's
invariants and payloads hold is under it, so that their untraced arms are today's. -/
def gateTr (o : Option GName) (P : IProp GF) : IProp GF :=
  match o with
  | none => iprop(True)
  | some _ => P

instance gateTr_persistent (o : Option GName) (P : IProp GF) [Persistent P] :
    Persistent (gateTr o P) := by
  unfold gateTr; cases o <;> infer_instance

instance gateTr_timeless (o : Option GName) (P : IProp GF) [Timeless P] :
    Timeless (gateTr o P) := by
  unfold gateTr; cases o <;> infer_instance

theorem gateTr_none (o : Option GName) (P : IProp GF) (h : o = none) : ⊢ gateTr o P := by
  subst h; unfold gateTr; iintro; ipureintro; trivial

theorem gateTr_some (o : Option GName) (γd : GName) (P : IProp GF) (h : o = some γd) :
    gateTr o P ⊣⊢ P := by
  subst h; exact .rfl

theorem gateTr_intro (o : Option GName) (P : IProp GF) : P ⊢ gateTr o P := by
  unfold gateTr; cases o
  · iintro -; ipureintro; trivial
  · exact .rfl

theorem gateTr_wand (o : Option GName) (P Q : IProp GF) :
    ⊢ (P -∗ Q) -∗ gateTr o P -∗ gateTr o Q := by
  unfold gateTr; cases o
  · iintro - -; ipureintro; trivial
  · iintro H HP; iapply H $$ HP

theorem gateTr_sep (o : Option GName) (P Q : IProp GF) :
    gateTr o (iprop(P ∗ Q)) ⊣⊢ gateTr o P ∗ gateTr o Q := by
  unfold gateTr; cases o
  · constructor
    · iintro -; isplitr <;> (ipureintro; trivial)
    · iintro -; ipureintro; trivial
  · exact .rfl

/-! ### The escrow -/

/-- `acceptReady`'s token (`readyTok`) is the escrow's (`trTokR`): (2026-11-12, implementation step 3)
the same body, `readyTok` carrying its type handed out (`TrSent`) since `rnTrace`'s clause (b) and
`XfOk`'s traced clause give it at the `Ready` (until then a premise here). -/
theorem readyTok_trTokR (ρ : RaftNames) (st : MsgSt) :
    readyTok (GF := GF) ρ st ⊣⊢ trTokR ρ st := by
  unfold readyTok trTokR
  exact .rfl

/-- A key's slot: below the deposited count, the tokens, or the driver's element swapped in. -/
def rtkSlot (ρ : RaftNames) (γe : RtkNames) (dc j : Nat) (ms : List QMsg) : IProp GF :=
  iprop(⌜j < dc⌝ -∗ (([∗list] q ∈ ms, trTokR ρ q.st) ∨ ghostMapElem γe.rtk j (DFrac.own 1) ms))

/-- **The escrow's body** (the design's §3.2 item 2, with `pk` for `np`/`pend`): the keys `L` (key `j`
at position `j`), the pending deposit `p` (the last key's), the counts, the slots. -/
def rtkBody (ρ : RaftNames) (γe : RtkNames) : IProp GF :=
  iprop(∃ (L : List (List QMsg)) (M : GMap Nat (List QMsg)) (p : Option (List QMsg)),
    ghostMapAuth γe.rtk 1 M ∗ ⌜∀ j, M.lookup j = L[j]?⌝ ∗
    dghostVar γe.pk (DFrac.own (1 : Qp).half) p ∗
    ⌜∀ ms, p = some ms → L.getLast? = some ms⌝ ∗
    monoNatAuthOwn γe.al 1 L.length ∗
    monoNatAuthOwn γe.dep 1 (depCount L p) ∗
    [∗list] j ↦ ms ∈ L, rtkSlot ρ γe (depCount L p) j ms)

instance rtkSlot_timeless (ρ : RaftNames) (γe : RtkNames) (dc j : Nat) (ms : List QMsg) :
    Timeless (rtkSlot (GF := GF) ρ γe dc j ms) := by
  unfold rtkSlot; infer_instance

instance rtkBody_timeless (ρ : RaftNames) (γe : RtkNames) : Timeless (rtkBody (GF := GF) ρ γe) := by
  unfold rtkBody; infer_instance

/-- **The escrow** (persistent; gated in `isAdvChan`). -/
def rtkInv (ρ : RaftNames) (γe : RtkNames) : IProp GF := inv rtkN (rtkBody ρ γe)

instance rtkInv_persistent (ρ : RaftNames) (γe : RtkNames) :
    Persistent (rtkInv (GF := GF) ρ γe) := by
  unfold rtkInv; infer_instance

/-- **`run`'s part**: its half of the pending deposit. `none` in the idle and busy states, `some ms`
between the `readyc` commit and the deposit. -/
def rtkRun (γe : RtkNames) (p : Option (List QMsg)) : IProp GF :=
  dghostVar γe.pk (DFrac.own (1 : Qp).half) p

/-- **The driver's element** of a key recording `ms`, with the key's allocation bound (`readyP`'s
gated payload, minted at the `readyc` commit). -/
def rtkElem (γe : RtkNames) (ms : List QMsg) : IProp GF :=
  iprop(∃ j, ghostMapElem γe.rtk j (DFrac.own 1) ms ∗ monoNatLbOwn γe.al (j + 1))

/-- **The driver's claim** on a received `Ready`'s messages `ms` (the design's §3.1
`readyToksClaim`'s traced body): nothing claimed (`ms = []`), or the key's element. -/
def rtkClaim (γe : RtkNames) (ms : List QMsg) : IProp GF :=
  iprop(⌜ms = []⌝ ∨ rtkElem γe ms)

theorem rtkClaim_nil (γe : RtkNames) : ⊢ rtkClaim (GF := GF) γe [] := by
  unfold rtkClaim; ileft; ipureintro; rfl

/-! #### Allocation -/

/-- The escrow, empty, with `run`'s half at `none` (at a traced node's start). -/
theorem rtk_alloc (ρ : RaftNames) (E : CoPset) :
    ⊢ |={E}=> ∃ γe : RtkNames, rtkInv (GF := GF) ρ γe ∗ rtkRun γe none ∗
      ∃ q : Option Nat, dghostVar γe.rq (DFrac.own (1 : Qp).half) q ∗
        dghostVar γe.rq (DFrac.own (1 : Qp).half) q := by
  imod ghost_map_alloc_empty (K := Nat) (V := List QMsg) (GF := GF) with ⟨%γr, Hm⟩
  imod dghostVar_alloc (GF := GF) (none : Option (List QMsg)) with ⟨%γp, Hp⟩
  imod dghostVar_alloc (GF := GF) (none : Option Nat) with ⟨%γq, Hq⟩
  imod mono_nat_own_alloc (GF := GF) 0 with ⟨%γd, Hd, -⟩
  imod mono_nat_own_alloc (GF := GF) 0 with ⟨%γa, Ha, -⟩
  icases dghostVar_split γp (none : Option (List QMsg)) (DFrac.own (1 : Qp).half)
    (DFrac.own (1 : Qp).half) $$ [Hp] with ⟨Hp1, Hp2⟩
  · rw [DFrac.op_own, Qp.half_add_half]; iexact Hp
  icases dghostVar_split γq (none : Option Nat) (DFrac.own (1 : Qp).half)
    (DFrac.own (1 : Qp).half) $$ [Hq] with ⟨Hq1, Hq2⟩
  · rw [DFrac.op_own, Qp.half_add_half]; iexact Hq
  imod inv_alloc rtkN E (rtkBody (GF := GF) ρ ⟨γr, γp, γd, γa, γq⟩) $$ [Hm Hp1 Hd Ha] with #Hi
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
  iexists ⟨γr, γp, γd, γa, γq⟩
  unfold rtkInv rtkRun
  iframe Hi Hp2
  iexists none
  iframe Hq1 Hq2

/-! #### The `readyc` commit and the deposit -/

/-- **A key allocated** (the `readyc` commit): `run`'s half from `none` to `some ms`, the key `a` (the
count allocated) recording `ms`, its element with `monoNatLb al (a + 1)`. -/
theorem rtk_key (ρ : RaftNames) (γe : RtkNames) (ms : List QMsg) (E : CoPset) (hE : ↑rtkN ⊆ E) :
    ⊢ rtkInv (GF := GF) ρ γe -∗ rtkRun γe none ={E}=∗ rtkRun γe (some ms) ∗ rtkElem γe ms := by
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
  unfold rtkElem
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

/-! #### The `advancec` rendezvous -/

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

/-- **The driver's swap**: its element of a deposited key in, the key's tokens out. At any time after
`RcvCommit`, whatever `run` allocated since, and for a stale claim. -/
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

/-! #### The rendezvous's gated steps (`advInv`'s escrow payloads)

`advInv` (`InvNodeChan.lean`) carries, gated: in `SndPending` the driver's request half with the
claimed key's allocation bound (`escPay γe (monoNatLbOwn γe.al)`); in `RcvCommit` `run`'s answer, the
request half with the deposit bound (`escPay γe (monoNatLbOwn γe.dep)`); in `RcvPending`/`SndCommit`
`run`'s lent half (`advDep`/`advRet`'s `rtkRun γe none`). The driver keeps `escHeld γe ms` (its other
request half and its element) across its send. -/

/-- The driver's request's escrow payload: for a claimed key `j`, a bound `B (j + 1)`. -/
def rqPay (B : Nat → IProp GF) : Option Nat → IProp GF
  | none => iprop(True)
  | some j => B (j + 1)

instance rqPay_persistent (B : Nat → IProp GF) [∀ n, Persistent (B n)] (q : Option Nat) :
    Persistent (rqPay B q) := by
  cases q <;> unfold rqPay <;> infer_instance

/-- A request half with its payload. -/
def escPay (γe : RtkNames) (B : Nat → IProp GF) : IProp GF :=
  iprop(∃ q : Option Nat, dghostVar γe.rq (DFrac.own (1 : Qp).half) q ∗ rqPay B q)

/-- The driver's request, whole (its two halves, at rest). -/
def escReq (γe : RtkNames) : IProp GF :=
  iprop(∃ q : Option Nat, dghostVar γe.rq (DFrac.own (1 : Qp).half) q ∗
    dghostVar γe.rq (DFrac.own (1 : Qp).half) q)

/-- What the driver keeps across its send: its request half, at the key it claims (with the element)
or at `none` (with nothing claimed). -/
def escHeld (γe : RtkNames) (ms : List QMsg) : IProp GF :=
  iprop(∃ q : Option Nat, dghostVar γe.rq (DFrac.own (1 : Qp).half) q ∗
    ((⌜q = none⌝ ∗ ⌜ms = []⌝) ∨ ∃ j, ⌜q = some j⌝ ∗ ghostMapElem γe.rtk j (DFrac.own 1) ms))

/-- **The driver's request from its claim** (before its send): its request at the claimed key. -/
theorem esc_send_prep (o : Option GName) (γe : RtkNames) (ms : List QMsg) :
    ⊢ gateTr (GF := GF) o (rtkClaim γe ms) -∗ gateTr o (escReq γe) ==∗
      gateTr o (escPay γe (monoNatLbOwn γe.al)) ∗ gateTr o (escHeld γe ms) := by
  unfold gateTr
  cases o with
  | none => iintro - -; imodintro; isplitr <;> (ipureintro; trivial)
  | some _ =>
    dsimp only
    unfold escReq
    iintro Hc ⟨%q0, Hr1, Hr2⟩
    unfold rtkClaim rtkElem
    icases Hc with (%Hnil | ⟨%j, He, #Hal⟩)
    · imod dghostVar_update_halves (none : Option Nat) γe.rq q0 q0 $$ Hr1 Hr2 with ⟨Hr1, Hr2⟩
      imodintro
      unfold escPay escHeld rqPay
      isplitl [Hr1]
      · iexists none; iframe Hr1
      iexists none; iframe Hr2; ileft; ipureintro; exact ⟨rfl, Hnil⟩
    · imod dghostVar_update_halves (some j) γe.rq q0 q0 $$ Hr1 Hr2 with ⟨Hr1, Hr2⟩
      imodintro
      unfold escPay escHeld rqPay
      isplitl [Hr1]
      · iexists some j; iframe Hr1 Hal
      iexists some j; iframe Hr2; iright; iexists j; iframe He; ipureintro; rfl

/-- **`run` meeting a waiting driver** (`SndPending → RcvCommit`, inside `advInv` at `E`): the deposit
bound for the requested key, `run`'s half back. -/
theorem esc_recv_commit (ρ : RaftNames) (γe : RtkNames) (E : CoPset) (hE : ↑rtkN ⊆ E) :
    ⊢ gateTr (GF := GF) ρ.reTrace (rtkInv ρ γe) -∗ gateTr ρ.reTrace (rtkRun γe none) -∗
      gateTr ρ.reTrace (escPay γe (monoNatLbOwn γe.al)) ={E}=∗
      gateTr ρ.reTrace (rtkRun γe none) ∗ gateTr ρ.reTrace (escPay γe (monoNatLbOwn γe.dep)) := by
  unfold gateTr
  cases ρ.reTrace with
  | none => iintro - - -; imodintro; isplitr <;> (ipureintro; trivial)
  | some _ =>
    dsimp only
    unfold escPay
    iintro #Hi Hr ⟨%q, Hrq, #Hpay⟩
    cases q with
    | none =>
      imodintro; iframe Hr; iexists none; iframe Hrq; unfold rqPay; itrivial
    | some j =>
      unfold rqPay
      imod rtk_depLb ρ γe j E hE $$ Hi Hr Hpay with ⟨Hr, #Hd⟩
      imodintro; iframe Hr; iexists some j; iframe Hrq Hd

/-- **The driver meeting `run`'s offer** (`RcvPending → SndCommit`, inside `advInv` at `E`): its swap
with `run`'s lent half, which goes back to `run`; the request whole again. -/
theorem esc_send_rcvPending (ρ : RaftNames) (γe : RtkNames) (ms : List QMsg) (E : CoPset)
    (hE : ↑rtkN ⊆ E) :
    ⊢ gateTr (GF := GF) ρ.reTrace (rtkInv ρ γe) -∗ gateTr ρ.reTrace (rtkRun γe none) -∗
      gateTr ρ.reTrace (escPay γe (monoNatLbOwn γe.al)) -∗ gateTr ρ.reTrace (escHeld γe ms) ={E}=∗
      gateTr ρ.reTrace (rtkRun γe none) ∗ ([∗list] q ∈ ms, trTokR ρ q.st) ∗
        gateTr ρ.reTrace (escReq γe) := by
  have Hn : ρ.reTrace = none → ⊢ [∗list] q ∈ ms, trTokR (GF := GF) ρ q.st :=
    fun h => trTokRs_none ρ QMsg.st ms h
  unfold gateTr
  cases h : ρ.reTrace with
  | none =>
    dsimp only
    iintro - - - -; imodintro
    isplitr; · ipureintro; trivial
    isplitr; · iapply Hn h
    ipureintro; trivial
  | some _ =>
    dsimp only
    unfold escPay escHeld
    iintro #Hi Hr ⟨%q, Hrq, -⟩ ⟨%q', Hrq', Hcl⟩
    ihave %Hk := dghostVar_agree _ _ _ _ _ $$ Hrq Hrq'
    subst Hk
    unfold escReq
    icases Hcl with (⟨-, %Hnil⟩ | ⟨%j, -, He⟩)
    · subst Hnil
      imodintro
      iframe Hr
      isplitr
      · iapply BigSepL.bigSepL_nil.2; iempintro
      iexists q; iframe Hrq Hrq'
    · imod rtk_depLb_elem ρ γe j ms E hE $$ Hi Hr He with ⟨Hr, He, #Hd⟩
      imod rtk_take ρ γe j ms E hE $$ Hi He Hd with Ht
      imodintro
      iframe Hr Ht
      iexists q; iframe Hrq Hrq'

/-- **The driver's swap after `run`'s answer** (`RcvCommit`, at `⊤`, or any `E` holding `rtkN`): its
element in for the deposit bound `run` answered; the request whole again. -/
theorem esc_send_rcvCommit (ρ : RaftNames) (γe : RtkNames) (ms : List QMsg) (E : CoPset)
    (hE : ↑rtkN ⊆ E) :
    ⊢ gateTr (GF := GF) ρ.reTrace (rtkInv ρ γe) -∗
      gateTr ρ.reTrace (escPay γe (monoNatLbOwn γe.dep)) -∗ gateTr ρ.reTrace (escHeld γe ms) ={E}=∗
      ([∗list] q ∈ ms, trTokR ρ q.st) ∗ gateTr ρ.reTrace (escReq γe) := by
  have Hn : ρ.reTrace = none → ⊢ [∗list] q ∈ ms, trTokR (GF := GF) ρ q.st :=
    fun h => trTokRs_none ρ QMsg.st ms h
  unfold gateTr
  cases h : ρ.reTrace with
  | none =>
    dsimp only
    iintro - - -; imodintro
    isplitr; · iapply Hn h
    ipureintro; trivial
  | some _ =>
    dsimp only
    unfold escPay escHeld
    iintro #Hi ⟨%q, Hrq, #Hans⟩ ⟨%q', Hrq', Hcl⟩
    ihave %Hk := dghostVar_agree _ _ _ _ _ $$ Hrq Hrq'
    subst Hk
    unfold escReq
    icases Hcl with (⟨%Hq, %Hnil⟩ | ⟨%j, %Hq, He⟩)
    · subst Hnil
      imodintro
      isplitr
      · iapply BigSepL.bigSepL_nil.2; iempintro
      iexists q; iframe Hrq Hrq'
    · subst Hq
      unfold rqPay
      imod rtk_take ρ γe j ms E hE $$ Hi He Hans with Ht
      imodintro
      iframe Ht
      iexists some j; iframe Hrq Hrq'

end escrow

end EtcdGrove
end Perennial
