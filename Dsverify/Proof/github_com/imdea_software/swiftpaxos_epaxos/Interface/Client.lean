/-
Ported from dsverify-lab examples/epaxos/proof/Epaxos/Interface/Client.lean (run epaxos-e1nogs-1;
notes/dsv-epaxos.md), redesigned for `examples/lib/remote`: the op's update is remote's one-shot
`lin` (`opU`, an update `|={⊤ ∖ epEop, ∅}=> …` at the store's state) in place of the lab's atomic
update at `clientN`, and the world is the part's (`GooseGlobalGS` over any `GF`, `Proto.lean`'s
`connFresh`/`addrProto`, connection numbers `Nat`).

The client side of the cross-package interface:

* **The abstract state.** `kvHalf γ σ`: half of the ghost variable `γ.kv` over a finite map whose
  lookup is `σ` (the model's state, a function, is not `Pos.Countable`, so the variable holds a
  `GMap` and `σ` is its lookup). The store's `own_state` (remote's `RBase.sysState`) is one half;
  the other half belongs to the replicas' invariant. `escrow_fire` is the only law that changes
  them. The store's step is `kvStep` (a function: linkv's `PendSpec.step`), the lab's `kvScan`
  relation's (`kvStep_spec`).
* **Connection roles.** A ghost map `γ.roles` from the number of a connection to a replica's
  peer/client address to its role (`ConnRole`: a peer `d`, or client `c`'s op with input `i`),
  registered by the dialer with its `connFresh cid false` token (`roleInv`), so each connection has
  at most one role and every party agrees on it. A client connection's escrow names are registered
  with its role, in a separate map (`escrowNames`).
* **The escrow of an op** (keyed by its connection `cid`, names `nm`: claim token `nm.1`, fire state
  `nm.2`): an invariant `opInv` at `opN cid` holding, while pending, the op's update (`opU`, remote's
  `lin`) and the whole fire state (`none`); once fired with output `o`, the update's postcondition
  `Φ o` (until claimed, then the op's claim token). `fired γ cid o` (persistent) is the fire state
  discarded at `some o` together with the replicas' fired map's entry. Laws: `escrow_register`
  (`Op`), `escrow_fire` (the replica that executes the op's command first), `escrow_claim` (`Op`, on
  a reply).
* **The protocols of a replica's peer/client address** `a` (`repDialP γ a`, `repAccP γ a`): the
  empty stream (always: a writer is created before anything is known of the connection), else by
  the connection's role, the client role in full (`proposeBytes`, `encProposeReplyTS`), the peer
  role through `peerStreamOk` (`Interface/Net.lean`).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Interface.Net

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net github_com.imdea_software.swiftpaxos_epaxos.kvs

attribute [local instance] GooseGlobalGS.gooseInvGS

/-! ## Types and namespaces -/

/-- The model's state, input and output (`(kvScan w8).State` etc., spelled out so that instances
are found). -/
abbrev KvS := w64 → Option (List w8)
abbrev KvI := KvsInput (List w8)
abbrev KvO := KvsOutput (List w8)

/-- The store's step (linkv's `PendSpec.step`): `kvScan`'s, as a function. -/
def kvStep (i : KvI) (σ : KvS) : KvS × KvO :=
  match i with
  | .get k => (σ, .got (σ k))
  | .put k v => (fun k' => if k' = k then some v else σ k', .done)
  | .scan k n => (σ, .scanned ((scanKeys k n).filterMap σ).flatten)

theorem kvStep_spec (i : KvI) (σ : KvS) : (kvScan w8).step σ i (kvStep i σ).1 (kvStep i σ).2 := by
  cases i <;> exact ⟨rfl, rfl⟩

/-- The input premise (the lab's `kit.pre`): keys below `NKeys = 2`, a put's value non-empty and
below `2 ^ 15` bytes, a scan's count below 2. -/
def inPre : KvI → Prop
  | .get k => k.toNat < 2
  | .put k v => k.toNat < 2 ∧ v ≠ [] ∧ v.length < 2 ^ 15
  | .scan k n => k.toNat < 2 ∧ n.toNat < 2

/-- An output as a countable value (the fired map's values). -/
def kvOutCode : KvO → Option (Option (List w8)) ⊕ List w8
  | .done => .inl none
  | .got x => .inl (some x)
  | .scanned v => .inr v

instance kvOutput_countable : Pos.Countable KvO :=
  .ofInjective (fun o => Pos.Countable.encode (kvOutCode o)) (by
    intro a b h
    have h' := Pos.encode_inj h
    cases a <;> cases b <;> simp_all [kvOutCode])

/-- The role of a connection to a replica's peer/client address: a replica peer `d` (its replica
id), or client `c`'s op with input `i`. -/
inductive ConnRole where
  | peer (d : w64)
  | client (c : w64) (i : KvI)

/-- A role as a countable value. -/
def ConnRole.code : ConnRole → w64 ⊕ (w64 × (w8 × w64 × w64 × List w8))
  | .peer d => .inl d
  | .client c (.get k) => .inr (c, (W8 0, k, W64 0, []))
  | .client c (.put k v) => .inr (c, (W8 1, k, W64 0, v))
  | .client c (.scan k n) => .inr (c, (W8 2, k, n, []))

instance connRole_countable : Pos.Countable ConnRole :=
  .ofInjective (fun r => Pos.Countable.encode r.code) (by
    intro a b h
    have h' := Pos.encode_inj h
    rcases a with _ | ⟨_, _ | ⟨_, _⟩ | ⟨_, _⟩⟩ <;> rcases b with _ | ⟨_, _ | ⟨_, _⟩ | ⟨_, _⟩⟩ <;>
      simp_all [ConnRole.code])

/-- The names of an op's escrow: its claim token (`.1`) and its fire state (`.2`). -/
abbrev EscNames := GName × GName

/-- The namespace of the EPaxos run's invariants. -/
def epN : Namespace := ndot nroot "epaxos"
/-- The connection-role registry's invariant. -/
def roleN : Namespace := ndot epN "roles"
/-- The escrows' invariants (one per op, `opN cid`). -/
def escrowN : Namespace := ndot epN "escrow"
/-- The escrow of the op on connection `cid`. -/
def opN (cid : Nat) : Namespace := ndot escrowN cid

/-- The invariants an op's update may find open when it fires (remote's `RBase.Eop` of the store):
all of the run's. -/
def epEop : CoPset := ↑epN

theorem opN_subseteq (cid : Nat) : (↑(opN cid) : CoPset) ⊆ ↑escrowN := by
  unfold opN; exact nclose_subseteq _ _

theorem escrowN_subseteq : (↑escrowN : CoPset) ⊆ ↑epN := by
  unfold escrowN; exact nclose_subseteq _ _

theorem roleN_subseteq : (↑roleN : CoPset) ⊆ ↑epN := by
  unfold roleN; exact nclose_subseteq _ _

/-- From a mask holding `⊤ ∖ epEop`, the mask without an escrow still holds it. -/
theorem epEop_diff_opN {E : CoPset} (cid : Nat) (hEc : ⊤ \ epEop ⊆ E) :
    ⊤ \ epEop ⊆ E \ ↑(opN cid) := by
  intro p hp
  have hp' := hp
  rw [LawfulSet.mem_diff] at hp'
  rw [LawfulSet.mem_diff]
  exact ⟨hEc p hp, fun h => hp'.2 (escrowN_subseteq p (opN_subseteq cid p h))⟩

/-! ## The abstract state, finite -/

/-- The lookup of a finite map, as the model's state. -/
def kvOf (m : GMap w64 (List w8)) : KvS := fun k => m.lookup k

/-- The store's step on a finite map. -/
def kvStepM (i : KvI) (m : GMap w64 (List w8)) : GMap w64 (List w8) :=
  match i with
  | .put k v => m.insert k v
  | _ => m

theorem kvOf_kvStepM (i : KvI) (m : GMap w64 (List w8)) :
    kvOf (kvStepM i m) = (kvStep i (kvOf m)).1 := by
  cases i with
  | get k => rfl
  | scan k n => rfl
  | put k v =>
    funext k'
    simp only [kvOf, kvStepM, kvStep, GMap.lookup_insert_eq_iff]
    by_cases h : k' = k
    · subst h; simp
    · simp [h, Ne.symm h]

section ghost
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [G : GooseGlobalGS .hasLC GF] [π : NetProtoGS]

/-- Half of the abstract key-value state `σ` (the ghost variable `γ.kv` over a finite map whose
lookup is `σ`). One half is the store's (`own_state`), the other the replicas' (in their
invariant); `escrow_fire` updates both at an op's linearization point. -/
def kvHalf (γ : EpNames) (σ : KvS) : IProp GF :=
  iprop(∃ m : GMap w64 (List w8), ghostVar γ.kv (1 : Qp).half m ∗ ⌜kvOf m = σ⌝)

/-- The store's abstract state (remote's `RBase.sysState`): the store's half. -/
def own_state (γ : EpNames) (σ : KvS) : IProp GF := kvHalf γ σ

instance kvHalf_timeless (γ : EpNames) (σ : KvS) : Timeless (kvHalf (GF := GF) γ σ) := by
  unfold kvHalf; infer_instance

instance own_state_timeless (γ : EpNames) (σ : KvS) : Timeless (own_state (GF := GF) γ σ) := by
  unfold own_state; infer_instance

/-! ## Connection roles -/

/-- The registry: every registered connection's dialer gave up its fresh token (so a connection
is registered at most once); the client connections, and only they, have escrow names
(registered with the role). -/
def roleInv (γ : EpNames) : IProp GF :=
  iprop(∃ (M : GMap Nat ConnRole) (N : GMap Nat EscNames), ghostMapAuth γ.roles 1 M ∗
    ghostMapAuth γ.escrows 1 N ∗
    ⌜∀ cid, (N.lookup cid).isSome ↔ ∃ c i, M.lookup cid = some (.client c i)⌝ ∗
    [∗map] cid ↦ _r ∈ M, connFresh cid false)

/-- Connection `cid` has role `r` (persistent). -/
def roleElem (γ : EpNames) (cid : Nat) (r : ConnRole) : IProp GF :=
  ghostMapElem γ.roles cid .discard r

instance roleElem_persistent (γ : EpNames) (cid : Nat) (r : ConnRole) :
    Persistent (roleElem (GF := GF) γ cid r) := by
  unfold roleElem; infer_instance

/-- The escrow of client connection `cid` has names `nm` (persistent). -/
def escrowNames (γ : EpNames) (cid : Nat) (nm : EscNames) : IProp GF :=
  ghostMapElem γ.escrows cid .discard nm

instance escrowNames_persistent (γ : EpNames) (cid : Nat) (nm : EscNames) :
    Persistent (escrowNames (GF := GF) γ cid nm) := by
  unfold escrowNames; infer_instance

/-! ## The escrow -/

/-- The update of an op with input `i` and postcondition `Φ` of its output: remote's `lin` of the
store (one-shot; a read's is fired once here too). -/
def opU (γ : EpNames) (i : KvI) (Φ : KvO → IProp GF) : IProp GF :=
  iprop(|={⊤ \ epEop, ∅}=> ∃ σ, own_state γ σ ∗
    (own_state γ (kvStep i σ).1 ={∅, ⊤ \ epEop}=∗ Φ (kvStep i σ).2))

/-- The op on connection `cid` linearized with output `o` (persistent): the replicas' fired map
has `cid ↦ o`, and the op's escrow's fire state is `some o` (discarded). The second part is what
excludes the escrow's pending arm (which owns the fire state whole). -/
def fired (γ : EpNames) (cid : Nat) (o : KvO) : IProp GF :=
  iprop(ghostMapElem γ.fired cid .discard o ∗
    ∃ nm : EscNames, escrowNames γ cid nm ∗ dghostVar nm.2 DFrac.discard (some o))

instance fired_persistent (γ : EpNames) (cid : Nat) (o : KvO) :
    Persistent (fired (GF := GF) γ cid o) := by
  unfold fired; infer_instance

/-- The authority of the fired outputs, `F` (the replicas', in their invariant): a connection's op
fires at most once, when its number is not in `F`. -/
def firedAuth (γ : EpNames) (F : GMap Nat KvO) : IProp GF :=
  ghostMapAuth γ.fired 1 F

/-- The escrow of the op on connection `cid` (input `i`, postcondition `Φ`, names `nm`): pending
(its update, and the fire state whole at `none`), or fired with output `o` (`fired γ cid o`),
holding `Φ o` until claimed, then the claim token. -/
def opInv (γ : EpNames) (cid : Nat) (i : KvI) (Φ : KvO → IProp GF) (nm : EscNames) : IProp GF :=
  iprop((opU γ i Φ ∗ dghostVar nm.2 (DFrac.own 1) (none : Option KvO)) ∨
    ∃ o : KvO, fired γ cid o ∗ (Φ o ∨ token nm.1))

/-- Connection `cid` is client `c`'s op with input `i` (meeting the input premise), with its
escrow (persistent): what a replica learns from the bytes of a client connection. -/
def clientConn (γ : EpNames) (cid : Nat) (c : w64) (i : KvI) : IProp GF :=
  iprop(⌜inPre i⌝ ∗ roleElem γ cid (.client c i) ∗ ∃ nm : EscNames, escrowNames γ cid nm ∗
    ∃ Φ, inv (opN cid) (opInv γ cid i Φ nm))

instance clientConn_persistent (γ : EpNames) (cid : Nat) (c : w64) (i : KvI) :
    Persistent (clientConn (GF := GF) γ cid c i) := by
  unfold clientConn; infer_instance

/-- The op's claim on its escrow (exclusive): the claim token and the escrow with the op's own
`Φ`. -/
def escrowClaim (γ : EpNames) (cid : Nat) (i : KvI) (Φ : KvO → IProp GF) : IProp GF :=
  iprop(∃ nm : EscNames, escrowNames γ cid nm ∗ token nm.1 ∗ inv (opN cid) (opInv γ cid i Φ nm))

theorem fired_agree (γ : EpNames) (cid : Nat) (o o' : KvO) :
    fired (GF := GF) γ cid o -∗ fired γ cid o' -∗ ⌜o = o'⌝ := by
  unfold fired
  iintro ⟨H1, -⟩ ⟨H2, -⟩
  icombine H1 H2 gives %H
  ipureintro; exact H.2

/-- A fired op's escrow state is `some o` (excluding the pending arm, which owns it whole). -/
theorem fired_pending_false (γ : EpNames) (cid : Nat) (o : KvO) (nm : EscNames) :
    fired (GF := GF) γ cid o -∗ escrowNames γ cid nm -∗
      dghostVar nm.2 (DFrac.own 1) (none : Option KvO) -∗ False := by
  unfold fired escrowNames
  iintro ⟨-, %nm2, H2, Hs2⟩ H1 Hs
  icombine H1 H2 gives %H
  obtain ⟨-, rfl⟩ := H
  icombine Hs Hs2 gives %H
  cases H.2

/-- A fired op is in the fired map. -/
theorem fired_auth_lookup (γ : EpNames) (cid : Nat) (o : KvO) (F : GMap Nat KvO) :
    fired (GF := GF) γ cid o -∗ firedAuth γ F -∗ firedAuth γ F ∗ ⌜F.lookup cid = some o⌝ := by
  unfold fired firedAuth
  iintro ⟨H1, -⟩ HF
  icombine HF H1 gives %H
  iframe HF
  ipureintro; exact H

/-- `opInv` with its binders at the type `KvO` (so that instances on `fired` are found after
destructuring). -/
theorem opInv_eq (γ : EpNames) (cid : Nat) (i : KvI) (Φ : KvO → IProp GF) (nm : EscNames) :
    opInv γ cid i Φ nm = iprop((opU γ i Φ ∗ dghostVar nm.2 (DFrac.own 1) (none : Option KvO)) ∨
      ∃ o : KvO, fired γ cid o ∗ (Φ o ∨ token nm.1)) := rfl

/-- `Op` registers its connection (from the dialer's fresh token) as client `c`'s op with input
`i` (meeting the input premise), depositing its update in a fresh escrow; it keeps the claim. -/
theorem escrow_register (γ : EpNames) (E : CoPset) (cid : Nat) (c : w64) (i : KvI)
    (Φ : KvO → IProp GF) (hE : ↑roleN ⊆ E) :
    ⊢ ⌜inPre i⌝ -∗ inv roleN (roleInv γ) -∗ connFresh cid false -∗ opU γ i Φ ={E}=∗
      clientConn γ cid c i ∗ escrowClaim γ cid i Φ := by
  iintro %hpre #Hrole Hfr HU
  imod token_alloc (GF := GF) with ⟨%γt, Htok⟩
  imod dghostVar_alloc (GF := GF) (none : Option KvO) with ⟨%γs, Hst⟩
  let nm : EscNames := (γt, γs)
  iinv Hrole with Hi Hclose
  unfold roleInv
  icases Hi with ⟨%M, %N, >HM, >HN, >%HMN, >Hfs⟩
  cases hM : M.lookup cid with
  | some r =>
    icases (BigSepM.bigSepM_delete (show get? M cid = some r from hM)).1 $$ Hfs with ⟨Hf2, -⟩
    iexfalso
    iapply (connFresh_excl (Gg := G) cid false)
    isplitl [Hfr]
    · iexact Hfr
    · iexact Hf2
  | none =>
    have hN : N.lookup cid = none := by
      cases h : N.lookup cid with
      | none => rfl
      | some x =>
        obtain ⟨c', i', h'⟩ := (HMN cid).1 (by simp [h])
        simp [hM] at h'
    imod ghost_map_insert_persist cid (ConnRole.client c i) hM $$ HM with ⟨HM, #Hre⟩
    imod ghost_map_insert_persist cid nm hN $$ HN with ⟨HN, #Hne⟩
    imod Hclose $$ [HM HN Hfs Hfr] with -
    · inext
      iexists M.insert cid (ConnRole.client c i), N.insert cid nm
      iframe HM HN
      isplitr
      · ipureintro
        intro k
        by_cases hk : cid = k
        · subst hk; simp
        · simp only [GMap.lookup_insert_eq_iff, hk, ite_false]
          exact HMN k
      iapply (BigSepM.bigSepM_insert (show get? M cid = none from hM)).2
      iframe
    imod inv_alloc (opN cid) E (opInv γ cid i Φ nm) $$ [HU Hst] with #Hinv
    · inext
      unfold opInv
      ileft
      iframe
    imodintro
    unfold clientConn escrowClaim roleElem escrowNames
    isplitr
    · isplitr
      · ipureintro; exact hpre
      iframe #
    iexists nm
    iframe #
    iexact Htok

/-- The replica that executes the op of connection `cid` first (its number not yet fired, `F`):
from the replicas' half of the abstract state `σ`, the op linearizes (its update fires): the state
becomes `σ'` with the output `o` of the model's step, the replicas' half is updated, `o` is
recorded (in the fired map, and in the escrow's fire state, discarded; the escrow keeps `Φ o`) and
the persistent witness `fired γ cid o` comes out. At any mask with the escrows and `⊤ ∖ epEop` (the
update's outer mask); the credit strips the later of the escrow's invariant. -/
theorem escrow_fire (γ : EpNames) (E : CoPset) (cid : Nat) (c : w64) (i : KvI) (σ : KvS)
    (F : GMap Nat KvO) (hE : ↑escrowN ⊆ E) (hEc : ⊤ \ epEop ⊆ E) (hF : F.lookup cid = none) :
    ⊢ clientConn (GF := GF) γ cid c i -∗ firedAuth γ F -∗ kvHalf γ σ -∗ £ 1 ={E}=∗
      ∃ σ' o, ⌜(kvScan w8).step σ i σ' o⌝ ∗ kvHalf γ σ' ∗
        firedAuth γ (F.insert cid o) ∗ fired γ cid o := by
  unfold clientConn
  iintro ⟨%hpre, #Hre, %nm, #Hnm, %Φ, #Hinv⟩ HF Hkv Hlc
  have hsub : (↑(opN cid) : CoPset) ⊆ E := fun p h => hE p (opN_subseteq cid p h)
  have hcl := epEop_diff_opN cid hEc
  iinv Hinv with Hi Hclose
  imod lc_fupd_elim_later (E := E \ ↑(opN cid)) $$ Hlc Hi with Hi
  rw [opInv_eq]
  icases Hi with (⟨HU, Hst⟩ | ⟨%o1, #Hf1, Hr⟩)
  rotate_left
  · ihave ⟨HF, %Hl⟩ := fired_auth_lookup $$ Hf1 HF
    rw [hF] at Hl; cases Hl
  unfold opU
  imod fupd_mask_subseteq (PROP := IProp GF) hcl with Hmask
  imod HU with ⟨%σa, Hown, Hcommit⟩
  unfold own_state kvHalf
  icases Hown with ⟨%ma, Hma, %Hma⟩
  icases Hkv with ⟨%m, Hm, %Hm⟩
  icombine Hm Hma gives %Heq
  obtain ⟨-, rfl⟩ := Heq
  subst Hm Hma
  imod ghostVar_update_halves (kvStepM i m) γ.kv m m $$ Hm Hma with ⟨Hm, Hma⟩
  imod Hcommit $$ [Hma] with HΦ
  · iexists kvStepM i m
    iframe Hma
    ipureintro; exact kvOf_kvStepM i m
  imod Hmask
  unfold firedAuth
  imod ghost_map_insert_persist cid (kvStep i (kvOf m)).2 hF $$ HF with ⟨HF, #Hfo⟩
  imod dghostVar_update (some (kvStep i (kvOf m)).2) nm.2 none $$ Hst with Hst
  imod dghostVar_persist nm.2 1 (some (kvStep i (kvOf m)).2) $$ Hst with #Hst
  ihave #Hfired : fired γ cid (kvStep i (kvOf m)).2 $$ []
  · unfold fired
    iframe #
  imod Hclose $$ [HΦ] with -
  · inext
    iright
    iexists (kvStep i (kvOf m)).2
    iframe #
    ileft; iexact HΦ
  imodintro
  iexists (kvStep i (kvOf m)).1, (kvStep i (kvOf m)).2
  isplitr
  · ipureintro; exact kvStep_spec i (kvOf m)
  iframe #
  isplitl [Hm]
  · iexists kvStepM i m; iframe Hm; ipureintro; exact kvOf_kvStepM i m
  iexact HF

/-- `Op`, on a reply carrying `fired γ cid o`: its claim gives the update's postcondition of `o`
(the credit strips the escrow's later). -/
theorem escrow_claim (γ : EpNames) (E : CoPset) (cid : Nat) (i : KvI) (Φ : KvO → IProp GF)
    (o : KvO) (hE : ↑escrowN ⊆ E) :
    ⊢ escrowClaim γ cid i Φ -∗ fired γ cid o -∗ £ 1 ={E}=∗ Φ o := by
  unfold escrowClaim
  iintro ⟨%nm, #Hnm, Htok, #Hinv⟩ #Hfired Hlc
  have hsub : (↑(opN cid) : CoPset) ⊆ E := fun p h => hE p (opN_subseteq cid p h)
  iinv Hinv with Hi Hclose
  imod lc_fupd_elim_later (E := E \ ↑(opN cid)) $$ Hlc Hi with Hi
  rw [opInv_eq]
  icases Hi with (⟨HU, Hst⟩ | ⟨%o2, #Hf2, Hr⟩)
  · iexfalso
    iapply fired_pending_false $$ Hfired Hnm Hst
  · ihave %Heq := fired_agree $$ Hfired Hf2
    subst Heq
    icases Hr with (HΦ | Htok2)
    · imod Hclose $$ [Htok] with -
      · inext
        iright
        iexists o
        iframe Hfired
        iright; iexact Htok
      imodintro
      iexact HΦ
    · iexfalso
      iapply token_exclusive $$ Htok Htok2

end ghost

/-! ## The protocols of a replica's peer/client address -/

/-- The servers' addresses (`ServerAddrs()`, `examples/epaxosnet/kit.go`): server id `1 + j` at
`j`; the master is server 1. -/
def serverAddrs : List GoString :=
  [go!"127.0.0.1:7501", go!"127.0.0.1:7502", go!"127.0.0.1:7503", go!"127.0.0.1:7504",
   go!"127.0.0.1:7505", go!"127.0.0.1:7506"]

/-- The replica peer/client addresses: servers 2..6 (`Op` dials `ServerAddrs()[1 + c mod
NReplicas]` for client `c`). -/
def replicaAddrs : List GoString := serverAddrs.drop 1

section protos
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [G : GooseGlobalGS .hasLC GF] [π : NetProtoGS]

/-- What client `c`'s op (input `i`) writes on its connection `cid`: a prefix of the `PROPOSE` tag
and its `Propose`; the connection is registered as that op (`clientConn`). -/
def clientDialOk (γ : EpNames) (cid : Nat) (c : w64) (i : KvI) (bs : List w8) : IProp GF :=
  iprop(clientConn γ cid c i ∗ ⌜bs <+: proposeBytes c i⌝)

/-- What a replica writes back on client connection `cid`: a prefix of one
`ProposeReplyTS{OK: TRUE, CommandId: 0, Value: v, Timestamp: ts}` whose value is the fired
output's (`replyValOk`; below `2 ^ 16` bytes, so its length field is exact). -/
def clientReplyOk (γ : EpNames) (cid : Nat) (bs : List w8) : IProp GF :=
  iprop(∃ (o : KvO) (v : List w8) (ts : w64), fired γ cid o ∗
    ⌜replyValOk o v ∧ v.length < 2 ^ 16 ∧ bs <+: encProposeReplyTS okTRUE (W32 0) v ts⌝)

/-- The protocol of what dialers write to the replica address `a`: nothing yet (any
connection), or by the connection's registered role, a peer's stream (`peerStreamOk`) or a client
op's proposal. -/
def repDialP (γ : EpNames) (a : GoString) : Proto GF := fun cid bs =>
  iprop(⌜bs = []⌝ ∨ ∃ r, roleElem γ cid r ∗
    match r with
    | .peer d => peerStreamOk γ a d false cid bs
    | .client c i => clientDialOk γ cid c i bs)

/-- The protocol of what the replica at address `a` writes back: nothing yet (any connection:
the acceptor creates its writer before the op has fired, `bufio.NewWriter` needs the protocol of
`[]`), or by the connection's role, to a peer (`peerStreamOk`) or the reply to a client op. -/
def repAccP (γ : EpNames) (a : GoString) : Proto GF := fun cid bs =>
  iprop(⌜bs = []⌝ ∨ ∃ r, roleElem γ cid r ∗
    match r with
    | .peer d => peerStreamOk γ a d true cid bs
    | .client _ _ => clientReplyOk γ cid bs)

/-- What `Op` needs, shared (persistent): every replica address's protocols and the role
registry. -/
def clientInvs (γ : EpNames) : IProp GF :=
  iprop(([∗list] a ∈ replicaAddrs, addrProto a (repDialP γ a) (repAccP γ a)) ∗
    inv roleN (roleInv γ))

instance clientInvs_persistent (γ : EpNames) : Persistent (clientInvs (GF := GF) γ) := by
  unfold clientInvs; infer_instance

end protos

end Perennial.github_com.imdea_software.swiftpaxos_epaxos
