/-
The master's registration and the replicas' ids (`notes/stage1-plan.md`, "Design details":
Registration and replica ids), over the global ghost state:

* **The addresses** of the deployment (`ServerAddrs()`, `examples/epaxosnet/kit.go`):
  server `k` (`Server(k)`; k = 1 the master, 2..6 the replicas) is at `127.0.0.1:(7500+k)`;
  replica `k` registers `("127.0.0.1", 7500 + k)`, i.e. its peer/client address `peerAddrOf k`
  (`serverAddrs[k - 1]`), and serves rpc on `rpcAddrOf k` (`127.0.0.1:(8500+k)`); the master is
  `masterAddr` (`127.0.0.1:7501`, listening on the wildcard `":7501"`).
* **The final node list** (write-once): `listUnset γ` (exclusive, the master's: the right to fix
  the list) and `listFinal γ L` (persistent: the list is `L`, a permutation of the five replica
  peer addresses `replicaAddrs`). The master fixes it once its `nodeList` holds five entries
  (`listFix`); every reply of `Master.Register` with `Ready` carries `listFinal γ L` for the
  `NodeList` it sends.
* **The exchange** (`regXInv γ R`, an invariant at `regXN`): for each replica id `i < 5`, its
  slot holds `idTok γ i` and the replica's start resources `R i` (a parameter: what the protocol
  layer gives replica `i`; the run's choice is `repStart`: the framework's `repFwStart` and the
  protocol layer's `epRepStart`) until node `k`
  claims it with its node token `nodeTok γ k` and the final list `L` with `L[i] = peerAddrOf k`
  (`regX_claim`). Node tokens are exclusive and the addresses distinct, so each slot is claimed
  at most once, by the node the final list puts there.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Interface.Client
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Interface.EpaxosGhost
public import Perennial.Proof.fmt

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net github_com.imdea_software.swiftpaxos_epaxos.kvs

attribute [local instance] GooseGlobalGS.gooseInvGS

/-! ## The addresses -/

/-- The replica servers (`Server(k)`). -/
def replicaNodes : List Nat := [2, 3, 4, 5, 6]

/-- The master's address (server 1's). -/
def masterAddr : GoString := go!"127.0.0.1:7501"

/-- The servers' IP (`host(addrs[id-1])`, what `serve` passes to `register`). -/
def masterIp : GoString := go!"127.0.0.1"

theorem masterAddr_eq : masterAddr = masterIp ++ go!":" ++ go!"7501" := rfl

theorem masterAddr_server : serverAddrs[0]? = some masterAddr := rfl

/-- Replica `k`'s IP (`host(addrs[k-1])`). -/
def replicaIp (_k : Nat) : GoString := go!"127.0.0.1"

/-- Replica `k`'s peer/client address (`ServerAddrs()[k - 1]`, port `7500 + k`): what it
registers with the master and what its peers and clients dial. -/
def peerAddrOf (k : Nat) : GoString := serverAddrs.getD (k - 1) []

/-- Replica `k`'s rpc address (`ip:(port + 1000)`, `serve`). -/
def rpcAddrOf (k : Nat) : GoString := replicaIp k ++ go!":" ++ fmt.decimal (8500 + k)

/-- The replicas' rpc addresses. -/
def replicaRpcAddrs : List GoString := replicaNodes.map rpcAddrOf

theorem replicaAddrs_eq : replicaAddrs = replicaNodes.map peerAddrOf := by decide

/-- What `Register` formats (`fmt.Sprintf("%s:%d", Addr, Port)`) for node `k`'s arguments is
its peer address. -/
theorem peerAddrOf_fmt (k : Nat) (hk : k ∈ replicaNodes) :
    peerAddrOf k = replicaIp k ++ go!":" ++ fmt.decimal (7500 + k) := by
  simp only [replicaNodes, List.mem_cons, List.mem_nil_iff, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl <;>
    simp [fmt.decimal, fmt.decimalNat_of_ge, fmt.decimalNat_of_lt, fmt.digitByte, peerAddrOf,
      replicaIp, serverAddrs]

theorem peerAddrOf_inj (k k' : Nat) (hk : k ∈ replicaNodes) (hk' : k' ∈ replicaNodes)
    (h : peerAddrOf k = peerAddrOf k') : k = k' := by
  simp only [replicaNodes, List.mem_cons, List.mem_nil_iff, or_false] at hk hk'
  rcases hk with rfl | rfl | rfl | rfl | rfl <;> rcases hk' with rfl | rfl | rfl | rfl | rfl <;>
    first | rfl | (exfalso; revert h; decide)

/-- A final node list: five distinct registered replica peer addresses, i.e. a permutation of
`replicaAddrs` (the master's `Register` admits only those: its precondition). -/
def finalListOk (L : List GoString) : Prop := L.Perm replicaAddrs

/-! ## The ghost state -/

/-- The namespace of the registration exchange. -/
def regXN : Namespace := ndot epN "registry"

section ghost
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [G : GooseGlobalGS .hasLC GF] [π : NetProtoGS]

/-- The master's right to fix the final node list (exclusive). -/
def listUnset (γ : EpNames) : IProp GF :=
  ghostMapAuth γ.master.list 1 (∅ : GMap Unit (List GoString))

/-- The final node list is `L` (persistent). -/
def listFinal (γ : EpNames) (L : List GoString) : IProp GF :=
  iprop(ghostMapElem γ.master.list () .discard L ∗ ⌜finalListOk L⌝)

/-- Node `k`'s token (exclusive): node `k` trades it for its replica id. -/
def nodeTok (γ : EpNames) (k : Nat) : IProp GF :=
  ghostMapElem γ.master.nodes k (DFrac.own 1) ()

/-- Replica id `i`'s token (exclusive): the right to run replica `i`. -/
def idTok (γ : EpNames) (i : Nat) : IProp GF :=
  ghostMapElem γ.rep.ids i (DFrac.own 1) ()

instance listFinal_persistent (γ : EpNames) (L : List GoString) :
    Persistent (listFinal (GF := GF) γ L) := by
  unfold listFinal; infer_instance

instance listUnset_timeless (γ : EpNames) : Timeless (listUnset (GF := GF) γ) := by
  unfold listUnset; infer_instance
instance listFinal_timeless (γ : EpNames) (L : List GoString) : Timeless (listFinal (GF := GF) γ L) := by
  unfold listFinal; infer_instance
instance nodeTok_timeless (γ : EpNames) (k : Nat) : Timeless (nodeTok (GF := GF) γ k) := by
  unfold nodeTok; infer_instance
instance idTok_timeless (γ : EpNames) (i : Nat) : Timeless (idTok (GF := GF) γ i) := by
  unfold idTok; infer_instance

/-- Slot `i` of the exchange: unclaimed (the id token and the replica's start resources), or
claimed by node `k`, which the final list puts at `i` (its node token stays here). -/
def regSlot (γ : EpNames) (R : Nat → IProp GF) (i : Nat) : IProp GF :=
  iprop((idTok γ i ∗ R i) ∨
    ∃ (L : List GoString) (k : Nat), listFinal γ L ∗ ⌜k ∈ replicaNodes ∧ L[i]? = some (peerAddrOf k)⌝ ∗
      nodeTok γ k)

/-- The exchange invariant, for replica start resources `R`: a slot per replica id. -/
def regXInv (γ : EpNames) (R : Nat → IProp GF) : IProp GF :=
  iprop([∗list] i ∈ List.range nRep, regSlot γ R i)

/-- Replica `i`'s framework start resources (for `repStart γ i`, with `nRep` replicas): for every
other replica `j`, the framework's half of the (empty) list of messages from `i` to `j` and the
right to mint the delivery tokens of `j`'s messages at `i`; the dial tokens of `i` to every lower
id and its own (`dialTok γ i i`, unused by `peerConn`: the framework's own names); the authorities
of the replica's client-writer and reply-token maps (empty). (The other halves of the sent lists
are the protocol layer's.) (Declared here rather than in `Epaxos/Interface/Replica.lean`, which
imports this file, so that `repStart` can name it.) -/
def repFwStart (γ : EpNames) (i : Nat) : IProp GF :=
  iprop(([∗list] j ∈ List.range nRep,
      if j = i then iprop(True) else iprop(sentHalf γ i j [] ∗ delivFrom γ i j 0)) ∗
    ([∗list] j ∈ List.range (i + 1), dialTok γ i j) ∗
    ghostMapAuth (γ.rep.cwriters i) 1 (∅ : GMap Loc Nat) ∗
    ghostMapAuth (γ.rep.replies i) 1 (∅ : GMap Loc Unit))

/-- What replica `i` gets with its id at registration, besides `idTok γ i`: the framework's start
resources (`repFwStart`) and the protocol layer's (`epRepStart`,
`Epaxos/Interface/EpaxosGhost.lean`). -/
def repStart (γ : EpNames) (i : Nat) : IProp GF := iprop(repFwStart γ i ∗ epRepStart γ i)

/-! ## Laws -/

/-- The final list agrees. -/
theorem listFinal_agree (γ : EpNames) (L L' : List GoString) :
    listFinal (GF := GF) γ L -∗ listFinal γ L' -∗ ⌜L = L'⌝ := by
  unfold listFinal
  iintro ⟨H1, -⟩ ⟨H2, -⟩
  iapply ghostMapElem_agree $$ H1 H2

/-- A final list is a permutation of the replica peer addresses. -/
theorem listFinal_ok (γ : EpNames) (L : List GoString) :
    listFinal (GF := GF) γ L -∗ ⌜finalListOk L⌝ := by
  unfold listFinal
  iintro ⟨-, %h⟩
  ipureintro; exact h

/-- Once fixed, the list cannot be fixed again. -/
theorem listUnset_listFinal (γ : EpNames) (L : List GoString) :
    listUnset (GF := GF) γ -∗ listFinal γ L -∗ False := by
  unfold listFinal listUnset
  iintro Ha ⟨He, -⟩
  icombine He Ha gives %H
  simp at H

/-- The master fixes the final list (once). -/
theorem listFix (γ : EpNames) (L : List GoString) (hL : finalListOk L) :
    listUnset (GF := GF) γ ==∗ listFinal γ L := by
  unfold listFinal listUnset
  iintro Ha
  imod ghost_map_insert_persist () L (by simp) $$ Ha with ⟨-, He⟩
  imodintro
  iframe He
  ipureintro; exact hL

theorem nodeTok_excl (γ : EpNames) (k : Nat) : nodeTok (GF := GF) γ k -∗ nodeTok γ k -∗ False := by
  unfold nodeTok
  iintro H1 H2
  ihave %h := ghostMapElem_ne _ k k _ () () $$ H1 H2
  exact absurd rfl h

theorem idTok_excl (γ : EpNames) (i : Nat) : idTok (GF := GF) γ i -∗ idTok γ i -∗ False := by
  unfold idTok
  iintro H1 H2
  ihave %h := ghostMapElem_ne _ i i _ () () $$ H1 H2
  exact absurd rfl h

/-- (Internal.) Whole elements for the keys of `l`, from an authority without them. -/
theorem toks_alloc (γ : GName) (l : List Nat) (m : GMap Nat Unit) (hl : l.Nodup)
    (hm : ∀ k ∈ l, m.lookup k = none) :
    ⊢ (ghostMapAuth γ 1 m : IProp GF) ==∗ [∗list] k ∈ l, ghostMapElem γ k (DFrac.own 1) () := by
  induction l generalizing m with
  | nil => iintro -; imodintro; iapply BigSepL.bigSepL_nil.2; iempintro
  | cons k l ih =>
    have hm' : ∀ k' ∈ l, (m.insert k ()).lookup k' = none := by
      intro k' hk'
      have hne : k ≠ k' := fun h => (List.nodup_cons.mp hl).1 (h ▸ hk')
      exact (GMap.lookup_insert_ne m () hne).trans (hm k' (List.mem_cons_of_mem k hk'))
    iintro Ha
    imod ghost_map_insert k () (hm k (by simp)) $$ Ha with ⟨Ha, Hk⟩
    imod ih (m.insert k ()) (List.nodup_cons.mp hl).2 hm' $$ Ha with Hl
    imodintro
    iapply BigSepL.bigSepL_cons.2
    iframe Hk Hl

/-- The registry's ghost state, fresh: the names, and for any `γ` with those names, the
master's `listUnset`, every replica node's token and every replica id's token. (The start then
allocates `regXInv` from the id tokens with `regXInv_alloc`.) -/
theorem registry_alloc :
    ⊢ |==> ∃ (mn : MasterNames) (ids : GName), ∀ γ : EpNames,
      ⌜γ.master = mn ∧ γ.rep.ids = ids⌝ -∗
        listUnset (GF := GF) γ ∗ ([∗list] k ∈ replicaNodes, nodeTok γ k) ∗
        ([∗list] i ∈ List.range nRep, idTok γ i) := by
  imod ghost_map_alloc_empty (GF := GF) (K := Unit) (V := List GoString) with ⟨%γl, Hl⟩
  imod ghost_map_alloc_empty (GF := GF) (K := Nat) (V := Unit) with ⟨%γn, Hn⟩
  imod ghost_map_alloc_empty (GF := GF) (K := Nat) (V := Unit) with ⟨%γi, Hi⟩
  imod toks_alloc γn replicaNodes ∅ (by decide) (by simp) $$ Hn with Hn
  imod toks_alloc γi (List.range nRep) ∅ (List.nodup_range) (by simp) $$ Hi with Hi
  imodintro
  iexists ⟨γl, γn⟩, γi
  iintro %γ %h
  obtain ⟨h1, h2⟩ := h
  unfold listUnset nodeTok idTok
  rw [h1, h2]
  iframe Hl Hn Hi

/-- The exchange's invariant, from the id tokens and the replicas' start resources. -/
theorem regXInv_alloc (γ : EpNames) (R : Nat → IProp GF) (E : CoPset) :
    ([∗list] i ∈ List.range nRep, idTok γ i ∗ R i) ={E}=∗ inv regXN (regXInv γ R) := by
  iintro Hs
  iapply inv_alloc
  inext
  unfold regXInv
  iapply BigSepL.bigSepL_mono_of_forall ?_ $$ Hs
  intro _ i
  unfold regSlot
  iintro H
  ileft
  iexact H

/-- Node `k` (2..6), with its token and the final list `L` that puts its peer address at `i`,
claims replica id `i` and the replica's start resources (the credit strips the later of the
invariant, as `R` need not be timeless). -/
theorem regX_claim (γ : EpNames) (R : Nat → IProp GF) (E : CoPset) (k i : Nat)
    (L : List GoString) (hE : ↑regXN ⊆ E) (hk : k ∈ replicaNodes)
    (hi : L[i]? = some (peerAddrOf k)) :
    ⊢ inv regXN (regXInv γ R) -∗ nodeTok γ k -∗ listFinal γ L -∗ £ 1 ={E}=∗
      idTok γ i ∗ R i := by
  iintro #Hinv Hk #HL Hlc
  ihave %hok := listFinal_ok γ L $$ HL
  have hlen : L.length = nRep := by
    rw [hok.length_eq]; rfl
  have hiR : (List.range nRep)[i]? = some i := by
    have : i < L.length := (List.getElem?_eq_some_iff.mp hi).1
    rw [List.getElem?_range (by omega)]
  iinv Hinv with Hi Hclose
  imod lc_fupd_elim_later $$ Hlc Hi with Hi
  unfold regXInv
  icases BigSepL.bigSepL_insert_acc hiR $$ Hi with ⟨Hs, Hback⟩
  unfold regSlot
  icases Hs with (⟨Ht, HR⟩ | ⟨%L', %k', #HL', %hkk', Hk'⟩)
  · imod Hclose $$ [Hback Hk] with -
    · inext
      have hlt : i < (List.range nRep).length := (List.getElem?_eq_some_iff.mp hiR).1
      have hset : (List.range nRep).set i i = List.range nRep := by
        have h := List.set_getElem_self hlt
        simpa using h
      ihave Hb := Hback $$ %i
      rw [hset]
      iapply Hb
      iright
      iexists L, k
      iframe HL Hk
      ipureintro; exact ⟨hk, hi⟩
    imodintro
    iframe Ht HR
  · obtain ⟨hk', hi'⟩ := hkk'
    ihave %hLL := listFinal_agree γ L L' $$ HL HL'
    subst hLL
    have hkk : k = k' := peerAddrOf_inj k k' hk hk' (Option.some.inj (hi.symm.trans hi'))
    subst hkk
    iexfalso
    iapply nodeTok_excl γ k $$ Hk Hk'

end ghost

end Perennial.github_com.imdea_software.swiftpaxos_epaxos
