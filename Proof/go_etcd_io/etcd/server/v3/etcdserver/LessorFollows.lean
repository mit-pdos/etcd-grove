/-
**The per-member lessor law** (auth-lease S4 item 7, the Freeze's §5, `notes/auth-lease-s4-freeze.md`; frozen text
`notes/auth-lease-s4-frozen.lean.txt` §5): given a floor `F` of a member's store, its lessor has a lower bound `m`
such that every lessor snapshot from `m` on holds `k` on the live lease `id` whenever the KV state of the clients'
view keeps `k` on `id` at every revision from `F`'s on.

- `leaseKeptIn`, `lsHolds`, `lessorLawMask`: the law's vocabulary (frozen; `lessorLawMask` with the tie's and the
  lessor's reader namespaces added, the form its docstring allows);
- `srvKVCoreM_nx_st`/`srvKVCoreM_st` (S5): the KV state of the clients' view is the KV model of the committed log,
  which extends every log with the store's witness (`E.Nx`); at the lease mode `none` that model attaches no lease;
- `lessor_keys_of_read`: the law. In a cluster that grants leases (`E.lg = true`), the lessor-window tie's
  observation (`srvApi.tie_obs`) gives `m`, its law at each later index (`srvApi.tie_law`) two committed logs whose
  common items the snapshot holds, and S5 places both under the view's state. At `E.lg = false` (the lease mode
  `none`) the committed model attaches no key to a lease, so the hypothesis is false. The auth-off mode is the same
  argument (its client half exists only at `E.lg = false`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.ReadOn
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.KVStoreApi
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.SnapRecvOn
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.KVModelRestore

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3 go_etcd_io.etcd.server.v3.etcdserver

/-! ## The law's vocabulary -/

section lawpure
variable [GooseExts]

/-- §5 (rev 2) **`k` is on the lease `id` at every revision of the KV state `σ` from `r₀` on** (pure,
in the client's vocabulary: `σ`'s revisions keep each key-value's lease, so `leaseItemsOf (σ.at r).kvs`
is the lessor's item map at revision `r`). -/
def leaseKeptIn (σ : KVState) (r₀ : Nat) (id : w64) (k : GoString) : Prop :=
  r₀ ≤ σ.rev ∧ ∀ r : Nat, r₀ ≤ r → r ≤ σ.rev →
    (mvcc.leaseItemsOf (σ.at r).kvs).lookup ⟨k⟩ = some id

/-- §5: a lessor snapshot holds `k` on the live lease `id` (the S4 probe's `leaseHoldsFrom`, at one
index). -/
def lsHolds (σ : lease.LSnap) (id : w64) (k : GoString) : Prop :=
  (∃ l, σ.1.lookup id = some l) ∧ σ.2.1.lookup ⟨k⟩ = some id

/-- The state at a revision of a log's KV state, at the last revision of a non-empty prefix of the log, has the
prefix's items. -/
theorem kvStateOf_items_prefix (C L : mvcc.Log) (lt : LeaseTable) (hp : L <+: C) (hne : L ≠ []) :
    ((kvStateOf C lt).at (L.length - 1)).kvs = mvcc.stateAfter L := by
  have hlen : L.length ≤ C.length := hp.length_le
  have h0 : 0 < L.length := List.length_pos_iff.2 hne
  rw [kvStateOf_at_kvs C _ (by omega)]
  unfold mvcc.stateAt
  rw [show L.length - 1 + 1 = L.length by omega]
  obtain ⟨t, rfl⟩ := hp
  rw [List.take_left' rfl]

end lawpure

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]

/-- §5 (rev 3, review r3's R3-1; new vocabulary, exported with its body) **The namespaces the lessor law
opens**: the server's KV, raft and store invariants, and (auth-lease S4 item 7b F4, the form this docstring allowed)
the lessor-window tie's (`srvApi.winTieN`, which holds the lessor-index ↔ applied-revision tie) and the lessor's reader
invariant's (`lease.lessorRdN`, which the tie's law opens). A caller proves `lessorLawMask ⊆ Em` by unfolding, and only
needs its own namespaces disjoint from these. -/
def lessorLawMask : CoPset :=
  ↑kvN ∪ ↑srvRaftN ∪ ↑srvApi.kvsN ∪ ↑srvApi.winTieN ∪ ↑lease.lessorRdN

/-- §5 **The per-member lessor law** (statement; `lessor_keys_of_read`; rev 3). Given a floor `F` of the
member's own store (`srvApi.kvLogLb E.γs F`: the store applied `F`, whose revision is `F.length - 1`,
`kvStateOf_rev`; a read's result carries one at the log it read, `InvRead`'s `∃ log, srvApi.kvLogLb E.γs log ∗ …`), the member's lessor has a lower bound
`m`, and every lessor snapshot `σl` from `m` on holds `k` on the live lease `id` if the KV state `σ` the
caller's view holds (`etcdKV`) keeps `k` on `id` at every revision from `F`'s on. (Rev 3, review r2's S1:
rev 2's threshold `log.length` over `readLogOk γr c log` was false: `log` may extend what the member had
applied; the floor is member-local.)

Mode-generic (over `isServerReadM E.authOn`; L3). At auth off, or wherever `kvInv` holds the whole model
state, the law's proof must show the hypothesis contradictory or the conclusion direct; if it cannot, the
law is restated at `isServerReadM true` (a literal the mode gate counts) and comes back for review (r2's S6).

The mask: any `Em` containing `lessorLawMask` (r2's S4, r3's R3-1): the conclusion for an index pushed
after the law fired opens the invariant holding the lessor-index ↔ applied-revision tie (§5.4).

Why a member-local floor (r3's R3-4): the check the law serves reads this same member's lessor (a lease read
is served by the member it reaches, `nonissues/etcd-lease-checks-lagging-member.md`), so the threshold must be
a revision this member had applied; the driver gets `F` from its linearizable read at that member (barrier 2's
`client_range_on`, whose reply's log has revision `≥ r_put`). The proof
obligation this states (r2's S5): `σ` of `etcdKV` is the KV model of the committed log, and a member applies
only committed entries, so an entry a member has begun applying is in `σ` (its revision `≤ σ.rev`).

**L1 (option 1, approved by the user 2026-11-16; Freeze §8.4):** the member's cluster in raft's
no-snapshot mode (`clusterNoSnap`, a pure fact of the names, chosen at the cluster's allocation). It excludes
the snapshot `Ready` (`readySnap_mode`, L-r3), so `applySnapshot`'s `Recover` (which empties the lessor's
items before `kv.Restore` re-attaches them) and a restart's recovery never run: outside the mode the law is
false (`nonissues/etcd-lease-keys-mid-apply.md`, "A second window: after a snapshot"). Within an entry the
pair changes at most once, so `leaseKeptIn`'s two revisions around it cover the other window. -/
abbrev lessor_keys_of_read_stmt : Prop :=
  ∀ (s : Loc) (E : apply.AEnv GF) (γr : ReadNames) (F : mvcc.Log) (id : w64) (k : GoString),
  clusterNoSnap γr.raft.raft.cl →
  (isServerReadM E.authOn s E γr ∗ srvApi.kvLogLb E.γs F ⊢ |={⊤}=>
    ∃ m : Nat, lease.lessorLb (mvcc.api.mvccLeases E.γ) m ∗
      □ ∀ (i : Nat) (σl : lease.LSnap), ⌜m ≤ i⌝ -∗ lease.lessorAt (mvcc.api.mvccLeases E.γ) i σl -∗
        ∀ (Em : CoPset) (σ : KVState),
          ⌜lessorLawMask ⊆ Em⌝ -∗
          etcdKV γr.kv σ ={Em}=∗ etcdKV γr.kv σ ∗ ⌜leaseKeptIn σ (F.length - 1) id k → lsHolds σl id k⌝)

end defs

/-! ## S5: the clients' view is the committed model -/

section s5
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]

/-- **The clients' KV state is the committed model's** (S5): with the KV core in the mode `on`, the KV state `σ` of
the clients' view (`etcdKV`) is the KV state of a log `C`, the mode's model of the committed log; at the lease mode
`none` it attaches no lease (the mode's plain log from the lease-free start). -/
theorem srvKVCoreM_st (on : Bool) (E : apply.AEnv GF) (γr : ReadNames) (σ : KVState) (Em : CoPset)
    (hk : ↑kvN ⊆ Em) :
    ⊢ srvKVCoreM on E γr -∗ etcdKV γr.kv σ ={Em}=∗ etcdKV γr.kv σ ∗
      ⌜∃ (C : mvcc.Log) (lt : LeaseTable), σ = kvStateOf C lt ∧
        (γr.kv.lm = .none → mvcc.LogNoLease C)⌝ := by
  cases on
  · rw [srvKVCoreM_false]
    iintro #Hinvs Hc
    iunfold srvKVInvs at Hinvs
    icases Hinvs with ⟨#HkI, -⟩
    iunfold kvInv at HkI
    iinv HkI with >Hi Hclose
    icases Hi with ⟨%Lf, HLf, Hσ', %Hok', #Hw, HG⟩
    iunfold etcdKV at Hc
    ihave %Hag := ghostVar_agree γr.kv.st _ _ _ _ $$ Hσ' Hc
    imod Hclose $$ [HLf Hσ' HG] with -
    · inext; iexists Lf; iframe HLf Hσ' Hw HG; ipureintro; exact Hok'
    imodintro
    iunfold etcdKV
    iframe Hc
    ipureintro
    refine ⟨kvModel γr.kv Lf, kvLeases γr.kv Lf, Hag.symm, fun _ => ?_⟩
    rw [kvModel_offM _ Lf Hok'.1]
    exact (kvRaftOf_restorable _ _ _ Lf Hok'.1 Hok'.2.2.2.2.1.2).1
  · rw [srvKVCoreM_true]
    iintro #Hinvs Hc
    icases Hinvs with ⟨#HkI, -⟩
    iunfold kvInvOn at HkI
    iinv HkI with >Hi Hclose
    icases Hi with ⟨%Lf, HLf, Hσ', Hh, %Hok', #Hw, HG⟩
    iunfold etcdKV at Hc
    ihave %Hag := ghostVar_agree γr.kv.st _ _ _ _ $$ Hσ' Hc
    imod Hclose $$ [HLf Hσ' Hh HG] with -
    · inext; iexists Lf; iframe HLf Hσ' Hh Hw HG; ipureintro; exact Hok'
    imodintro
    iunfold etcdKV
    iframe Hc
    ipureintro
    refine ⟨kvModelOn γr.kv srvAuthSt0 Lf, kvLeasesOn γr.kv srvAuthSt0 Lf, Hag.symm, fun hlm => ?_⟩
    unfold kvModelOn
    exact (kvRaftOfOn_restorable _ _ (srvAuthSt0, γr.kv.log0, []) Lf (hlm ▸ Hok'.1)
      Hok'.2.2.2.2.2.1.2).1

/-- **A witnessed log is under the clients' KV state** (S5): with the KV core in the mode `on`, two logs with the
store's witness (`E.Nx`: the mode's models of committed raft prefixes) are non-empty prefixes of the log `C` whose
KV state is the clients' view's (`etcdKV`): the mode's model of the committed log, which extends every committed
prefix's (`srvRLog_lb`). -/
theorem srvKVCoreM_nx_st (on : Bool) (E : apply.AEnv GF) (γr : ReadNames) (L1 L2 : mvcc.Log) (σ : KVState)
    (Em : CoPset) (hk : ↑kvN ⊆ Em) (hr : ↑srvRaftN ⊆ Em \ ↑kvN) :
    ⊢ srvKVCoreM on E γr -∗ E.Nx L1 -∗ E.Nx L2 -∗ etcdKV γr.kv σ ={Em}=∗ etcdKV γr.kv σ ∗
      ⌜∃ (C : mvcc.Log) (lt : LeaseTable), σ = kvStateOf C lt ∧ L1 <+: C ∧ L1 ≠ [] ∧ L2 <+: C ∧ L2 ≠ []⌝ := by
  cases on
  · rw [srvKVCoreM_false]
    iintro #Hinvs H1 H2 Hc
    iunfold srvKVInvs at Hinvs
    icases Hinvs with ⟨#HkI, -, #HrI, -, -, %HNx, -⟩
    rw [HNx]
    iunfold kvNxOff at H1
    iunfold kvNxOff at H2
    icases H1 with ⟨%A1, #HA1, %hA1⟩
    icases H2 with ⟨%A2, #HA2, %hA2⟩
    iunfold kvInv at HkI
    iinv HkI with >Hi Hclose
    icases Hi with ⟨%Lf, HLf, Hσ', %Hok', #Hw, HG⟩
    imod srvRLog_lb γr.raft (Em \ ↑kvN) hr Lf A1 $$ HrI HLf HA1 with ⟨HLf, %Hp1⟩
    imod srvRLog_lb γr.raft (Em \ ↑kvN) hr Lf A2 $$ HrI HLf HA2 with ⟨HLf, %Hp2⟩
    ihave %HAi1 := srvRLogLb_idx γr.raft A1 $$ HA1
    ihave %HAi2 := srvRLogLb_idx γr.raft A2 $$ HA2
    have hpre : ∀ (A : List EntryModel) (L : mvcc.Log), kvModel γr.kv A = L → srvIdxOkW γr.raft.ai0 A →
        srvIdxOkW γr.raft.ai0 Lf ∧ (∀ m ∈ Lf, ¬ m.toLE.isFiller ∧ ¬ m.toLE.isEmptyV2) ∧
          opsOf (A.map EntryModel.toLE) <+: Lf.map EntryModel.toLE →
        L <+: kvModel γr.kv Lf ∧ L ≠ [] := by
      intro A L hA hAi hp
      obtain ⟨A', hA'L, hA'⟩ := srv_eqv_prefix γr.raft A Lf hAi hp.1 hp.2.1 hp.2.2
      refine ⟨?_, ?_⟩
      · rw [← hA, (kvModel_eqv γr.raft γr.kv A A' hA' Hok'.2.2.1).1]
        exact kvModel_prefix _ A' Lf hA'L
      · intro h0
        have hx := kvModel_extends γr.kv A
        rw [hA, h0] at hx
        exact Hok'.2.2.2.2.1.1 (List.prefix_nil.1 hx)
    obtain ⟨hq1, hn1⟩ := hpre A1 L1 hA1.1 HAi1 Hp1
    obtain ⟨hq2, hn2⟩ := hpre A2 L2 hA2.1 HAi2 Hp2
    iunfold etcdKV at Hc
    ihave %Hag := ghostVar_agree γr.kv.st _ _ _ _ $$ Hσ' Hc
    imod Hclose $$ [HLf Hσ' HG] with -
    · inext; iexists Lf; iframe HLf Hσ' Hw HG; ipureintro; exact Hok'
    imodintro
    iunfold etcdKV
    iframe Hc
    ipureintro
    exact ⟨kvModel γr.kv Lf, kvLeases γr.kv Lf, Hag.symm, hq1, hn1, hq2, hn2⟩
  · rw [srvKVCoreM_true]
    iintro #Hinvs H1 H2 Hc
    icases Hinvs with ⟨#HkI, -, #HrI, -, -, %HNx⟩
    rw [HNx]
    iunfold kvNxOn at H1
    iunfold kvNxOn at H2
    icases H1 with ⟨%A1, #HA1, %hA1⟩
    icases H2 with ⟨%A2, #HA2, %hA2⟩
    iunfold kvInvOn at HkI
    iinv HkI with >Hi Hclose
    icases Hi with ⟨%Lf, HLf, Hσ', Hh, %Hok', #Hw, HG⟩
    imod srvRLog_lb γr.raft (Em \ ↑kvN) hr Lf A1 $$ HrI HLf HA1 with ⟨HLf, %Hp1⟩
    imod srvRLog_lb γr.raft (Em \ ↑kvN) hr Lf A2 $$ HrI HLf HA2 with ⟨HLf, %Hp2⟩
    ihave %HAi1 := srvRLogLb_idx γr.raft A1 $$ HA1
    ihave %HAi2 := srvRLogLb_idx γr.raft A2 $$ HA2
    have hpre : ∀ (A : List EntryModel) (L : mvcc.Log), kvModelOn γr.kv srvAuthSt0 A = L →
        srvIdxOkW γr.raft.ai0 A →
        srvIdxOkW γr.raft.ai0 Lf ∧ (∀ m ∈ Lf, ¬ m.toLE.isFiller ∧ ¬ m.toLE.isEmptyV2) ∧
          opsOf (A.map EntryModel.toLE) <+: Lf.map EntryModel.toLE →
        L <+: kvModelOn γr.kv srvAuthSt0 Lf ∧ L ≠ [] := by
      intro A L hA hAi hp
      refine ⟨?_, ?_⟩
      · obtain ⟨L', hL', hAL⟩ := kvRaftOfOn_of_lb γr.raft γr.kv.c0 γr.kv.ch0
          (srvAuthSt0, γr.kv.log0, []) A Lf Hok'.2.2.2.1 hAi hp.1 (fun m hm => (hp.2.1 m hm).1) hp.2.2
        rw [← hA]
        unfold kvModelOn
        rw [hAL]
        exact kvRaftOfOn_prefix _ _ _ L' Lf hL'
      · intro h0
        have hx := kvRaftOfOn_extends γr.kv.c0 γr.kv.ch0 (srvAuthSt0, γr.kv.log0, []) A
        have : (kvRaftOfOn γr.kv.c0 γr.kv.ch0 (srvAuthSt0, γr.kv.log0, []) A).2.1 = L := hA
        rw [this, h0] at hx
        exact Hok'.2.2.2.2.2.1.1 (List.prefix_nil.1 hx)
    obtain ⟨hq1, hn1⟩ := hpre A1 L1 hA1.1 HAi1 Hp1
    obtain ⟨hq2, hn2⟩ := hpre A2 L2 hA2.1 HAi2 Hp2
    iunfold etcdKV at Hc
    ihave %Hag := ghostVar_agree γr.kv.st _ _ _ _ $$ Hσ' Hc
    imod Hclose $$ [HLf Hσ' Hh HG] with -
    · inext; iexists Lf; iframe HLf Hσ' Hh Hw HG; ipureintro; exact Hok'
    imodintro
    iunfold etcdKV
    iframe Hc
    ipureintro
    exact ⟨kvModelOn γr.kv srvAuthSt0 Lf, kvLeasesOn γr.kv srvAuthSt0 Lf, Hag.symm, hq1, hn1, hq2, hn2⟩

end s5

/-! ## The law -/

section law
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- **What the law takes of the server's KV invariants, in either auth mode**: the store invariant, its witness the
mode's (`kvNx`) and its permit `crevOk`, the lessor-window tie, and the KV names' lease mode the environment's. -/
theorem srvKVInvsM_lawParts (on : Bool) (s : Loc) (E : apply.AEnv GF) (γr : ReadNames) :
    srvKVInvsM (GF := GF) on s E γr ⊢
      □ srvApi.kvStoreInvG E.kv E.γ E.Nx E.Cp E.γs ∗
      srvApi.winTieRes E (clusterNoSnap γr.raft.raft.cl → E.lg = false) ∗
      ⌜E.Cp = srvApi.crevOk γr ∧ E.Nx = srvApi.kvNx γr on ∧ γr.kv.lm = E.lm⌝ := by
  cases on
  · iintro #H
    iunfold srvKVInvsM at H
    iunfold srvKVInvs at H
    icases H with ⟨-, -, -, #Hk, %Hm, %HNx, %Hlm, #Ht⟩
    iframe Hk Ht
    ipureintro; exact ⟨Hm.2.2.2, HNx, Hlm⟩
  · iintro #H
    iunfold srvKVInvsM at H
    icases H with ⟨#H', -⟩
    iunfold srvKVInvsOn at H'
    icases H' with ⟨-, -, -, -, #Hk, %Hm, %HNx, %Hm2, #Ht⟩
    iframe Hk Ht
    ipureintro; exact ⟨Hm.2, HNx, Hm2.2.1⟩

/-- The reader's view's KV invariants (`srvReadFieldsAtM`'s). -/
theorem srvKVInvsM_of_readM (on : Bool) (s : Loc) (E : apply.AEnv GF) (γr : ReadNames) :
    isServerReadM (GF := GF) on s E γr ⊢ srvKVInvsM on s E γr := by
  iintro #Hsrd
  iunfold isServerReadM at Hsrd
  icases Hsrd with ⟨%v, Hsrd⟩
  iunfold srvReadFieldsAtM at Hsrd
  icases Hsrd with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, #Hkvi, -⟩
  iexact Hkvi

/-- The law's mask's pieces. -/
theorem lessorLawMask_sub (Em : CoPset) (h : lessorLawMask ⊆ Em) :
    (↑kvN : CoPset) ⊆ Em ∧ (↑srvRaftN : CoPset) ⊆ Em \ ↑kvN ∧ (↑srvApi.winTieN : CoPset) ⊆ Em ∧
      (↑lease.lessorRdN : CoPset) ⊆ Em \ ↑srvApi.winTieN := by
  have hu : ∀ p, p ∈ (↑kvN : CoPset) ∨ p ∈ (↑srvRaftN : CoPset) ∨ p ∈ (↑srvApi.kvsN : CoPset) ∨
      p ∈ (↑srvApi.winTieN : CoPset) ∨ p ∈ (↑lease.lessorRdN : CoPset) → p ∈ Em := by
    intro p hp
    apply h
    unfold lessorLawMask
    simp only [Iris.Std.LawfulSet.mem_union]
    rcases hp with hp | hp | hp | hp | hp
    · exact .inl (.inl (.inl (.inl hp)))
    · exact .inl (.inl (.inl (.inr hp)))
    · exact .inl (.inl (.inr hp))
    · exact .inl (.inr hp)
    · exact .inr hp
  have hrk : (↑srvRaftN : CoPset) ⊆ ⊤ \ ↑kvN :=
    mask_ndot_ne' nroot "raft_commit" "server_kv" (by decide)
  refine ⟨fun p hp => hu p (.inl hp), fun p hp => ?_, fun p hp => hu p (.inr (.inr (.inr (.inl hp)))),
    fun p hp => ?_⟩
  · rw [Iris.Std.LawfulSet.mem_diff]
    exact ⟨hu p (.inr (.inl hp)), (Iris.Std.LawfulSet.mem_diff.1 (hrk p hp)).2⟩
  · rw [Iris.Std.LawfulSet.mem_diff]
    exact ⟨hu p (.inr (.inr (.inr (.inr hp)))),
      (Iris.Std.LawfulSet.mem_diff.1 (srvApi.lessorRdN_winTieN p hp)).2⟩

/-- The law's conclusion from S5 and the tie's law (pure): the floor `F` under the tie's committed logs `La` (and
`Lt`, or `La`'s items), both under the clients' log `C`; a key kept on `id` from `F`'s revision on is then an item of
both, which the snapshot holds. -/
theorem lsHolds_of_tie (F L0 La Lt C : mvcc.Log) (lt : LeaseTable) (σ : KVState) (σl : lease.LSnap) (id : w64)
    (k : GoString) (hF : F <+: L0) (hL0 : L0 <+: La) (hor : La <+: Lt ∨ srvApi.itemsOfLog La = srvApi.itemsOfLog Lt)
    (hσ : σ = kvStateOf C lt) (ha : La <+: C) (hna : La ≠ []) (ht : Lt <+: C) (hnt : Lt ≠ [])
    (hl : ∀ (it : go_etcd_io.etcd.server.v3.lease.LeaseItem) (id : w64),
      (srvApi.itemsOfLog La).lookup it = some id →
      (srvApi.itemsOfLog Lt).lookup it = some id → σl.2.1.lookup it = some id ∧ (σl.1.lookup id).isSome) :
    leaseKeptIn σ (F.length - 1) id k → lsHolds σl id k := by
  rintro ⟨-, hall⟩
  subst hσ
  have hrev : (kvStateOf C lt).rev = C.length - 1 := kvStateOf_rev C
  have hFa : F.length ≤ La.length := (hF.trans hL0).length_le
  have hItems : ∀ L : mvcc.Log, L <+: C → L ≠ [] → F.length ≤ L.length →
      (srvApi.itemsOfLog L).lookup ⟨k⟩ = some id := by
    intro L hL hne hFL
    have h0 : 0 < L.length := List.length_pos_iff.2 hne
    have hLC : L.length ≤ C.length := hL.length_le
    have := hall (L.length - 1) (by omega) (by rw [hrev]; omega)
    rw [kvStateOf_items_prefix C L lt hL hne] at this
    exact this
  have h1 := hItems La ha hna hFa
  have h2 : (srvApi.itemsOfLog Lt).lookup ⟨k⟩ = some id := by
    rcases hor with h | h
    · exact hItems Lt ht hnt (Nat.le_trans hFa h.length_le)
    · rw [← h]; exact h1
  obtain ⟨hk, hlive⟩ := hl ⟨k⟩ id h1 h2
  refine ⟨?_, hk⟩
  cases hx : σl.1.lookup id with
  | none => rw [hx] at hlive; cases hlive
  | some l => exact ⟨l, rfl⟩

/-- At the lease mode `none` no revision of the clients' state attaches a key to a lease (pure). -/
theorem leaseKeptIn_noLease (C : mvcc.Log) (lt : LeaseTable) (σ : KVState) (r₀ : Nat) (id : w64) (k : GoString)
    (hσ : σ = kvStateOf C lt) (hnl : mvcc.LogNoLease C) : ¬ leaseKeptIn σ r₀ id k := by
  rintro ⟨h0, hall⟩
  have h := hall σ.rev h0 (Nat.le_refl _)
  subst hσ
  rw [kvStateOf_at_kvs C _ (Nat.le_of_eq (kvStateOf_rev C))] at h
  rw [mvcc.leaseItemsOf_zero _ (mvcc.stateAt_leaseZero C hnl _)] at h
  cases h

/-- §5 **The per-member lessor law** (`lessor_keys_of_read_stmt`, the frozen statement; `notes/auth-lease-s4-frozen.lean.txt`
§5, rev 3), proved. Mode-generic (over `isServerReadM E.authOn`): at the lease mode `none` (`E.lg = false`, which auth
off with a client half implies) the committed model attaches no key to a lease and the hypothesis is false
(`leaseKeptIn_noLease`); otherwise the lessor-window tie places every index from the observation's `m` in a window
whose committed logs extend `F` (`srvApi.tie_obs`, `srvApi.tie_law`), and S5 places those logs under the view's state
(`srvKVCoreM_nx_st`, `lsHolds_of_tie`). The member's cluster in raft's no-snapshot mode: the tie's free markers
(pushed by the snapshot path) then do not occur in a cluster that grants leases. -/
theorem lessor_keys_of_read : lessor_keys_of_read_stmt (GF := GF) := by
  intro s E γr F id k hns
  iintro ⟨#Hsrd, #HF⟩
  ihave #Hkvi := srvKVInvsM_of_readM E.authOn s E γr $$ Hsrd
  ihave #Hcore := srvKVInvsM_core E.authOn s E γr $$ Hkvi
  ihave ⟨#Hst, #Htie, %HW⟩ := srvKVInvsM_lawParts E.authOn s E γr $$ Hkvi
  have Hlm := HW.2.2
  iunfold srvApi.winTieRes at Htie
  icases Htie with ⟨%γt, -, #Hti, #Hrd⟩
  haveI : ∀ l, Persistent (E.Nx l) := by rw [HW.2.1]; infer_instance
  haveI : ∀ l, Timeless (E.Nx l) := by rw [HW.2.1]; infer_instance
  haveI : ∀ c, Persistent (E.Cp c) := by rw [HW.1]; infer_instance
  haveI : ∀ c, Timeless (E.Cp c) := by rw [HW.1]; infer_instance
  by_cases hlg : E.lg = true
  · -- a cluster that grants leases: the tie
    have hFr : ¬ (clusterNoSnap γr.raft.raft.cl → E.lg = false) := by
      intro h; rw [h hns] at hlg; cases hlg
    imod srvApi.tie_obs E.Nx E.Cp E.kv E.γ E.γs _ hFr (mvcc.api.mvccLeases E.γ) γt F ⊤ (fun _ _ => CoPset.mem_full)
      (fun p hp => by
        rw [Iris.Std.LawfulSet.mem_diff]
        exact ⟨CoPset.mem_full, (Iris.Std.LawfulSet.mem_diff.1 (srvApi.winTieN_kvsN p hp)).2⟩)
      $$ [Hst Hti HF] with ⟨%tw0, %anc0, %j0, %L0, #Htw0, #Han0, #Hj0, %Hobs⟩
    · iframe Hst Hti HF
    obtain ⟨hlast, hFL0, hidx⟩ := Hobs
    imodintro
    iexists j0
    iframe Hj0
    iintro !> %i %σl %hi #Hi %Em %σ %hEm Hc
    obtain ⟨hk, hr, hw, hl⟩ := lessorLawMask_sub Em hEm
    imod srvApi.tie_law E.Nx _ hFr (mvcc.api.mvccLeases E.γ) E.γs γt hlast hidx i σl hi Em hw hl
      $$ [Hti Hrd Htw0 Han0 Hi] with ⟨%La, %Lt, #HLa, #HLt, %Hlaw⟩
    · iframe Hti Hrd Htw0 Han0 Hi
    obtain ⟨hL0, hor, hit⟩ := Hlaw
    imod srvKVCoreM_nx_st E.authOn E γr La Lt σ Em hk hr $$ Hcore HLa HLt Hc with ⟨Hc, %Hσ⟩
    obtain ⟨C, lt, hσ, ha, hna, ht, hnt⟩ := Hσ
    imodintro
    iframe Hc
    ipureintro
    exact lsHolds_of_tie F L0 La Lt C lt σ σl id k hFL0 hL0 hor hσ ha hna ht hnt hit
  · -- the lease mode `none`: no committed model attaches a key to a lease
    have hlm0 : γr.kv.lm = .none := by rw [Hlm]; exact apply.AEnv.lm_of_lg_false (by simpa using hlg)
    imod lease.lessorLb_get (mvcc.api.mvccLeases E.γ) ⊤ (fun _ _ => CoPset.mem_full) $$ Hrd with ⟨%m, #Hm⟩
    imodintro
    iexists m
    iframe Hm
    iintro !> %i %σl %_ #_ %Em %σ %hEm Hc
    obtain ⟨hk, -⟩ := lessorLawMask_sub Em hEm
    imod srvKVCoreM_st E.authOn E γr σ Em hk $$ Hcore Hc with ⟨Hc, %Hσ⟩
    obtain ⟨C, lt, hσ, hnl⟩ := Hσ
    imodintro
    iframe Hc
    ipureintro
    intro h
    exact absurd h (leaseKeptIn_noLease C lt σ _ id k hσ (hnl hlm0))

end law

end EtcdGrove
end Perennial
