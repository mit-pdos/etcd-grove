/-
**authlease's lessor-side refusals** (auth-lease S4, item 9; Draft §4.3, the S4 probe's
`leaseKeysVerdict_refused` through the cell): after barrier 2 at a member (its floor `F` and the cell
seen at `F`'s state with the three attachments), the member's lessor holds `z/lease` on `Lz` and
`a/lease` on `Lu` at every index from some `m` on, while u's revocation is not yet permitted
(`cell_holds`, from the per-member lessor law `lessor_keys_of_read` and the cell's attachment
history). A passed `TimeToLive` keys verdict or `Leases` listing over such a lease, at a principal
denied the key, is then impossible (`holds_refutes_keys`, `holds_refutes_ids`).
Lean-first (no Rocq counterpart).

Moved here from the authlease example's `authlease/Holds.lean` (2026-11-27): the multi-machine theorem
reuses it (names and namespace `etcd_authlease` unchanged).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.AuthLeaseCell
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.LessorFollows
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.LeaseCheck

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_authlease

open Iris Iris.BI Iris.ProofMode Iris.ProgramLogic Iris.Std go_etcd_io.etcd.server.v3.etcdserver client

/-! ### The history the law asks, from the cell (pure) -/

section pure
variable [GooseExts]

/-- `z/lease` is kept on `Lz` from a seen state's revision on (its first attachment at or before it). -/
theorem keptZ_of_cell {σF σ : KVState} {ids0 ids : List w64} {ps0 ps : List Nat} {gs0 gs : List w64}
    {d0 d : Nat} (hF : CellOk σF ids0 ps0 gs0 d0) (h : CellOk σ ids ps gs d) (hps : ps0 <+: ps)
    (hrev : σF.rev ≤ σ.rev) (h1 : 1 ≤ ps0.length) :
    leaseKeptIn σ σF.rev (lzOf ids) zK := by
  obtain ⟨r0, hr0⟩ : ∃ r0, ps0[0]? = some r0 := ⟨ps0[0], List.getElem?_eq_getElem (by omega)⟩
  have hle := (hF.2.z_hist r0 hr0).1
  have hz := (h.2.z_hist r0 (getElem?_prefix hps hr0)).2
  have hl1 : 1 ≤ ps.length := by have := hps.length_le; omega
  refine ⟨hrev, fun r h1 h2 => leaseItemsOf_of_leaseOf (hz r (by omega) h2) (h.1.lz_ne (h.1.ps_ids.2.1 hl1))⟩

/-- `a/lease` is kept on `Lu` from a seen state's revision on, before the revocation. -/
theorem keptA_of_cell {σF σ : KVState} {ids0 ids : List w64} {ps0 ps : List Nat} {gs0 gs : List w64}
    {d0 d : Nat} (hF : CellOk σF ids0 ps0 gs0 d0) (h : CellOk σ ids ps gs d) (hps : ps0 <+: ps)
    (hrev : σF.rev ≤ σ.rev) (h2 : 2 ≤ ps0.length) (hd : d = 0) :
    leaseKeptIn σ σF.rev (luOf ids) aK := by
  obtain ⟨r1, hr1⟩ : ∃ r1, ps0[1]? = some r1 := ⟨ps0[1], List.getElem?_eq_getElem (by omega)⟩
  have hle := (hF.1.hist r1 hr1).1
  have ha := (h.2.a_hist r1 (getElem?_prefix hps hr1) hd).2
  have hl2 : 2 ≤ ps.length := by have := hps.length_le; omega
  refine ⟨hrev, fun r h1 h2 => leaseItemsOf_of_leaseOf (ha r (by omega) h2) (h.1.lu_ne (h.1.ps_ids.2.2 hl2))⟩

end pure

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- The law's mask is outside the cell's namespace. -/
theorem lawMask_cell : lessorLawMask ⊆ (⊤ : CoPset) \ ↑cellN := by
  intro p hp
  rw [Iris.Std.LawfulSet.mem_diff]
  refine ⟨CoPset.mem_full, fun hc => ?_⟩
  unfold lessorLawMask at hp
  simp only [Iris.Std.LawfulSet.mem_union] at hp
  rcases hp with (((h | h) | h) | h) | h <;> exact ndot_ne_disjoint nroot (by decide) p ⟨hc, h⟩

/-- **The lease `id` holds `k` at every index of the lessor `γl` from `m` on**, while the main thread
holds u's revocation unpermitted (the S4 probe's `leaseHoldsFrom`, through the cell). -/
def holdsFrom (γc : CellNames) (γl : GName) (m : Nat) (id : w64) (k : GoString) : IProp GF :=
  iprop(□ ∀ (i : Nat) (σl : lease.LSnap), ⌜m ≤ i⌝ -∗ lease.lessorAt γl i σl -∗
    monoNatAuthOwn γc.a (1 : Qp).half 0 ={⊤}=∗ monoNatAuthOwn γc.a (1 : Qp).half 0 ∗ ⌜lsHolds σl id k⌝)

instance holdsFrom_persistent (γc : CellNames) (γl : GName) (m : Nat) (id : w64) (k : GoString) :
    Persistent (holdsFrom (GF := GF) γc γl m id k) := by
  unfold holdsFrom; infer_instance

/-- **The member's lessor holds the cell's attachments** (see the file header): after a read at the
member whose floor is `F` and which saw the cell past the three attachments (`ps1`), `z/lease` on `Lz`
and `a/lease` on `Lu`. -/
theorem cell_holds (hlaw : lessor_keys_of_read_stmt (GF := GF)) (s : Loc) (E : apply.AEnv GF)
    (γr : ReadNames) (γc : CellNames) (F : mvcc.Log) (lt : LeaseTable) (Lz Lu id : w64) (k : GoString)
    (ps1 : List Nat) (d1 : Nat) (h3 : 3 ≤ ps1.length) (hns : clusterNoSnap γr.raft.raft.cl)
    (hk : (id = Lz ∧ k = zK) ∨ (id = Lu ∧ k = aK)) :
    isServerReadM E.authOn s E γr ∗ srvApi.kvLogLb E.γs F ∗ cellInv γr.kv γc ∗
        cellSeen γc ps1 d1 (kvStateOf F lt) ∗ monoListLbOwn γc.ids [Lz, Lu] ⊢ |={⊤}=>
      ∃ m : Nat, lease.lessorLb (mvcc.api.mvccLeases E.γ) m ∗
        holdsFrom γc (mvcc.api.mvccLeases E.γ) m id k := by
  iintro ⟨#Hrd, #HF, #Hinv, #Hseen, #Hi0⟩
  imod (hlaw s E γr F id k hns) $$ [Hrd HF] with ⟨%m, #Hm, #Hlaw⟩
  · iframe Hrd HF
  imodintro
  iexists m
  iframe Hm
  iunfold holdsFrom
  iintro !> %i %σl %hmi #Hat Ham
  ihave Hl := Hlaw $$ %i %σl %hmi Hat
  iunfold cellSeen at Hseen
  icases Hseen with ⟨%ids0, %ps0, %gs0, %d0, %HF0, #Hil0, #Hpl0, -, -, #Hvl0⟩
  iunfold cellInv at Hinv
  iinv Hinv with >Hi Hclose
  icases Hi with ⟨%σ, %ids, %ps, %gs, %d, Hσ, Hids, Ha, Hv, ⟨%a, Hal⟩, %HS⟩
  imod Hl $$ %((⊤ : CoPset) \ ↑cellN) %σ %lawMask_cell Hσ with ⟨Hσ, %Himp⟩
  ihave %Hpre := ids_of_lb γc ids [Lz, Lu] $$ Hids Hi0
  obtain ⟨-, hz, hu⟩ := luOf_of_prefix Hpre
  iunfold cellAuth at Ha
  icases Ha with ⟨Hp, Hg, Hd, Hdo⟩
  ihave %Hpp := mono_list_auth_lb_valid γc.ps 1 ps ps0 $$ Hp Hpl0
  ihave %Hvv := monoNatLbOwn_valid γc.v 1 σ.rev (kvStateOf F lt).rev $$ Hv Hvl0
  icases Hdo with (%Hd0 | #Ha1)
  rotate_left
  · ihave %Hbad := monoNatLbOwn_valid γc.a _ 0 1 $$ Ham Ha1
    exfalso; omega
  have hp3 : 3 ≤ ps0.length := by have := HF0.2.1.length_le; omega
  have hkept : leaseKeptIn σ (F.length - 1) id k := by
    rw [← kvStateOf_rev F (lt := lt)]
    rcases hk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [← hz]; exact keptZ_of_cell HF0.1 HS Hpp.2 Hvv.2 (by omega)
    · rw [← hu]; exact keptA_of_cell HF0.1 HS Hpp.2 Hvv.2 (by omega) Hd0
  imod Hclose $$ [Hσ Hids Hp Hg Hd Hv Hal] with -
  · inext
    iexists σ, ids, ps, gs, d
    iframe Hσ Hids Hv
    isplitl [Hp Hg Hd]
    · iunfold cellAuth; iframe Hp Hg Hd; ileft; ipureintro; exact Hd0
    isplitl [Hal]
    · iexists a; iexact Hal
    · ipureintro; exact HS
  imodintro
  iframe Ham
  ipureintro; exact Himp hkept

/-- **A passed keys verdict over a held lease is impossible** (the S4 probe's `leaseKeysVerdict_refused`,
through the cell): the principal is denied reading `k`. -/
theorem holds_refutes_keys (γc : CellNames) (γl : GName) (m : Nat) (id : w64) (k : GoString)
    (M : auth.AuthMode) (n : Nat) (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) :
    holdsFrom (GF := GF) γc γl m id k ∗
      □ (auth.permVerdictFrom M n info k [] .read GoInterface.nil ={⊤}=∗ False) ∗
      leaseKeysVerdictFrom M n info γl m id .read ∗ monoNatAuthOwn γc.a (1 : Qp).half 0 ={⊤}=∗ False := by
  iintro ⟨#Hh, #Hd, Hv, Ham⟩
  iunfold leaseKeysVerdictFrom at Hv
  iunfold holdsFrom at Hh
  icases Hv with (Habs | ⟨%l, Hv⟩)
  · iunfold lease.leaseAbsentFrom at Habs
    icases Habs with ⟨%i, %σ, %hσ, #Ha⟩
    imod Hh $$ %i %σ %hσ.1 Ha Ham with ⟨-, %hh⟩
    obtain ⟨⟨l, hl⟩, -⟩ := hh
    rw [hσ.2] at hl
    cases hl
  · iunfold leaseOfKeysVerdictFrom at Hv
    icases Hv with ⟨%ks, Hks, Hall⟩
    iunfold lease.leaseKeysFrom at Hks
    icases Hks with ⟨%i, %σ, %hσ, #Ha⟩
    imod Hh $$ %i %σ %hσ.1 Ha Ham with ⟨-, %hh⟩
    have hk : k ∈ ks := (hσ.2.2.1 k).2 hh.2
    ihave Hk := BigSepL.bigSepL_mem hk $$ Hall
    iapply Hd $$ Hk

/-- **A passed listing at an index from `m` on lists the held lease**, so its keys verdict is passed. -/
theorem holds_listed (γc : CellNames) (γl : GName) (m i : Nat) (id : w64) (k : GoString) (ids : List w64)
    (hmi : m ≤ i) :
    holdsFrom (GF := GF) γc γl m id k ∗ lease.leaseIdsAt γl i ids ∗
      monoNatAuthOwn γc.a (1 : Qp).half 0 ={⊤}=∗ monoNatAuthOwn γc.a (1 : Qp).half 0 ∗ ⌜id ∈ ids⌝ := by
  iintro ⟨#Hh, #Hids, Ham⟩
  iunfold lease.leaseIdsAt at Hids
  icases Hids with ⟨%σ, %hσ, #Ha⟩
  iunfold holdsFrom at Hh
  imod Hh $$ %i %σ %hmi Ha Ham with ⟨Ham, %hh⟩
  imodintro
  iframe Ham
  ipureintro
  obtain ⟨⟨l, hl⟩, -⟩ := hh
  exact (hσ.2 id).2 (by rw [hl]; rfl)

end defs

end etcd_authlease
end EtcdGrove
end Perennial
