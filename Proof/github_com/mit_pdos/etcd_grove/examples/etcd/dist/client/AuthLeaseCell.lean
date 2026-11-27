/-
**authlease's cell** (auth-lease S4, item 9; the handoff's design, accepted by etcd-grove-03 2026-11-18):
the driver's invariant over the client's half of the KV state (`etcdKV`), with the ghost state of
`CellModel.lean`'s `CellOk`: the leases the main thread fixed (`ids`), the revisions of the first
attachments (`ps`), the grant updates' ids (`gs`), the revocation flag (`d`), each a monotone
authority the invariant owns whole (every update is persistent with auth on, so no exclusive piece can
ride in one), and a lower bound of the state's revision (`v`, the lessor law's floor). Every update the
driver hands the server keeps it (`cell_writeAu`), and a read sees it (`cell_readAu`).
Lean-first (no Rocq counterpart).

Moved here from the authlease example's `authlease/Cell.lean` (2026-11-27): the multi-machine theorem
reuses it (names and namespace `etcd_authlease` unchanged).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.AuthLeaseCellModel
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.auth.Hist
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.auth.WorkEnv
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.auth.WorkAuth
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.LeaseReqOn
public import Perennial.Ghost.MonoList
public import Perennial.Ghost.MonoNat

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_authlease

open Iris Iris.BI Iris.ProofMode Iris.ProgramLogic Iris.Std go_etcd_io.etcd.server.v3.etcdserver client

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- The cell's ghost names. -/
structure CellNames where
  ids : GName
  ps : GName
  gs : GName
  d : GName
  v : GName
  /-- the main thread's permission for u's revocation (`0`: not yet; half with the main thread) -/
  a : GName

/-- The cell's namespace. -/
def cellN : Namespace := nroot .@ "authlease_cell"

/-- The cell's authorities at `ids ps gs d` (all but `ids`, which only the main thread changes). -/
def cellAuth (γc : CellNames) (ps : List Nat) (gs : List w64) (d : Nat) : IProp GF :=
  iprop(monoListAuthOwn γc.ps 1 ps ∗ monoListAuthOwn γc.gs 1 gs ∗ monoNatAuthOwn γc.d 1 d ∗
    (⌜d = 0⌝ ∨ monoNatLbOwn γc.a 1))

instance cellAuth_timeless (γc : CellNames) (ps : List Nat) (gs : List w64) (d : Nat) :
    Timeless (cellAuth (GF := GF) γc ps gs d) := by
  unfold cellAuth; infer_instance

/-- **The cell** (persistent; see the file header). -/
def cellInv (γk : KVNames) (γc : CellNames) : IProp GF :=
  inv cellN iprop(∃ (σ : KVState) (ids : List w64) (ps : List Nat) (gs : List w64) (d : Nat),
    etcdKV γk σ ∗ monoListAuthOwn γc.ids (1 : Qp).half ids ∗ cellAuth γc ps gs d ∗ monoNatAuthOwn γc.v 1 σ.rev ∗
    (∃ a : Nat, monoNatAuthOwn γc.a (1 : Qp).half a) ∗ ⌜CellOk σ ids ps gs d⌝)

instance cellInv_persistent (γk : KVNames) (γc : CellNames) :
    Persistent (cellInv (GF := GF) γk γc) := by
  unfold cellInv; infer_instance

/-- **What the cell's readers know of a state**: the cell holds at it, with lower bounds of its
ghost state and its revision, its attachments past the reader's `ps1`, its revocation flag past `d1`. -/
def cellSeen (γc : CellNames) (ps1 : List Nat) (d1 : Nat) (σ : KVState) : IProp GF :=
  iprop(∃ (ids : List w64) (ps : List Nat) (gs : List w64) (d : Nat), ⌜CellOk σ ids ps gs d ∧ ps1 <+: ps ∧ d1 ≤ d⌝ ∗
    monoListLbOwn γc.ids ids ∗ monoListLbOwn γc.ps ps ∗ monoListLbOwn γc.gs gs ∗ monoNatLbOwn γc.d d ∗
    monoNatLbOwn γc.v σ.rev)

instance cellSeen_persistent (γc : CellNames) (ps1 : List Nat) (d1 : Nat) (σ : KVState) :
    Persistent (cellSeen (GF := GF) γc ps1 d1 σ) := by
  unfold cellSeen; infer_instance

/-- The cell's namespace is inside the updates' outer mask. -/
theorem cellN_mask : (↑cellN : CoPset) ⊆ (⊤ \ ↑srvRaftN) \ ↑kvN := by
  intro p hp
  rw [Iris.Std.LawfulSet.mem_diff, Iris.Std.LawfulSet.mem_diff]
  exact ⟨⟨CoPset.mem_full, fun h => ndot_ne_disjoint nroot (by decide) p ⟨hp, h⟩⟩,
    fun h => ndot_ne_disjoint nroot (by decide) p ⟨hp, h⟩⟩

/-- The mask an update's step runs in, the cell opened. -/
abbrev cellM : CoPset := ((⊤ \ ↑srvRaftN) \ ↑kvN) \ ↑cellN

/-- **The cell's allocation**, from the client's half at a state without `a/x`. -/
theorem cell_alloc (γk : KVNames) (σ : KVState) (hx : mvcc.findKey xK σ.kvs = none) :
    etcdKV (GF := GF) γk σ ⊢ |={⊤}=> ∃ γc : CellNames, cellInv γk γc ∗ monoListLbOwn γc.ids ([] : List w64) ∗
      monoListLbOwn γc.ps ([] : List Nat) ∗ monoListLbOwn γc.gs ([] : List w64) ∗ monoNatLbOwn γc.d 0 ∗
      monoNatAuthOwn γc.a (1 : Qp).half 0 ∗ monoListAuthOwn γc.ids (1 : Qp).half ([] : List w64) := by
  iintro Hσ
  imod (mono_list_own_alloc (GF := GF) ([] : List w64)) with ⟨%γi, Hi, #Hil⟩
  ihave ⟨Hi, Hi2⟩ : monoListAuthOwn (GF := GF) γi (1 : Qp).half ([] : List w64) ∗
      monoListAuthOwn (GF := GF) γi (1 : Qp).half ([] : List w64) $$ [Hi]
  · iapply ((monoListAuthOwn_fractional (GF := GF) γi ([] : List w64)).fractional
      (1 : Qp).half (1 : Qp).half).1
    rw [Qp.half_add_half]; iexact Hi
  imod (mono_list_own_alloc (GF := GF) ([] : List Nat)) with ⟨%γp, Hp, #Hpl⟩
  imod (mono_list_own_alloc (GF := GF) ([] : List w64)) with ⟨%γg, Hg, #Hgl⟩
  imod (mono_nat_own_alloc (GF := GF) 0) with ⟨%γd, Hd, #Hdl⟩
  imod (mono_nat_own_alloc (GF := GF) σ.rev) with ⟨%γv, Hv, -⟩
  imod (mono_nat_own_alloc (GF := GF) 0) with ⟨%γa, Ha, -⟩
  ihave ⟨Ha1, Ha2⟩ : monoNatAuthOwn (GF := GF) γa (1 : Qp).half 0 ∗
      monoNatAuthOwn (GF := GF) γa (1 : Qp).half 0 $$ [Ha]
  · iapply ((monoNatAuthOwn_fractional (GF := GF) γa 0).fractional (1 : Qp).half (1 : Qp).half).1
    rw [Qp.half_add_half]; iexact Ha
  imod (inv_alloc cellN ⊤ iprop(∃ (σ : KVState) (ids : List w64) (ps : List Nat) (gs : List w64) (d : Nat),
    etcdKV γk σ ∗ monoListAuthOwn γi (1 : Qp).half ids ∗
      cellAuth ⟨γi, γp, γg, γd, γv, γa⟩ ps gs d ∗ monoNatAuthOwn γv 1 σ.rev ∗
      (∃ a : Nat, monoNatAuthOwn γa (1 : Qp).half a) ∗
    ⌜CellOk σ ids ps gs d⌝)) $$ [Hσ Hi Hp Hg Hd Hv Ha1] with #Hinv
  · inext
    iexists σ, [], [], [], 0
    iframe Hσ Hi Hv
    isplitl [Hp Hg Hd]
    · iunfold cellAuth; iframe Hp Hg Hd; ileft; ipureintro; rfl
    isplitl [Ha1]
    · iexists 0; iexact Ha1
    · ipureintro; exact cellOk_start σ hx
  imodintro
  iexists ⟨γi, γp, γg, γd, γv, γa⟩
  iframe Hil Hpl Hgl Hdl Ha2 Hi2
  iunfold cellInv
  iexact Hinv

/-- **An update under the cell**: an update whose step, given the cell at the state it fires at and
its grant `G`, re-establishes the cell after the operation (with new authorities) and gives `Q`,
keeps it. -/
theorem cell_writeAu (γk : KVNames) (γc : CellNames) (op : KVOp) (G Q : KVState → IProp GF) :
    cellInv (GF := GF) γk γc ∗
      □ (∀ σ ids ps gs d, ⌜CellOk σ ids ps gs d⌝ -∗ monoListAuthOwn γc.ids (1 : Qp).half ids -∗ cellAuth γc ps gs d -∗
          G σ ={cellM}=∗ ∃ ps' gs' d', ⌜CellOk (kvOpStep op σ) ids ps' gs' d'⌝ ∗
            monoListAuthOwn γc.ids (1 : Qp).half ids ∗ cellAuth γc ps' gs' d' ∗ Q σ) ⊢
    □ kvAu1G γk (kvOpStep op) G Q := by
  have Hm := cellN_mask
  iintro ⟨#Hinv, #HG⟩
  imodintro
  unfold kvAu1G
  iauintro
  unfold atomic_acc
  iunfold cellInv at Hinv
  iinv Hinv with >Hi Hclose
  icases Hi with ⟨%σ, %ids, %ps, %gs, %d, Hσ, Hids, Ha, Hv, Hal, %HS⟩
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ cellM from Std.LawfulSet.empty_subset)
  iintro Hclose2
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
  iexists σ
  iframe Hσ
  isplit
  · iintro Hσ
    imod Hclose2 with -
    imod Hclose $$ [Hσ Hids Ha Hv Hal] with -
    · inext; iexists σ, ids, ps, gs, d; iframe Hσ Hids Ha Hv Hal; ipureintro; exact HS
    imodintro
    iempintro
  · iintro ⟨Hσ, -, HGσ⟩
    imod Hclose2 with -
    imod HG $$ %σ %ids %ps %gs %d %HS Hids Ha HGσ with ⟨%ps', %gs', %d', %HS', Hids, Ha', HQ⟩
    imod (mono_nat_own_update (GF := GF) (γ := γc.v) (kvOpStep op σ).rev (kvOpStep_rev_le op σ)) $$ Hv
      with ⟨Hv, -⟩
    imod Hclose $$ [Hσ Hids Ha' Hv Hal] with -
    · inext; iexists (kvOpStep op σ), ids, ps', gs', d'; iframe Hσ Hids Ha' Hv Hal; ipureintro; exact HS'
    imodintro
    iexact HQ

/-- **A read under the cell** (persistent): it fires at a state the cell holds, and tells the reader
so (`cellSeen`). -/
theorem cell_readAu (γk : KVNames) (γc : CellNames) (ps1 : List Nat) (d1 : Nat) :
    cellInv (GF := GF) γk γc ∗ monoListLbOwn γc.ps ps1 ∗ monoNatLbOwn γc.d d1 ⊢
      kvReadAu γk (cellSeen γc ps1 d1) := by
  have Hm := cellN_mask
  iintro ⟨#Hinv, #Hp1, #Hd1⟩
  unfold kvReadAu kvAu
  imodintro
  iauintro
  unfold atomic_acc
  iunfold cellInv at Hinv
  iinv Hinv with >Hi Hclose
  icases Hi with ⟨%σ, %ids, %ps, %gs, %d, Hσ, Hids, Ha, Hv, Hal, %HS⟩
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ cellM from Std.LawfulSet.empty_subset)
  iintro Hclose2
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
  iexists σ
  iframe Hσ
  isplit
  · iintro Hσ
    imod Hclose2 with -
    imod Hclose $$ [Hσ Hids Ha Hv Hal] with -
    · inext; iexists σ, ids, ps, gs, d; iframe Hσ Hids Ha Hv Hal; ipureintro; exact HS
    imodintro
    iempintro
  · iintro ⟨Hσ, -⟩
    imod Hclose2 with -
    iunfold cellAuth at Ha
    icases Ha with ⟨Hp, Hg, Hd, Hdo⟩
    ihave #Hidl := monoListLbOwn_get γc.ids _ ids $$ Hids
    ihave #Hpl := monoListLbOwn_get γc.ps 1 ps $$ Hp
    ihave %Hpp := mono_list_auth_lb_valid γc.ps 1 ps ps1 $$ Hp Hp1
    ihave %Hdd := monoNatLbOwn_valid γc.d 1 d d1 $$ Hd Hd1
    ihave #Hgl := monoListLbOwn_get γc.gs 1 gs $$ Hg
    ihave #Hdl := monoNatLbOwn_get γc.d 1 d $$ Hd
    ihave #Hvl := monoNatLbOwn_get γc.v 1 σ.rev $$ Hv
    imod Hclose $$ [Hσ Hids Hp Hg Hd Hdo Hv Hal] with -
    · inext; iexists σ, ids, ps, gs, d; iframe Hσ Hids Hv Hal
      isplitl [Hp Hg Hd Hdo]
      · iunfold cellAuth; iframe Hp Hg Hd Hdo
      · ipureintro; exact HS
    imodintro
    imodintro
    iunfold cellSeen
    iexists ids, ps, gs, d
    iframe Hidl Hpl Hgl Hdl Hvl
    ipureintro; exact ⟨HS, Hpp.2, Hdd.2⟩

/-- **`id` is one of the grant updates' ids** (persistent; what a grant's update tells the caller). -/
def gsHas (γc : CellNames) (id : w64) (_σ : KVState) : IProp GF :=
  iprop(∃ gs : List w64, monoListLbOwn γc.gs gs ∗ ⌜id ∈ gs⌝)

/-- **At least `n` attachments recorded** (persistent; what a put's update tells the caller). -/
def psAtLeast (γc : CellNames) (n : Nat) (_σ : KVState) : IProp GF :=
  iprop(∃ ps : List Nat, monoListLbOwn γc.ps ps ∗ ⌜n ≤ ps.length⌝)

/-- **The revocation fired** (persistent; what u's revocation's update tells the caller). -/
def revoked (γc : CellNames) (_σ : KVState) : IProp GF := iprop(monoNatLbOwn γc.d 1)

instance gsHas_persistent (γc : CellNames) (id : w64) (σ : KVState) :
    Persistent (gsHas (GF := GF) γc id σ) := by unfold gsHas; infer_instance
instance psAtLeast_persistent (γc : CellNames) (n : Nat) (σ : KVState) :
    Persistent (psAtLeast (GF := GF) γc n σ) := by unfold psAtLeast; infer_instance
instance revoked_persistent (γc : CellNames) (σ : KVState) :
    Persistent (revoked (GF := GF) γc σ) := by unfold revoked; infer_instance

/-- The fixed leases, read off a lower bound: `ids` extends `[L]`/`[Lz, Lu]`. -/
theorem ids_of_lb (γc : CellNames) (ids pre : List w64) :
    ⊢ monoListAuthOwn (GF := GF) γc.ids (1 : Qp).half ids -∗ monoListLbOwn γc.ids pre -∗ ⌜pre <+: ids⌝ := by
  iintro Ha Hl
  ihave %H := mono_list_auth_lb_valid γc.ids _ ids pre $$ Ha Hl
  ipureintro; exact H.2

theorem lzOf_of_prefix {Lz : w64} {ids : List w64} (h : [Lz] <+: ids) :
    1 ≤ ids.length ∧ lzOf ids = Lz := by
  obtain ⟨t, rfl⟩ := h
  exact ⟨by simp, rfl⟩

theorem luOf_of_prefix {Lz Lu : w64} {ids : List w64} (h : [Lz, Lu] <+: ids) :
    2 ≤ ids.length ∧ lzOf ids = Lz ∧ luOf ids = Lu := by
  obtain ⟨t, rfl⟩ := h
  exact ⟨by simp, rfl, rfl⟩

theorem mem_of_lb (γc : CellNames) (gs gs0 : List w64) (id : w64) (h : id ∈ gs0) :
    ⊢ monoListAuthOwn (GF := GF) γc.gs 1 gs -∗ monoListLbOwn γc.gs gs0 -∗ ⌜id ∈ gs⌝ := by
  iintro Ha Hl
  ihave %H := mono_list_auth_lb_valid γc.gs 1 gs gs0 $$ Ha Hl
  ipureintro; exact H.2.subset h

theorem len_of_lb (γc : CellNames) (ps ps0 : List Nat) :
    ⊢ monoListAuthOwn (GF := GF) γc.ps 1 ps -∗ monoListLbOwn γc.ps ps0 -∗ ⌜ps0.length ≤ ps.length⌝ := by
  iintro Ha Hl
  ihave %H := mono_list_auth_lb_valid γc.ps 1 ps ps0 $$ Ha Hl
  ipureintro; exact H.2.length_le

/-- **A grant's update under the cell** (any principal's, at a TTL at most the maximum; the revocable
mode): it records its id in `gs` and tells the caller so. Its grant's freshness keeps `Lu` gone after
the revocation (thaw 1, `writeGrantG_grant_fresh`). -/
theorem cell_grantAu (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (conn : Loc) (ctx : GrpcMd)
    (γc : CellNames) (ttl : w64) (L₀ : List EntryModel) (httl : sint.Z ttl ≤ maxLeaseTTL)
    (hrev : ρ.kv.lm = .revocable) :
    cellInv (GF := GF) ρ.kv γc ⊢ □ ∀ id : w64, kvAu1G ρ.kv (kvOpStep (.leaseGrant id ttl))
      (clientGrant (srvTLSId s) E ρ conn ctx (.leaseGrant id ttl) L₀) (gsHas γc id) := by
  iintro #Hinv
  imodintro
  iintro %id
  ihave #Hau := cell_writeAu ρ.kv γc (.leaseGrant id ttl) (clientGrant (srvTLSId s) E ρ conn ctx (.leaseGrant id ttl) L₀)
    (gsHas γc id) $$ [Hinv]
  · isplitl []
    · iexact Hinv
    iintro !> %σ %ids %ps %gs %d %HS Hids Ha HG
    iunfold clientGrant at HG
    icases HG with ⟨%md, -, HG⟩
    ihave HG : writeGrantG ρ.kv srvAuthSt0 (v3rpc.hdrBoundT (srvTLSId s) E.authMode (auth.mdTokenOf md))
        (irrLeaseGrant id ttl) L₀ σ $$ [HG]
    · iunfold v3rpc.opGrantT at HG; iexact HG
    ihave %Hf := writeGrantG_grant_fresh ρ.kv srvAuthSt0 (v3rpc.hdrBoundT (srvTLSId s) E.authMode (auth.mdTokenOf md))
      id ttl L₀ σ hrev $$ HG
    iunfold cellAuth at Ha
    icases Ha with ⟨Hp, Hg, Hd, Hdo⟩
    imod (monoListAuthOwn_update_app (GF := GF) (γ := γc.gs) (l := gs) [id]) $$ Hg with ⟨Hg, #Hgl⟩
    imodintro
    iexists ps, gs ++ [id], d
    iframe Hids
    isplitr
    · ipureintro; exact cellOk_grant HS id ttl httl (cellOk_fresh HS id Hf)
    isplitl [Hp Hg Hd Hdo]
    · iunfold cellAuth; iframe Hp Hg Hd Hdo
    iunfold gsHas
    iexists gs ++ [id]
    iframe Hgl
    ipureintro; simp
  iexact Hau

/-- **Root's put of `z/lease` with `Lz` under the cell** (after the main thread fixed `Lz`, a grant
id): it records `z/lease`'s first attachment and tells the caller so. -/
theorem cell_putZAu (γk : KVNames) (γc : CellNames) (Lz : w64) (gs0 : List w64) (hg : Lz ∈ gs0)
    (G : KVState → IProp GF) :
    cellInv (GF := GF) γk γc ∗ monoListLbOwn γc.ids [Lz] ∗ monoListLbOwn γc.gs gs0 ⊢
      □ kvAu1G γk (kvOpStep (.put (leasePutOp zK Lz))) G (psAtLeast γc 1) := by
  iintro ⟨#Hinv, #Hi0, #Hg0⟩
  iapply cell_writeAu γk γc (.put (leasePutOp zK Lz)) G (psAtLeast γc 1)
  isplitl []
  · iexact Hinv
  iintro !> %σ %ids %ps %gs %d %HS Hids Ha -
  ihave %Hpre := ids_of_lb γc ids [Lz] $$ Hids Hi0
  obtain ⟨h1, hz⟩ := lzOf_of_prefix Hpre
  iunfold cellAuth at Ha
  icases Ha with ⟨Hp, Hg, Hd, Hdo⟩
  ihave %Hgs := mem_of_lb γc gs gs0 Lz hg $$ Hg Hg0
  subst hz
  imod (monoListAuthOwn_update (GF := GF) (γ := γc.ps) (l := ps)
    (if ps = [] then [(kvOpStep (.put (leasePutOp zK (lzOf ids))) σ).rev] else ps)
    (by split <;> simp_all)) $$ Hp with ⟨Hp, #Hpl⟩
  imodintro
  iexists (if ps = [] then [(kvOpStep (.put (leasePutOp zK (lzOf ids))) σ).rev] else ps), gs, d
  iframe Hids
  isplitr
  · ipureintro; exact cellOk_putZ HS h1 Hgs
  isplitl [Hp Hg Hd Hdo]
  · iunfold cellAuth; iframe Hp Hg Hd Hdo
  iunfold psAtLeast
  iexists _
  iframe Hpl
  ipureintro
  split
  · simp
  · exact List.length_pos_iff.2 ‹_›

/-- **u's put of `a/lease` with `Lu` under the cell** (after root's put; `Lu` fixed, a grant id): its
grant, told `z/lease` holds `Lz`, gives `Lu ≠ Lz` (`hne`: u may not write `z/lease`). -/
theorem cell_putAAu (γk : KVNames) (γc : CellNames) (Lz Lu : w64) (gs0 : List w64) (ps0 : List Nat)
    (hg : Lu ∈ gs0) (h1 : 1 ≤ ps0.length) (G : KVState → IProp GF) :
    cellInv (GF := GF) γk γc ∗ monoListLbOwn γc.ids [Lz, Lu] ∗ monoListLbOwn γc.gs gs0 ∗
      monoListLbOwn γc.ps ps0 ∗
      □ (∀ σ, ⌜leaseOf zK σ.kvs = some Lz⌝ -∗ G σ ={cellM}=∗ ⌜Lu ≠ Lz⌝) ⊢
      □ kvAu1G γk (kvOpStep (.put (leasePutOp aK Lu))) G (psAtLeast γc 2) := by
  iintro ⟨#Hinv, #Hi0, #Hg0, #Hp0, #Hne⟩
  iapply cell_writeAu γk γc (.put (leasePutOp aK Lu)) G (psAtLeast γc 2)
  isplitl []
  · iexact Hinv
  iintro !> %σ %ids %ps %gs %d %HS Hids Ha HG
  ihave %Hpre := ids_of_lb γc ids [Lz, Lu] $$ Hids Hi0
  obtain ⟨h2, hz, hu⟩ := luOf_of_prefix Hpre
  iunfold cellAuth at Ha
  icases Ha with ⟨Hp, Hg, Hd, Hdo⟩
  ihave %Hgs := mem_of_lb γc gs gs0 Lu hg $$ Hg Hg0
  ihave %Hps := len_of_lb γc ps ps0 $$ Hp Hp0
  have hza : leaseOf zK σ.kvs = some Lz := by rw [← hz]; exact HS.1.z_at (by omega)
  imod Hne $$ %σ %hza HG with %Hne'
  subst hz hu
  imod (monoListAuthOwn_update (GF := GF) (γ := γc.ps) (l := ps)
    (if ps.length = 1 then ps ++ [(kvOpStep (.put (leasePutOp aK (luOf ids))) σ).rev] else ps)
    (by split <;> simp)) $$ Hp with ⟨Hp, #Hpl⟩
  imodintro
  iexists (if ps.length = 1 then ps ++ [(kvOpStep (.put (leasePutOp aK (luOf ids))) σ).rev] else ps), gs, d
  iframe Hids
  isplitr
  · ipureintro; exact cellOk_putA HS (by omega) h2 Hgs Hne'
  isplitl [Hp Hg Hd Hdo]
  · iunfold cellAuth; iframe Hp Hg Hd Hdo
  iunfold psAtLeast
  iexists _
  iframe Hpl
  ipureintro
  have := HS.1.ps_ids
  split
  · simp; omega
  · have : ps.length ≠ 0 := by omega
    have := HS.1.ps_len
    -- ps.length ≥ 2 here: it is not 1 and at least 1
    omega

/-- **u's transaction putting `a/txn` with `Lu` under the cell** (after u's put). -/
theorem cell_txnTAu (γk : KVNames) (γc : CellNames) (Lz Lu : w64) (ps0 : List Nat)
    (h2 : 2 ≤ ps0.length) (G : KVState → IProp GF) :
    cellInv (GF := GF) γk γc ∗ monoListLbOwn γc.ids [Lz, Lu] ∗ monoListLbOwn γc.ps ps0 ⊢
      □ kvAu1G γk (kvOpStep (.txn (txnWireOf (leaseTxn tK Lu)))) G (psAtLeast γc 3) := by
  iintro ⟨#Hinv, #Hi0, #Hp0⟩
  iapply cell_writeAu γk γc (.txn (txnWireOf (leaseTxn tK Lu))) G (psAtLeast γc 3)
  isplitl []
  · iexact Hinv
  iintro !> %σ %ids %ps %gs %d %HS Hids Ha -
  ihave %Hpre := ids_of_lb γc ids [Lz, Lu] $$ Hids Hi0
  obtain ⟨-, -, hu⟩ := luOf_of_prefix Hpre
  iunfold cellAuth at Ha
  icases Ha with ⟨Hp, Hg, Hd, Hdo⟩
  ihave %Hps := len_of_lb γc ps ps0 $$ Hp Hp0
  subst hu
  imod (monoListAuthOwn_update (GF := GF) (γ := γc.ps) (l := ps)
    (if ps.length = 2 then ps ++ [(kvOpStep (.txn (txnWireOf (leaseTxn tK (luOf ids)))) σ).rev] else ps)
    (by split <;> simp)) $$ Hp with ⟨Hp, #Hpl⟩
  imodintro
  iexists (if ps.length = 2 then ps ++ [(kvOpStep (.txn (txnWireOf (leaseTxn tK (luOf ids)))) σ).rev] else ps),
    gs, d
  iframe Hids
  isplitr
  · ipureintro; exact cellOk_txnT HS (by omega)
  isplitl [Hp Hg Hd Hdo]
  · iunfold cellAuth; iframe Hp Hg Hd Hdo
  iunfold psAtLeast
  iexists _
  iframe Hpl
  ipureintro
  have := HS.1.ps_len
  split
  · simp; omega
  · omega

/-- **u's revocation of `Lu` under the cell** (after u's transaction): the cell is revoked. -/
theorem cell_revokeUAu (γk : KVNames) (γc : CellNames) (Lz Lu : w64) (ps0 : List Nat)
    (h3 : 3 ≤ ps0.length) (G : KVState → IProp GF) :
    cellInv (GF := GF) γk γc ∗ monoListLbOwn γc.ids [Lz, Lu] ∗ monoListLbOwn γc.ps ps0 ∗
      monoNatLbOwn γc.a 1 ⊢
      □ kvAu1G γk (kvOpStep (.leaseRevoke Lu)) G (revoked γc) := by
  iintro ⟨#Hinv, #Hi0, #Hp0, #Hal⟩
  iapply cell_writeAu γk γc (.leaseRevoke Lu) G (revoked γc)
  isplitl []
  · iexact Hinv
  iintro !> %σ %ids %ps %gs %d %HS Hids Ha -
  ihave %Hpre := ids_of_lb γc ids [Lz, Lu] $$ Hids Hi0
  obtain ⟨-, -, hu⟩ := luOf_of_prefix Hpre
  iunfold cellAuth at Ha
  icases Ha with ⟨Hp, Hg, Hd, Hdo⟩
  ihave %Hps := len_of_lb γc ps ps0 $$ Hp Hp0
  subst hu
  have hdle := HS.1.d_le
  imod (mono_nat_own_update (GF := GF) (γ := γc.d) 1 hdle) $$ Hd with ⟨Hd, #Hdl⟩
  imodintro
  iexists ps, gs, 1
  iframe Hids
  isplitr
  · ipureintro; exact cellOk_revokeU HS (by have := HS.1.ps_len; omega)
  isplitl [Hp Hg Hd]
  · iunfold cellAuth; iframe Hp Hg Hd; iright; iexact Hal
  iunfold revoked
  iexact Hdl

/-- **A refused update under the cell**: one whose grant, at any state the cell holds, is refuted,
keeps it (it never fires); its result is anything. -/
theorem cell_refusedAu (γk : KVNames) (γc : CellNames) (op : KVOp) (G Q : KVState → IProp GF) :
    cellInv (GF := GF) γk γc ∗
      □ (∀ σ ids ps gs d, ⌜CellOk σ ids ps gs d⌝ -∗ monoListAuthOwn γc.ids (1 : Qp).half ids -∗ cellAuth γc ps gs d -∗
          G σ ={cellM}=∗ False) ⊢
    □ kvAu1G γk (kvOpStep op) G Q := by
  iintro ⟨#Hinv, #HF⟩
  iapply cell_writeAu γk γc op G Q
  isplitl []
  · iexact Hinv
  iintro !> %σ %ids %ps %gs %d %HS Hids Ha HG
  imod HF $$ %σ %ids %ps %gs %d %HS Hids Ha HG with ⟨⟩

/-- **A revocation of `Lu` refused while `a/lease` holds it** (v's, the no-token client's, the invalid
token's): before u's revocation its grant is refuted (`a/lease` holds `Lu`, which the principal may not
write); after it, it changes nothing. -/
theorem cell_revokeLuAu (γk : KVNames) (γc : CellNames) (Lz Lu : w64) (ps0 : List Nat)
    (h3 : 3 ≤ ps0.length) (G : KVState → IProp GF) :
    cellInv (GF := GF) γk γc ∗ monoListLbOwn γc.ids [Lz, Lu] ∗ monoListLbOwn γc.ps ps0 ∗
      □ (∀ σ, ⌜leaseOf aK σ.kvs = some Lu⌝ -∗ G σ ={cellM}=∗ False) ⊢
      □ kvAu1G γk (kvOpStep (.leaseRevoke Lu)) G (revoked γc) := by
  iintro ⟨#Hinv, #Hi0, #Hp0, #HF⟩
  iapply cell_writeAu γk γc (.leaseRevoke Lu) G (revoked γc)
  isplitl []
  · iexact Hinv
  iintro !> %σ %ids %ps %gs %d %HS Hids Ha HG
  ihave %Hpre := ids_of_lb γc ids [Lz, Lu] $$ Hids Hi0
  obtain ⟨-, -, hu⟩ := luOf_of_prefix Hpre
  iunfold cellAuth at Ha
  icases Ha with ⟨Hp, Hg, Hd, Hdo⟩
  ihave %Hps := len_of_lb γc ps ps0 $$ Hp Hp0
  by_cases hd : d = 1
  · -- after the revocation: nothing changes
    subst hd
    ihave #Hdl := monoNatLbOwn_get γc.d 1 1 $$ Hd
    have hst : kvOpStep (.leaseRevoke Lu) σ = σ := by rw [← hu]; exact cellOk_revokeLu_done HS
    imodintro
    iexists ps, gs, 1
    iframe Hids
    isplitr
    · ipureintro; rw [hst]; exact HS
    isplitl [Hp Hg Hd Hdo]
    · iunfold cellAuth; iframe Hp Hg Hd Hdo
    iunfold revoked
    iexact Hdl
  · have hd0 : d = 0 := by have := HS.1.d_le; omega
    have ha : leaseOf aK σ.kvs = some Lu := by rw [← hu]; exact HS.1.a_at (by have := HS.1.ps_len; omega) hd0
    imod HF $$ %σ %ha HG with ⟨⟩

/-- **Before u's revocation is permitted, no update's `revoked` holds** (the main thread's half of
the permission at `0`). -/
theorem cell_not_revoked (γk : KVNames) (γc : CellNames) (σ : KVState) (E : CoPset) (hE : ↑cellN ⊆ E) :
    cellInv (GF := GF) γk γc ∗ monoNatAuthOwn γc.a (1 : Qp).half 0 ∗ revoked γc σ ={E}=∗ False := by
  iintro ⟨#Hinv, Ham, #Hr⟩
  iunfold cellInv at Hinv
  iunfold revoked at Hr
  iinv Hinv with >Hi Hclose
  icases Hi with ⟨%σ', %ids, %ps, %gs, %d, -, -, Ha, -, ⟨%a, Hal⟩, %HS⟩
  iunfold cellAuth at Ha
  icases Ha with ⟨-, -, Hd, Hdo⟩
  ihave %Hd1 := monoNatLbOwn_valid γc.d 1 d 1 $$ Hd Hr
  icases Hdo with (%Hd0 | #Ha1)
  · exfalso; omega
  ihave %Hv := monoNatLbOwn_valid γc.a _ 0 1 $$ Ham Ha1
  exfalso; omega

/-- **The main thread fixes the next lease** `L` (`Lz` before root's put; `Lu` after it, with
`psAtLeast 1`'s lower bound): `ids` grows by `L`. -/
theorem cell_fix (γk : KVNames) (γc : CellNames) (pre : List w64) (L : w64) (ps0 : List Nat)
    (hL : L ≠ W64 0) (hpre : pre.length < 2) (hps : pre.length ≤ ps0.length) (E : CoPset)
    (hE : ↑cellN ⊆ E) :
    cellInv (GF := GF) γk γc ∗ monoListAuthOwn γc.ids (1 : Qp).half pre ∗ monoListLbOwn γc.ps ps0 ={E}=∗
      monoListAuthOwn γc.ids (1 : Qp).half (pre ++ [L]) ∗ monoListLbOwn γc.ids (pre ++ [L]) := by
  iintro ⟨#Hinv, Hm, #Hp0⟩
  iunfold cellInv at Hinv
  iinv Hinv with >Hi Hclose
  icases Hi with ⟨%σ, %ids, %ps, %gs, %d, Hσ, Hids, Ha, Hv, Hal, %HS⟩
  ihave %Hag := monoListAuthOwn_agree γc.ids _ _ ids pre $$ Hids Hm
  obtain ⟨-, rfl⟩ := Hag
  iunfold cellAuth at Ha
  icases Ha with ⟨Hp, Hg, Hd, Hdo⟩
  ihave %Hps := len_of_lb γc ps ps0 $$ Hp Hp0
  have hlen : ids.length = ps.length := by
    have h1 := HS.1.ps_ids
    rcases Nat.lt_or_ge ids.length 1 with h0 | h0
    · have : ps.length = 0 := by
        rcases Nat.eq_zero_or_pos ps.length with h | h
        · exact h
        · have := h1.2.1 h; omega
      omega
    · have : ps.length ≤ 1 := by
        rcases Nat.lt_or_ge ps.length 2 with h | h
        · omega
        · have := h1.2.2 h; omega
      omega
  have hfr := (monoListAuthOwn_fractional (GF := GF) γc.ids ids).fractional (1 : Qp).half (1 : Qp).half
  rw [Qp.half_add_half] at hfr
  ihave Hfull : monoListAuthOwn (GF := GF) γc.ids 1 ids $$ [Hids Hm]
  · iapply hfr.2
    iframe Hids Hm
  imod (monoListAuthOwn_update_app (GF := GF) (γ := γc.ids) (l := ids) [L]) $$ Hfull with ⟨Hfull, #Hil⟩
  ihave ⟨Hids, Hm⟩ : monoListAuthOwn (GF := GF) γc.ids (1 : Qp).half (ids ++ [L]) ∗
      monoListAuthOwn (GF := GF) γc.ids (1 : Qp).half (ids ++ [L]) $$ [Hfull]
  · iapply ((monoListAuthOwn_fractional (GF := GF) γc.ids (ids ++ [L])).fractional
      (1 : Qp).half (1 : Qp).half).1
    rw [Qp.half_add_half]; iexact Hfull
  imod Hclose $$ [Hσ Hids Hp Hg Hd Hdo Hv Hal] with -
  · inext
    iexists σ, ids ++ [L], ps, gs, d
    iframe Hσ Hids Hv Hal
    isplitl [Hp Hg Hd Hdo]
    · iunfold cellAuth; iframe Hp Hg Hd Hdo
    · ipureintro; exact cellOk_fix σ ids ps gs d L HS hlen hpre hL
  imodintro
  iframe Hm Hil

/-- **The main thread permits u's revocation** (before handing out its update): the permission goes
to `1`, a persistent lower bound for the update. -/
theorem cell_permit (γk : KVNames) (γc : CellNames) (E : CoPset) (hE : ↑cellN ⊆ E) :
    cellInv (GF := GF) γk γc ∗ monoNatAuthOwn γc.a (1 : Qp).half 0 ={E}=∗
      monoNatAuthOwn γc.a (1 : Qp).half 1 ∗ monoNatLbOwn γc.a 1 := by
  iintro ⟨#Hinv, Hm⟩
  iunfold cellInv at Hinv
  iinv Hinv with >Hi Hclose
  icases Hi with ⟨%σ, %ids, %ps, %gs, %d, Hσ, Hids, Ha, Hv, ⟨%a, Hal⟩, %HS⟩
  ihave %Hag := monoNatAuthOwn_agree γc.a _ _ a 0 $$ Hal Hm
  obtain ⟨-, rfl⟩ := Hag
  have hfr := (monoNatAuthOwn_fractional (GF := GF) γc.a 0).fractional (1 : Qp).half (1 : Qp).half
  rw [Qp.half_add_half] at hfr
  ihave Hfull : monoNatAuthOwn (GF := GF) γc.a 1 0 $$ [Hal Hm]
  · iapply hfr.2
    iframe Hal Hm
  imod (mono_nat_own_update (GF := GF) (γ := γc.a) 1 (Nat.zero_le 1)) $$ Hfull with ⟨Hfull, #Hl⟩
  ihave ⟨Hal, Hm⟩ : monoNatAuthOwn (GF := GF) γc.a (1 : Qp).half 1 ∗
      monoNatAuthOwn (GF := GF) γc.a (1 : Qp).half 1 $$ [Hfull]
  · iapply ((monoNatAuthOwn_fractional (GF := GF) γc.a 1).fractional (1 : Qp).half (1 : Qp).half).1
    rw [Qp.half_add_half]; iexact Hfull
  imod Hclose $$ [Hσ Hids Ha Hv Hal] with -
  · inext
    iexists σ, ids, ps, gs, d
    iframe Hσ Hids Ha Hv
    isplitl [Hal]
    · iexists 1; iexact Hal
    · ipureintro; exact HS
  imodintro
  iframe Hm Hl

/-! ### The grants of refused updates -/

/-- **A request of `who`'s granted at `setupSt`, its lease part included** (at the lease items of the
state `σ` the update fires at). -/
def akGrantedL (who : GoString) (σ : KVState) (rq : apply.IRRModel) : Prop :=
  ∃ r hm, kvGrantedL (etcd_auth.setupSt r) (mvcc.leaseItemsOf σ.kvs) (apply.withHeader rq hm) ∧
    etcd_auth.akUser who hm.username

/-- **A write's grant at an attempt of `who`'s is granted at `setupSt`, its lease part included**
(`etcd_auth.akGranted_of_writeGrantG`'s, through `writeGrantG_granted`). -/
theorem akGrantedL_of_writeGrantG (s : Loc) (E : apply.AEnv GF) (γa : auth.AuthNames)
    (ρ : ReqNames) (Lset : List EntryModel) (n : Nat) (who : GoString) (tok : Option GoString)
    (rq : apply.IRRModel) (σ : KVState) (Em : CoPset) (hγa : E.authMode = .on γa)
    (hE : ↑authHistN ⊆ Em) :
    etcd_auth.akAuthFixed (GF := GF) γa ρ Lset n ∗ etcd_auth.akTokSeen γa who tok ∗
        □ (srvTLSId s -∗ False) ⊢
      writeGrantG ρ.kv srvAuthSt0 (v3rpc.hdrBoundT (srvTLSId s) E.authMode tok) rq Lset σ ={Em}=∗
        ⌜akGrantedL who σ rq⌝ := by
  rw [hγa]
  iintro ⟨#Hf, #Hseen, #Htls⟩ Hw
  ihave Hw := writeGrantG_granted ρ.kv srvAuthSt0 _ rq Lset σ $$ Hw
  icases Hw with ⟨%hm, %L, #Hb, #Hlb, %Hp⟩
  obtain ⟨hL, hgr⟩ := Hp
  imod (etcd_auth.akAuthFixed_write γa ρ Lset n L Em hE hL) $$ Hf Hlb with %Hr
  obtain ⟨r, hr⟩ := Hr
  ihave %Hu := etcd_auth.akUser_hdr s γa who tok hm $$ [Hb Hseen Htls]
  · iframe Hb Hseen Htls
  imodintro
  ipureintro
  exact ⟨r, hm, by rw [← hr]; exact hgr, Hu⟩

/-- **A lease-part refusal**: a granted put, transaction put or revocation names a lease `L` holding
the key `k`, at the lease check of a principal who may not write `k`. -/
theorem not_akGrantedL_lease (who : GoString) (σ : KVState) (rq : apply.IRRModel) (k : GoString) (L : w64)
    (hk : leaseOf k σ.kvs = some L) (hL : L ≠ W64 0)
    (hwho : who = go!"anon" ∨ who = go!"bad" ∨ who = go!"v" ∨ (who = go!"u" ∧ ¬ etcd_auth.inRangeK k))
    (hrq : ∀ r (hm : apply.HeaderModel), leaseGrantedM (etcd_auth.setupSt r) (mvcc.leaseItemsOf σ.kvs)
      (apply.withHeader rq hm) → leaseOk (etcd_auth.setupSt r) ⟨hm.username, hm.authRevision⟩
        (mvcc.leaseItemsOf σ.kvs) L) :
    ¬ akGrantedL who σ rq := by
  rintro ⟨r, hm, ⟨-, hl⟩, hu⟩
  refine not_leaseOk_setupSt r ⟨hm.username, hm.authRevision⟩ _ k L (leaseItemsOf_of_leaseOf hk hL) ?_
    (hrq r hm hl)
  show hm.username = _ ∨ (hm.username = go!"u" ∧ ¬ etcd_auth.inRangeK k) ∨ hm.username = go!"v"
  unfold etcd_auth.akUser at hu
  rcases hu with h0 | ⟨hw, hw'⟩
  · exact Or.inl h0
  · rcases hw' with rfl | rfl
    · rcases hwho with h | h | h | ⟨-, hk'⟩
      · exact absurd h (by decide)
      · exact absurd h (by decide)
      · exact absurd h (by decide)
      · exact Or.inr (Or.inl ⟨hw, hk'⟩)
    · exact Or.inr (Or.inr hw)

/-- A put's lease check is of its lease. -/
theorem leaseGranted_put (r : Nat) (I : GMap go_etcd_io.etcd.server.v3.lease.LeaseItem w64) (o : OpFull)
    (hm : apply.HeaderModel) (h : leaseGrantedM (etcd_auth.setupSt r) I (apply.withHeader (irrPut o) hm)) :
    leaseOk (etcd_auth.setupSt r) ⟨hm.username, hm.authRevision⟩ I o.leaseID := by
  unfold leaseGrantedM at h
  rw [dispatchKind_withHeader] at h
  have hk : apply.dispatchKind (irrPut o) = .put := by
    simp [apply.dispatchKind, irrPut, apply.irrEmpty]
  rw [hk] at h
  exact h o rfl

/-- A revocation's lease check is of its lease. -/
theorem leaseGranted_revoke (r : Nat) (I : GMap go_etcd_io.etcd.server.v3.lease.LeaseItem w64) (id : w64)
    (hm : apply.HeaderModel)
    (h : leaseGrantedM (etcd_auth.setupSt r) I (apply.withHeader (irrLeaseRevoke id) hm)) :
    leaseOk (etcd_auth.setupSt r) ⟨hm.username, hm.authRevision⟩ I id := by
  unfold leaseGrantedM at h
  rw [dispatchKind_withHeader, irrLeaseRevoke_kind] at h
  exact h id rfl

/-! ### The set-up's puts, other members' names, masks -/

/-- `SetUp`'s keys are none of the cell's four. -/
theorem setupKeys_other (k : GoString) (hk : k ∈ etcd_auth.setupKeys) :
    k ≠ xK ∧ k ≠ zK ∧ k ≠ aK ∧ k ≠ tK := by
  simp only [etcd_auth.setupKeys, etcd_auth.principals, etcd_auth.keyParts, etcd_auth.keyOfK,
    List.flatMap_cons, List.flatMap_nil, List.map_cons, List.map_nil, List.cons_append,
    List.nil_append, List.append_nil, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- **A set-up put under the cell** (`SetUp`'s, from any state): it keeps the cell, told nothing. -/
theorem cell_setupAu (γk : KVNames) (γc : CellNames) (k : GoString) (hk : k ∈ etcd_auth.setupKeys) :
    cellInv (GF := GF) γk γc ⊢
      □ kvOpAu1 γk (.put (client.putKeyOp k go!"setup")) (fun _ => iprop(True)) := by
  obtain ⟨hx, hz, ha, ht⟩ := setupKeys_other k hk
  iintro #Hinv
  ihave #Hau := cell_writeAu γk γc (.put (client.putKeyOp k go!"setup")) (fun _ => iprop(True))
    (fun _ => iprop(True)) $$ [Hinv]
  · isplitl []
    · iexact Hinv
    iintro !> %σ %ids %ps %gs %d %HS Hids Ha -
    imodintro
    iexists ps, gs, d
    iframe Hids Ha
    ipureintro; exact cellOk_put0 HS k go!"setup" hx hz ha ht
  imodintro
  unfold kvOpAu1
  iapply etcd_auth.kvAu1G_true
  iexact Hau

/-- **The cell at another member's KV names** (the same client half: `etcdKV` reads only `st`). -/
theorem cellInv_same (γk γk' : KVNames) (γc : CellNames) (h : γk'.st = γk.st) :
    cellInv (GF := GF) γk γc ⊢ cellInv γk' γc := by
  unfold cellInv etcdKV
  rw [h]

/-- The auth history's namespace is inside an update's step mask, the cell opened. -/
theorem authHistN_cellM : (↑authHistN : CoPset) ⊆ cellM := by
  intro p hp
  rw [Iris.Std.LawfulSet.mem_diff, Iris.Std.LawfulSet.mem_diff, Iris.Std.LawfulSet.mem_diff]
  exact ⟨⟨⟨CoPset.mem_full, fun h => ndot_ne_disjoint nroot (by decide) p ⟨hp, h⟩⟩,
    fun h => ndot_ne_disjoint nroot (by decide) p ⟨hp, h⟩⟩,
    fun h => ndot_ne_disjoint nroot (by decide) p ⟨hp, h⟩⟩

end defs

end etcd_authlease
end EtcdGrove
end Perennial
