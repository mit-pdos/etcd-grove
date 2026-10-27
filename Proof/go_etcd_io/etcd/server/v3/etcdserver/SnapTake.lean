/-
**What the apply thread's `snapshot` takes beyond its snapshot state** (D22 J4b, 2026-10-27;
`notes/decisions.md`, "D22 J4b"). Lean-first.

* `memCertReg γs`: the storage's certificate registry (`γs.cert`, `NewMemoryStorage`'s authority
  `memCertAuth`) in an invariant that ties its entries to nothing (`srvCertN`): what lets the apply
  thread register the snapshot it creates, which `CreateSnapshot` needs (`memStorCert`). Free in
  raft's no-snapshot mode (raft reads no storage certificate: `certLink` is vacuous); L3 replaces
  it by raft's `memCertInv` (the entries' raft certificates, `ep.confState`'s).
* `MemoryStorage.CreateSnapshot.wp_reg`: `CreateSnapshot` over the shared token
  (`srvStorTokN`'s `memTokShared`, as J3's `wp_shared`) and the registry, for any conf-state
  argument (`memCsArg`: `ep.confState` may be `nil`): the entry registered at the linearization
  point, for the snapshot the storage's state then gives.
* `srvSnapDisk s γr`: the raft wrapper's `storage` (a `*storage.storage` over the snapshotter
  `ss`), its `SaveSnap` (the WAL's and the snapshotter's write, names-only: `saveSnapOk`) and the
  snapshot directory's invariant at a removal fact `Rm` that the applied index past `j` gives
  (J1a's `srvSnapRm`'s second disjunct): what `snapshot(toDisk)`'s `SaveSnap` and `Release` take.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvApplyAll
public import Proof.go_etcd_io.etcd.server.v3.storage.InvOpen
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Net
public import Proof.go_etcd_io.raft.v3.InvPbLog

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- The registry's namespace. -/
def srvCertN : Namespace := nroot .@ "etcdserver_cert_reg"

theorem srvCertN_disj_memSnap : (↑srvCertN : CoPset) ## ↑memSnapN := by
  intro p ⟨hp, h⟩
  exact ndot_ne_disjoint nroot (by decide : "etcdserver_cert_reg" ≠ "raft_memsnap") p ⟨hp, h⟩

theorem srvCertN_disj_tok : (↑srvCertN : CoPset) ## ↑srvStorTokN := by
  intro p ⟨hp, h⟩
  exact ndot_ne_disjoint nroot (by decide : "etcdserver_cert_reg" ≠ "etcdserver_stor_tok") p ⟨hp, h⟩

/-- **The storage's certificate registry, free** (persistent; see the file header). -/
def memCertReg (γs : MemStorNames) : IProp GF :=
  inv srvCertN iprop(∃ L : List CertKey, monoListAuthOwn γs.cert 1 L)

instance memCertReg_persistent (γs : MemStorNames) : Persistent (memCertReg (GF := GF) γs) := by
  unfold memCertReg; infer_instance

/-- The registry from its authority. -/
theorem memCertReg_alloc (γs : MemStorNames) (Ec : CoPset) :
    ⊢ memCertAuth (GF := GF) γs ={Ec}=∗ memCertReg γs := by
  iintro Ha
  iunfold memCertAuth at Ha
  iunfold memCertReg
  iapply inv_alloc
  inext
  iexists ([] : List CertKey)
  iexact Ha

/-- **The raft wrapper's `SaveSnap`** (persistent; the trust boundary, names-only: the WAL's
`SaveSnapshot` and the snapshotter's `SaveSnap` write the snapshot's `.snap` file and its WAL
record, outside what the model tracks; `bootOk`'s storage contract, J1a): for a read-only
snapshot, it returns `nil` (an I/O failure is the environment's, as `storage.releaseOk`). -/
def saveSnapOk (stp : Loc) : IProp GF :=
  iprop(□ ∀ (sn : Loc) (sv : SnapshotM),
    {{ ownSnapM sn DFrac.discard sv }}
      (App (Val (stp @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.storage.ty @!!
        go!"SaveSnap")) (Val #sn))
    {{ RET #interface.nil; True }})

instance saveSnapOk_persistent (stp : Loc) : Persistent (saveSnapOk (GF := GF) stp) := by
  unfold saveSnapOk; infer_instance

/-- **The disk snapshot's storage** (persistent; see the file header) of the server `s` with the
read names `γr`. -/
def srvSnapDisk (s : Loc) (γr : ReadNames) : IProp GF :=
  iprop(∃ (stp ss : Loc) (γd : GName) (img : w64 → backend.Data → IProp GF) (Rm : w64 → IProp GF),
    ⌜storage.storageSnap stp ss⌝ ∗
    rnStorageAddr (srvRAddr s) ↦□ (interface.mkOk (go.GoType.PointerType
      go_etcd_io.etcd.server.v3.storage.storage.ty) #stp : GoInterface) ∗
    saveSnapOk stp ∗
    inv snapDirN (snapDirInv ss γd img Rm) ∗
    □ (∀ j : w64, monoNatLbOwn γr.applied (uint.nat j + 1) -∗ Rm j))

instance srvSnapDisk_persistent (s : Loc) (γr : ReadNames) :
    Persistent (srvSnapDisk (GF := GF) s γr) := by
  unfold srvSnapDisk; infer_instance

end defs

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- A Texan triple's later continuation used across the call's step (`MemstorageAU.lean`'s). -/
theorem wp_later_frame_srv {e : Expr} {Φ : val → IProp GF} {R : IProp GF}
    (h : toVal e = none) :
    ⊢ ▷ R -∗ WP e {{ v, R -∗ Φ v }} -∗ WP e {{ Φ }} := by
  iintro HR Hwp
  iapply (wp_wand (Φ := fun v => iprop(R ∗ (R -∗ Φ v)))) $$ [HR Hwp]
  · iapply (wp_frame_step_l' h (fun _ hp => hp))
    iframe
  · iintro %v ⟨HR, H⟩
    iapply H $$ HR

/-- An any-term entry for the snapshot `CreateSnapshot(i, cs, data)` makes from the state `σ`
covers it at every term. -/
theorem certCovers_created (σ : StorState) (i t : w64) (oc : Option ConfStateM) (bs : List w8) :
    certCovers (snapTrip (memSnapCreated σ i (W64 0) oc bs)
        (memSnapCreated σ i (W64 0) oc bs).Metadata'.ConfState'.lists, true)
      (snapTrip (memSnapCreated σ i t oc bs) (memSnapCreated σ i t oc bs).Metadata'.ConfState'.lists) := by
  unfold certCovers
  simp only [↓reduceIte]
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- **`CreateSnapshot` over the shared token and the free registry** (see the file header). -/
theorem MemoryStorage.CreateSnapshot.wp_reg
    (wp_CreateSnapshot : MemoryStorage.CreateSnapshot.spec (GF := GF) (hG := hG))
    (ms : Loc) (γs : MemStorNames) (γss : GName) (x i : w64) (cs : Loc) (dq : DFrac)
    (oc : Option ConfStateM) (data : GoSlice) (bs : List w8) (eood : GoInterface)
    (Hx : uint.Z i ≤ uint.Z x) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
        memSnapRO ms γs ∗ memKey γs.ak ∗ memFloorTok ms γs x ∗ memCsArg cs dq oc ∗ data ↦* bs ∗
        globalAddr ErrSnapOutOfDate ↦□ eood ∗
        inv srvStorTokN (memTokShared γs γss) ∗ memCertReg γs }}
      (App (App (App (Val (ms @!! go.GoType.PointerType MemoryStorage.ty @!! go!"CreateSnapshot"))
        (Val #i)) (Val #cs)) (Val #data))
    {{ (snap' : Loc) (err : GoInterface), RET (PairV #snap' #err);
        memKey γs.ak ∗ memCsArg cs dq oc ∗ monoNatLbOwn γss (uint.nat i) ∗
        ((⌜err = eood⌝ ∗ data ↦* bs) ∨
         (⌜err = interface.nil⌝ ∗ ∃ σ t, ownSnapM snap' (DFrac.own 1) (memSnapCreated σ i t oc bs))) }} := by
  have HN := srvStorTokN_disj
  have HN1 := srvCertN_disj_memSnap
  have HN2 := srvCertN_disj_tok
  wp_start_folded as ⟨#Hro, Hak, #Hfw, Hcs, Hdata, #Herr, #Hinv, #Hreg⟩
  iapply (wp_later_frame_srv rfl) $$ HΦ
  iapply wp_CreateSnapshot ms γs x i cs dq oc data bs eood $$ [Hak Hcs Hdata] []
  · iframe Hpkg Hro Hak Hfw Hdata Herr Hcs
  iinv Hinv with >Hi Hclose
  iunfold memTokShared at Hi
  icases Hi with ⟨%σt, Htg, Hss, %Hps⟩
  -- the registry: the created snapshot's any-term entry
  iunfold memCertReg at Hreg
  iinv Hreg with >Hr Hcloser
  icases Hr with ⟨%L, Hra⟩
  imod monoListAuthOwn_update_app
      [(snapTrip (memSnapCreated σt i (W64 0) oc bs)
        (memSnapCreated σt i (W64 0) oc bs).Metadata'.ConfState'.lists, true)] $$ Hra
    with ⟨Hra, #Hlb⟩
  imod Hcloser $$ [Hra] with -
  · inext; iexists _; iexact Hra
  iapply fupd_mask_intro (Std.LawfulSet.empty_subset)
  iintro Hclose2
  iexists σt
  iframe Htg
  isplitr
  · ipureintro
    intro Hlt
    exact ⟨by omega, Hx⟩
  isplitr
  · imodintro
    iintro %t
    iapply memStorCert_of_lb γs _ _ _ (by simp) (certCovers_created σt i t oc bs) $$ Hlb
  isplit
  · -- `ErrSnapOutOfDate`: the storage's snapshot is at or past `i`
    iintro %Hle Htg
    ihave #Hlbi : monoNatLbOwn γss (uint.nat i) $$ [Hss]
    · ihave #Hlb' := monoNatLbOwn_get γss 1 _ $$ Hss
      iapply monoNatLbOwn_le (uint.nat i) (by word) $$ Hlb'
    imod Hclose2 with -
    imod Hclose $$ [Htg Hss] with -
    · inext
      iunfold memTokShared
      iexists σt
      iframe Htg Hss
      ipureintro; exact Hps
    imodintro
    iintro Hak Hcs Hdata HΦ
    iapply HΦ
    iframe Hak Hlbi Hcs
    ileft
    iframe Hdata
    ipureintro; rfl
  · -- the snapshot at `i`: the counter follows
    iintro %t %Hlt Htg
    imod mono_nat_own_update (uint.nat i) (by word) $$ Hss with ⟨Hss, #Hlbi⟩
    imod Hclose2 with -
    imod Hclose $$ [Htg Hss] with -
    · inext
      iunfold memTokShared
      iexists memStorCreated σt i t oc bs
      iframe Htg
      unfold memStorCreated
      iframe Hss
      ipureintro
      show uint.Z σt.prev.index' ≤ uint.Z i
      omega
    imodintro
    iintro %snap' Hsnap Hak Hcs HΦ
    iapply HΦ
    iframe Hak Hlbi Hcs
    iright
    isplitr
    · ipureintro; rfl
    iexists σt, t
    iexact Hsnap

end proof

end EtcdGrove
end Perennial
