/-
Lemmas of the request path's proposer side (`InvProposer.lean`): minting a proposal's fresh
token with its id's claim (`srv_claim_mint`), the request with its header (`irrIs_of_noHdr`). Lean-first (no Rocq
counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvProposer
public import Proof.go_etcd_io.etcd.pkg.v3.idutil.Lemmas

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.api.v3

theorem idClusterN_mintN : (↑idClusterN : CoPset) ⊆ ⊤ \ ↑srvMintN :=
  mask_ndot_ne' nroot "idutil_cluster" "server_mint" (by decide)

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]

instance idClaim_timeless (γi : IdNames) (id : w64) (d : List w8) (γf : GName) :
    Timeless (idClaim (GF := GF) γi id d γf) := by
  unfold idClaim; infer_instance

/-- **Claiming a fresh id for the proposal's data mints the data's fresh token**: the data
decode to a request whose id is `id`, unclaimed until now, so no token of the data exists (every
token is of data claimed under their id). The claim records the proposer's floor `F` (a certified
log its client saw; the vertical slice's unit V2) at a fresh ghost name `γf` (`floorAt`). -/
theorem srv_claim_mint (ρ : ReqNames) (E : apply.AEnv GF) (g : Loc) (id : w64) (d : List w8)
    (rq : apply.IRRModel) (F : mvcc.Log)
    (Hd : apply.irrDecode d = some rq) (Hid : apply.irrId rq = some id)
    (Hp : idPfx id = ρ.ids.pfx) :
    ⊢ idGen (GF := GF) ρ.ids g (srvFloorFact E) -∗ srvMintInv ρ -∗ idUnclaimed ρ.ids id -∗
      mvcc.idxCert E.γ.idx F ={⊤}=∗
      ∃ γf : GName, idClaim ρ.ids id d γf ∗ floorAt γf F ∗ srvPropFresh ρ.raft d := by
  iintro #Hg #Hm Hu #HF
  imod dghostVar_alloc (GF := GF) F with ⟨%γf, Hγ⟩
  imod dghostVar_persist γf 1 F $$ Hγ with #Hγ
  ihave #Hfl : floorAt (GF := GF) γf F $$ []
  · iunfold floorAt; iexact Hγ
  iunfold srvMintInv at Hm
  icases Hm with ⟨#Hm, -⟩
  iunfold srvPropMint at Hm
  iinv Hm with >Hi Hclose
  icases Hi with ⟨%Fm, HF', HFs⟩
  cases hF : Fm !! d with
  | some u =>
    ihave Hd' := (BigSepM.bigSepM_lookup_acc (Φ := fun d (_u : Unit) => iprop(∃ (rq : apply.IRRModel) (id : w64),
        ⌜apply.irrDecode d = some rq ∧ apply.irrId rq = some id⌝ ∗
        ∃ γf : GName, idClaim (GF := GF) ρ.ids id d γf)) hF).1 $$ HFs
    icases Hd' with ⟨⟨%rq', %id', %Hdec, %γ', #Hc⟩, -⟩
    obtain ⟨h1, h2⟩ := Hdec
    rw [Hd] at h1; cases h1
    rw [Hid] at h2; cases h2
    iexfalso
    iapply idClaim_unclaimed $$ Hc Hu
  | none =>
    imod idClaim_make ρ.ids g (srvFloorFact E) id d γf (⊤ \ ↑srvMintN) idClusterN_mintN
      $$ Hg Hu %Hp [] with #Hc
    · imodintro
      iunfold srvFloorFact
      iexists F
      iframe Hfl HF
    imod ghost_map_insert d () hF $$ HF' with ⟨HF', Hfr⟩
    imod Hclose $$ [HF' HFs] with -
    · inext
      iexists (Fm.insert d ())
      iframe HF'
      iapply (BigSepM.bigSepM_insert (Φ := fun d (_u : Unit) => iprop(∃ (rq : apply.IRRModel) (id : w64),
        ⌜apply.irrDecode d = some rq ∧ apply.irrId rq = some id⌝ ∗
        ∃ γf : GName, idClaim (GF := GF) ρ.ids id d γf)) hF).2
      iframe HFs
      iexists rq, id
      isplitr
      · ipureintro; exact ⟨Hd, Hid⟩
      iexists γf
      iexact Hc
    imodintro
    iexists γf
    iframe Hc Hfl
    iunfold srvPropFresh
    iexact Hfr

end lemmas

section heap
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]
variable [package_sem : go_etcd_io.etcd.api.v3.etcdserverpb.Assumptions]

/-- The request with its header set (and the header field read-only from then on). -/
theorem irrIs_of_noHdr (p h : Loc) (rq : apply.IRRModel) (hm : apply.HeaderModel) :
    irrNoHdrIs (GF := GF) p rq ∗
      structFieldRef etcdserverpb.InternalRaftRequest go!"Header" p ↦□ h ∗ apply.headerIs h hm ⊢
    apply.internalRaftRequestIs p (apply.withHeader rq hm) := by
  iintro ⟨Hno, #Hh, #Hhm⟩
  iunfold irrNoHdrIs at Hno
  iunfold apply.internalRaftRequestIs
  icases Hno with ⟨%Hpn, #HID, #H1, #H2, #H3, #H4, #H5, #H6, #H7, #H8, #H9, #H10, #H11, #H12,
    #H13, #H14, #H15, #H16, #H17, #H18, #H19, #H20, #H21, #H22, #H23, #H24, #H25, #H26, #H27,
    #H28, #H29, #H30⟩
  simp only [apply.withHeader]
  iframe #
  isplitr
  · ipureintro; exact Hpn
  iexists h
  iframe #
  simp only [apply.optReqIs]
  iexact Hhm

end heap

end EtcdGrove
end Perennial
