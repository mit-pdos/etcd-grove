/-
Lemmas of the request path's proposer side (`InvProposer.lean`): minting a proposal's fresh
token with its id's claim (`srv_claim_mint`), the trivial update a proposal deposits
(`srvPropAu_trivial`), the request with its header (`irrIs_of_noHdr`). Lean-first (no Rocq
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

theorem idN_mintN : (↑idN : CoPset) ⊆ ⊤ \ ↑srvMintN :=
  mask_ndot_ne' nroot "idutil" "server_mint" (by decide)

section lemmas
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

instance idClaim_timeless (γi : IdNames) (id : w64) (d : List w8) :
    Timeless (idClaim (GF := GF) γi id d) := by
  unfold idClaim; infer_instance

instance srvCLog_timeless (γ : ServerRaftNames) (L : List (List w8)) :
    Timeless (srvCLog (GF := GF) γ L) := by
  unfold srvCLog; infer_instance

/-- **Claiming a fresh id for the proposal's data mints the data's fresh token**: the data
decode to a request whose id is `id`, unclaimed until now, so no token of the data exists (every
token is of data claimed under their id). -/
theorem srv_claim_mint (ρ : ReqNames) (g : Loc) (id : w64) (d : List w8) (rq : apply.IRRModel)
    (Hd : apply.irrDecode d = some rq) (Hid : apply.irrId rq = some id) :
    ⊢ idGen (GF := GF) ρ.ids g -∗ srvMintInv ρ -∗ idUnclaimed ρ.ids id ={⊤}=∗
      idClaim ρ.ids id d ∗ srvPropFresh ρ.raft d := by
  iintro #Hg #Hm Hu
  iunfold srvMintInv at Hm
  iinv Hm with >Hi Hclose
  icases Hi with ⟨%F, HF, HFs⟩
  cases hF : F !! d with
  | some u =>
    ihave Hd' := (BigSepM.bigSepM_lookup_acc (Φ := fun d (_u : Unit) => iprop(∃ (rq : apply.IRRModel) (id : w64),
        ⌜apply.irrDecode d = some rq ∧ apply.irrId rq = some id⌝ ∗ idClaim (GF := GF) ρ.ids id d)) hF).1 $$ HFs
    icases Hd' with ⟨⟨%rq', %id', %Hdec, #Hc⟩, -⟩
    obtain ⟨h1, h2⟩ := Hdec
    rw [Hd] at h1; cases h1
    rw [Hid] at h2; cases h2
    iexfalso
    iapply idClaim_unclaimed $$ Hc Hu
  | none =>
    imod idClaim_make ρ.ids g id d (⊤ \ ↑srvMintN) idN_mintN $$ Hg Hu with #Hc
    imod ghost_map_insert d () hF $$ HF with ⟨HF, Hfr⟩
    imod Hclose $$ [HF HFs] with -
    · inext
      iexists (F.insert d ())
      iframe HF
      iapply (BigSepM.bigSepM_insert (Φ := fun d (_u : Unit) => iprop(∃ (rq : apply.IRRModel) (id : w64),
        ⌜apply.irrDecode d = some rq ∧ apply.irrId rq = some id⌝ ∗ idClaim (GF := GF) ρ.ids id d)) hF).2
      iframe HFs
      iexists rq, id
      iframe Hc
      ipureintro; exact ⟨Hd, Hid⟩
    imodintro
    iframe Hc
    iunfold srvPropFresh
    iexact Hfr

/-- **The update a proposal deposits** (`Q` = `True`): the server keeps the client log's other
half in an invariant (`srvCLogInv`), the proposer's result comes through the wait. -/
theorem srvPropAu_trivial (γ : ServerRaftNames) (d : List w8) :
    ⊢ srvCLogInv (GF := GF) γ -∗ srvPropAu γ d (fun _ => iprop(True)) := by
  iintro #Hinv
  unfold srvPropAu
  iauintro
  unfold atomic_acc
  unfold srvCLogInv
  have Hdisj := srvCLogN_raftN
  iinv Hinv with >Hi Hclose
  icases Hi with ⟨%L, HcL⟩
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
  iapply fupd_mask_intro (Std.LawfulSet.empty_subset)
  iintro Hmask
  iexists L
  iframe HcL
  isplit
  · iintro HcL
    imod Hmask with -
    imod Hclose $$ [HcL] with -
    · inext; iexists L; iexact HcL
    imodintro
    itrivial
  · iintro HcL
    imod Hmask with -
    imod Hclose $$ [HcL] with -
    · inext; iexists (L ++ [d]); iexact HcL
    imodintro
    itrivial

end lemmas

section heap
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
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
