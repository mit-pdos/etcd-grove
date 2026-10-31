/-
**Certifying the server's snapshot** (2026-10-31, the snapshot track, #9:
`notes/snapshot-sorries-plan.md`). `EtcdServer.snapshot` creates a raft snapshot of the applied
prefix (`CreateSnapshot(ep.appliedi, ep.confState, nil)`), which `CreateSnapshot.spec` takes valid
(`J.SV`, `snapshotValid`). As kv's `kv_snap_make`: the applied prefix is committed (`srvRLogLb`), its
membership the voters' (`srv_confAt_simple`, D3), `ep.confState` reports them (`epCsCfg`), so the
snapshot is recorded in the cluster's registry (`snapshotCert_make`, in `srvClusterOk`'s invariant)
and valid (`snapshotCert_valid`). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvApplyAll
public import Spec.go_etcd_io.raft.v3.MemoryStorage__CreateSnapshot

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

theorem srvClusterN_snapsN : (↑srvClusterN : CoPset) ⊆ ⊤ \ ↑srvSnapsN :=
  fun x h => mask_ndot_ne' nroot "raft_commit" "server_snaps" (by decide) x (srvClusterN_sub x h)

section cert
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]

/-- The voters' membership's conf state has well-formed lists (`snapshotCert_make`'s
`SnapListsOk`), for fewer than `2^61` voters at an index below `2^61`. -/
theorem srv_snapListsOk (γ : SrvRaft) (cs : ConfStateM) (t i : w64)
    (hv : (Membership.simple γ.cfg).Valid) (hr : (Membership.simple γ.cfg).Restorable)
    (hcs : confStateIs cs (Membership.simple γ.cfg)) (hsz : GMap.size γ.cfg < 2 ^ 61)
    (hi : uint.Z i < 2 ^ 61) :
    SnapListsOk ⟨⟨t, i⟩, cs.lists, (Membership.simple γ.cfg).autoLeave, []⟩ := by
  refine Membership.Valid.snapListsOk hv hcs hr.1 hr.2 ?_ hi
  have : (Membership.simple γ.cfg).ids = γ.cfg := by
    apply GMap.set_eq; intro x
    simp [Membership.ids, Membership.simple, GMap.elem_of_union, GMap.not_elem_of_empty]
  rw [this]; exact hsz

/-- **The server's snapshot at the applied index `ai` of term `at'`, valid** (see the file
header): of the applied prefix `A` (committed, `ai` long, ending at `at'`), at the conf state `c`
of the voters. A fancy update: it registers the snapshot in the cluster's registry. -/
theorem srv_snap_make (γr : ReadNames) (A : List EntryModel) (ai at' : w64) (c : ConfStateM)
    (hpos : 0 < uint.Z ai) (h61 : uint.Z ai < 2 ^ 61) (hsz : GMap.size γr.raft.raft.cfg < 2 ^ 61)
    (hlen : uint.Z ai = A.length) (hlast : lastTermIs A at')
    (hcs : confStateIs c (Membership.simple γr.raft.raft.cfg)) :
    letI := srvStor (GF := GF) γr.raft.raft
    srvRaftLogInv (GF := GF) γr.raft ∗ srvRLogLb γr.raft A ⊢
      |={⊤}=> snapshotValid γr.raft.raft.cl (memSnapMade ai at' c []) := by
  letI := srvStor (GF := GF) γr.raft.raft
  iintro ⟨#Hinv, #Hlb⟩
  ihave #Hinv' := Hinv
  iunfold srvRaftLogInv at Hinv'
  icases Hinv' with ⟨-, #Hcl, -, -, %Hpre⟩
  iunfold srvClusterOk at Hcl
  icases Hcl with ⟨#Hc, -, -, -, -, #Hreg, -⟩
  iunfold srvRLogLb at Hlb
  icases Hlb with ⟨#Hl, -⟩
  -- the committed prefix, `ai` long, its last term `at'`
  have hl : (srvLE γr.raft A).length = uint.nat ai := by
    simp only [srvLE, Hpre, List.nil_append, List.length_map]
    have := uint_nat_eq ai
    omega
  have hne : A ≠ [] := by
    intro h; subst h; simp only [List.length_nil] at hlen; omega
  have hlt : Option.map LogEntry.term (srvLE γr.raft A).getLast? = some at' := by
    rcases hlast with h | h
    · exact absurd h hne
    simp only [srvLE, Hpre, List.nil_append, List.getLast?_map, Option.map_map]
    rw [← h]
    rfl
  imod (srv_confAt_simple γr.raft (srvLE γr.raft A) (srvLE γr.raft A).length (Nat.le_refl _) ⊤
    (by simp) (by simp)) $$ [Hinv Hl] with #Ha
  · iframe Hinv Hl
  ihave %Hv := confAt_valid γr.raft.raft.cl _ _ $$ Ha
  ihave %Hr := confAt_restorable γr.raft.raft.cl _ _ $$ Ha
  have Hok := srv_snapListsOk γr.raft.raft c at' ai Hv Hr hcs hsz h61
  -- registered in the cluster's registry, so valid
  iinv Hreg with >Hb Hclose
  all_goals first | exact (fun _ _ => CoPset.mem_full) | skip
  icases Hb with ⟨%S, Hown⟩
  imod snapshotCert_make γr.raft.raft.cl srvClusterN (⊤ \ ↑srvSnapsN) (srvLE γr.raft A) ai at' []
      (Membership.simple γr.raft.raft.cfg) c S srvClusterN_snapsN hl hlt Hok hcs
    $$ Hc Hl Ha Hown with ⟨Hown, #Hcert⟩
  imod Hclose $$ [Hown] with -
  · inext
    iexists S ++ [⟨(srvLE γr.raft A).length, Membership.simple γr.raft.raft.cfg, []⟩]
    iexact Hown
  imodintro
  iapply snapshotCert_valid γr.raft.raft.cl srvClusterN (memSnapMade ai at' c []) hpos h61
  iframe Hc
  simp only [snapTrip, snapId, memSnapMade]
  have hal : c.AutoLeave' = (Membership.simple γr.raft.raft.cfg).autoLeave := hcs.2.2.2.2
  rw [hal]
  iexact Hcert

/-- **`CreateSnapshot(ai, ep.confState, nil)` by the apply thread** (`EtcdServer.snapshot`'s): the
snapshot certified first (`srv_snap_make`), `CreateSnapshot.spec` at the node's justifications
(`memStorJ`, `srvSnapStor`'s `memStorInv`); afterwards the stored snapshot past `ai`, and the
snapshot, owned, of the voters' conf state, or `ErrSnapOutOfDate`. -/
theorem wp_srv_createSnapshot
    (hCS : MemoryStorage.CreateSnapshot.spec (GF := GF) (hG := hG))
    (ms : Loc) (γs : MemStorNames) (γr : ReadNames) (nid ai at' : w64) (cs : Loc) (eood : GoInterface)
    (hpos : 0 < uint.Z ai) (hsz : GMap.size γr.raft.raft.cfg < 2 ^ 61) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ srvSnapStor ms γs γr nid ai at' ∗
        epCsCfg γr cs ∗ srvFrozenTerm γs ai at' ∗ memSnapLb γs 0 ∗
        globalAddr ErrSnapOutOfDate ↦□ eood }}
      (App (App (App (Val (ms @!! go.GoType.PointerType MemoryStorage.ty @!! go!"CreateSnapshot"))
        (Val #ai)) (Val #cs)) (Val #slice.nil))
    {{ (snap : Loc) (err : GoInterface), RET (PairV #snap #err); memSnapLb γs (uint.nat ai) ∗
        ((⌜err = interface.nil⌝ ∗ ∃ c : ConfStateM,
            ownSnapM snap (DFrac.own 1) (memSnapMade ai at' c [])) ∨
         ⌜snap = null ∧ err = eood⌝) }} := by
  iintro %Φ ⟨#Hpkg, Hstor, #Hecs, #Hft, #Hlb0, #Heood⟩ HΦ
  iunfold srvSnapStor at Hstor
  icases Hstor with ⟨#Hmsi, Hdl, #Hrli, ⟨%A, #HA, %HAp⟩⟩
  iunfold epCsCfg at Hecs
  icases Hecs with ⟨%c, #Hc, %Hcs⟩
  iunfold srvFrozenTerm at Hft
  icases Hft with ⟨%e, #He, %Hterm⟩
  subst Hterm
  ihave %Hb := memLog_bound γs (uint.nat ai) DFrac.discard [e] $$ He
  have h61 : uint.Z ai < 2 ^ 61 := by
    rcases Hb with h | h
    · cases h
    · have := uint_nat_eq ai; simp only [List.length_singleton] at h; omega
  imod (srv_snap_make γr A ai e.Term' c hpos h61 hsz HAp.1 HAp.2 Hcs) $$ [Hrli HA] with #HSV
  · iframe Hrli HA
  letI : MemStorReg GF := ⟨γr.raft.raft.reg⟩
  ihave Hnil : (slice.nil ↦* ([] : List w8) : IProp GF) $$ []
  · iapply ownSlice_nil
  wp_apply hCS ms γs (memStorJ γr.raft.raft.cl nid) ai e cs DFrac.discard c slice.nil [] eood
    $$ [Hnil Hdl] as %snap %err ⟨-, #Hlb, Hres⟩
  · simp only [memStorJ]
    iframe Hnil Hdl
    iframe #
    iExactEq Hmsi
    rfl
  iapply HΦ
  iframe Hlb
  icases Hres with (⟨%Herr, Hsn⟩ | ⟨%Herr, -⟩)
  · ileft
    isplitr
    · ipureintro; exact Herr
    iexists c
    iexact Hsn
  · iright
    ipureintro; exact Herr

end cert

end EtcdGrove
end Perennial
