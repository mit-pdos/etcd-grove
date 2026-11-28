/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/etcd/restartN/Run.lean` (`notes/restartN-plan.md`).
Lean-first (no Rocq counterpart). putgetN's start (the members, `etcdstart.allocN`, each member paired with
its ghost names and premises), each member's restart facts and compaction mode taken out of its boot bundle
first (`pres_restartFacts`), `startMembers`; restart1's KV invariant at 25 puts (`r3Inv_alloc`, at the
cluster's KV names, moved to member `0`'s by `r3Inv_st`), the `N1` puts through member `0` (`member0_of`);
the stopped member chosen by `k > 2 && srvs[k-1].Leader() == srvs[k-1].MemberID()` (the `if` proved with a
postcondition naming the chosen member, `stopCand`, built by `stopCand_of` from the member's started
resources, its restart facts and its restart contract; members `0`, `k - 1` and `k - 2` taken out of the
started members' big separating conjunction by `bigSepL_delete`); then restart3's steps: the stop, the `N2`
puts, the restart and the check.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.restartN.Run
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.restartN.startMembers
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.restartN.put
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.restartN.stop
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.restartN.check
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__Leader
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__MemberID
public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Members
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.AllocN
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.restart1.Defs
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.restartN.Dir

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_restartN

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver etcdstart
open etcd_restart

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.restartN.Assumptions]

/-- **Each member with its ghost names and its premises** (putgetN's `memberPres_of`, at `memberPreU`: 2026-11-27,
`bootstrap`'s contract borrowing every member's peer address). -/
theorem memberPres_of (N : Nat) (ms0 : List GMember) (ps : List w64)
    (bootLog : List EntryM) (ctxs : List (List w8)) (dir : w64 → List GoString)
    (Φs : w64 → w64 → List w8 → GName → IProp GF) (γn : NetNames GF)
    (ms : List GMember) (gs : List (MemberG GF)) (ids : List w64)
    (hids : gs.map (·.id) = ids) (hlen : ms.length = gs.length) :
    ⊢ ([∗list] m; id ∈ ms; ids,
        etcdstart.bootPremiseF (peersFree ms0) N ps bootLog ctxs dir token m.Name' (urlsN ms0 m) id) -∗
      (□ ∀ lid : w64, netHttpOk γn lid) -∗
      ([∗list] g ∈ gs, memberBoot g.γ ctxs g.ρ g.E Φs g.id) -∗
      ([∗list] m ∈ ms, memberFreshRes m.Name' ⟨some m.Peer', none⟩ γn) -∗
      [∗list] x ∈ ms.zip gs, memberPreU N ms0 ps bootLog ctxs dir Φs γn x := by
  induction ms generalizing gs ids with
  | nil =>
    iintro _ _ _ _
    simp only [List.zip_nil_left]
    iempintro
  | cons m ms ih =>
    cases gs with
    | nil => simp at hlen
    | cons g gs =>
      subst hids
      simp only [List.map_cons]
      iintro Hbp #Hnet Hb Hf
      ihave Hbp := BigSepL2.bigSepL2_cons.1 $$ Hbp
      ihave Hb := BigSepL.bigSepL_cons.1 $$ Hb
      ihave Hf := BigSepL.bigSepL_cons.1 $$ Hf
      icases Hbp with ⟨Hbp1, Hbp⟩
      icases Hb with ⟨Hb1, Hb⟩
      icases Hf with ⟨Hf1, Hf⟩
      rw [List.zip_cons_cons]
      iapply BigSepL.bigSepL_cons.2
      isplitl [Hbp1 Hb1 Hf1]
      · iunfold memberPreU
        iframe
        iapply Hnet
      iapply (ih gs (gs.map (·.id)) rfl (by simpa using hlen)) $$ Hbp Hnet Hb Hf

/-- **Each member's restart facts and compaction mode** (persistent), out of its boot bundle before
the start (restart3 took them from members 2 and 3; here from every member, any of the last two may be
stopped). -/
theorem pres_restartFacts (N : Nat) (ms : List GMember) (ps : List w64)
    (bootLog : List EntryM) (ctxs : List (List w8)) (dir : w64 → List GoString)
    (Φs : w64 → w64 → List w8 → GName → IProp GF) (γn : NetNames GF)
    (xs : List (GMember × MemberG GF)) :
    ([∗list] x ∈ xs, memberPreU N ms ps bootLog ctxs dir Φs γn x) ⊢
      ([∗list] x ∈ xs, memberPreU N ms ps bootLog ctxs dir Φs γn x) ∗
      [∗list] x ∈ xs, iprop(memberRestartFacts x.2.γ x.2.ρ x.2.id ∗ ⌜x.2.E.cmp = false⌝) := by
  induction xs with
  | nil =>
    iintro _
    isplitr <;> iempintro
  | cons x xs ih =>
    iintro H
    ihave H := BigSepL.bigSepL_cons.1 $$ H
    icases H with ⟨H1, H⟩
    icases ih $$ H with ⟨H, Hr⟩
    iunfold memberPreU at H1
    icases H1 with ⟨#Hbp, Hmb, #Hnet, Hfr⟩
    icases etcdstart.memberBoot_cmp _ _ _ _ _ _ false $$ Hmb with ⟨%hc, Hmb⟩
    icases etcdstart.memberBoot_restartFacts _ _ _ _ _ _ $$ Hmb with ⟨#Hrf, Hmb⟩
    isplitl [Hmb Hfr H]
    · iapply BigSepL.bigSepL_cons.2
      isplitl [Hmb Hfr]
      · iunfold memberPreU
        iframe; iframe #
      iexact H
    · iapply BigSepL.bigSepL_cons.2
      isplitr
      · iframe #; ipureintro; exact hc
      iexact Hr

/-- **A started server's leader and member-id fields** (restart3's). -/
theorem leadInv_memberID_of_req (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) :
    isServerReq (GF := GF) s E ρ ⊢ srvLeadInv s ∗ ∃ mid : w64, srvMemberIDAddr s ↦□ mid := by
  iintro #Hreq
  iunfold isServerReq at Hreq
  icases Hreq with ⟨⟨%v, #Hv⟩, -⟩
  iunfold srvReqFieldsAt at Hv
  icases Hv with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, #Hmid, #Hlead, -⟩
  isplitl
  · iunfold srvLeadInv
    iunfold srvAtomicU64 at Hlead
    iexact Hlead
  · iexists v.memberID
    iexact Hmid

/-- **Member `0`'s request view** (for the puts), from its started resources, the thread token
given back. -/
theorem member0_of (hRS : mvcc.api.mvccReaders_split.law (GF := GF)) (lg : Loc) (γn : NetNames GF)
    (z : Loc × Loc) (x : GMember × MemberG GF) :
    memberStarted (GF := GF) lg γn z x -∗ threadTok -∗
      threadTok ∗ ∃ (Ea : apply.AEnv GF) (γw : GName), ⌜Ea.authOn = false⌝ ∗
        isServerReq z.1 Ea { x.2.ρ with wait := γw } ∗ srvRevokeBuilt z.1 Ea := by
  iintro Hst Htok
  iunfold memberStarted at Hst
  icases Hst with ⟨Hup, -, -⟩
  ihave Hup := Hup $$ Htok
  icases etcd_restart1.memberUp_splitStop hRS _ _ _ _ _ _ .none $$ Hup with
    ⟨%Ea, %γw, %dd, %HE, #Hreq, -, #Hrvb, Hgo, -, -⟩
  iunfold srvGoRes at Hgo
  icases Hgo with ⟨-, Htok⟩
  iframe Htok
  iexists Ea, γw
  iframe #
  ipureintro; exact HE.2

/-- **The member a run stops** (the `if`'s postcondition): its record, the right to stop it and what
the stop takes, and what its restart takes (the restart contract, the cluster's persistent facts at its
names), at its name, addresses and id; its KV names the cluster's. -/
def stopCand (N : Nat) (m s : Loc) (γn : NetNames GF) (γ : SrvRaft) (γk : KVNames) (ms : List GMember)
    (ids : List w64) (ps : List w64) (ctxs : List (List w8)) (boot : List LogEntry) : IProp GF :=
  iprop(∃ (x : GMember) (id : w64) (reg : GName) (ρ : ReqNames) (E : apply.AEnv GF) (dd : GoString)
      (γS : SwNames),
    ⌜go!"http://" ++ x.Peer' ∈ dirN ms ids id ∧ x ∈ ms ∧ ρ.rd.kv.st = γk.st ∧ srvStop.scope E⌝ ∗
    memberRec m γS γn x.Name' x.Peer' x.Client' ∗ srvAppliedInv s E ρ.rd ∗
    srvDataDir s (memberDataDir x.Name') ∗ srvStopRight s E ρ.rd.raft.raft ρ id dd ∗ srvStopReaders E ∗
    netHttpOk γn id ∗
    etcdstart.bootPremiseR N ps (LogEntry.toEntries boot 0) ctxs (dirN ms ids) token x.Name'
      (urlsN ms x) id ∗
    etcdstart.memberRestartFacts { γ with reg := reg } ρ id)

/-- **A candidate's stop bundle** (`stopCand`), from its started resources, its restart facts, its
network's HTTP side and its restart contract; with its leader and member-id fields (for the `if`), the
thread token given back. -/
theorem stopCand_of (hRS : mvcc.api.mvccReaders_split.law (GF := GF)) (N : Nat) (lg : Loc)
    (γn : NetNames GF) (γ : SrvRaft) (γk : KVNames) (ms : List GMember) (ids : List w64) (ps : List w64)
    (ctxs : List (List w8)) (boot : List LogEntry) (z : Loc × Loc) (x : GMember × MemberG GF)
    (hgok : memberGOk γ γk x.2) (hd : go!"http://" ++ x.1.Peer' ∈ dirN ms ids x.2.id)
    (hxm : x.1 ∈ ms) :
    memberStarted (GF := GF) lg γn z x -∗ threadTok -∗
      iprop(memberRestartFacts x.2.γ x.2.ρ x.2.id ∗ ⌜x.2.E.cmp = false⌝) -∗ netHttpOk γn x.2.id -∗
      etcdstart.bootPremiseR N ps (LogEntry.toEntries boot 0) ctxs (dirN ms ids) token x.1.Name'
        (urlsN ms x.1) x.2.id -∗
      threadTok ∗ srvLeadInv z.1 ∗ (∃ mid : w64, srvMemberIDAddr z.1 ↦□ mid) ∗
        stopCand N z.2 z.1 γn γ γk ms ids ps ctxs boot := by
  obtain ⟨⟨r, hr⟩, hst, -⟩ := hgok
  iintro Hst Htok Hrf #Hnet #HbR
  icases Hrf with ⟨#Hrf, %hc⟩
  iunfold memberStarted at Hst
  icases Hst with ⟨Hup, ⟨%γS, Hrec⟩, #Hdd⟩
  ihave Hup := Hup $$ Htok
  icases etcd_restart1.memberUp_splitStop hRS _ _ _ _ _ _ .none $$ Hup with
    ⟨%Ea, %γw, %dd, %HE, #Hreq, #Hrd, -, Hgo, Hsr, Hrds⟩
  iunfold srvGoRes at Hgo
  icases Hgo with ⟨-, Htok⟩
  ihave ⟨#Hlead, %mid, #Hmid⟩ := leadInv_memberID_of_req z.1 Ea { x.2.ρ with wait := γw } $$ Hreq
  ihave #Hai := isServerRead_applied z.1 Ea x.2.ρ.rd $$ Hrd
  ihave #Hrf' : etcdstart.memberRestartFacts { γ with reg := r } x.2.ρ x.2.id $$ []
  · rw [← hr]; iexact Hrf
  iframe Htok
  isplitr
  · iexact Hlead
  isplitr
  · iexists mid; iexact Hmid
  iunfold stopCand
  iexists x.1, x.2.id, r, x.2.ρ, Ea, dd, γS
  iframe Hrec Hsr Hrds
  iframe #
  ipureintro
  exact ⟨hd, hxm, hst, HE.2, by rw [HE.1.2.2.2, hc]⟩

/-- **The `j`-th started member's facts** (pure): its pair of the servers' and records' slices, its
member and ghost names, its id. -/
theorem cand_facts (k : Nat) (gs : List (MemberG GF)) (ids : List w64) (hgids : gs.map (·.id) = ids)
    (zs : List (Loc × Loc)) (j : Nat) (p : (Loc × Loc) × (GMember × MemberG GF))
    (h : (zs.zip ((members k).zip gs))[j]? = some p) :
    zs[j]? = some p.1 ∧ ((members k).zip gs)[j]? = some p.2 ∧ (members k)[j]? = some p.2.1 ∧
      ids[j]? = some p.2.2.id := by
  rw [List.getElem?_zip_eq_some] at h
  obtain ⟨h1, h2⟩ := h
  have h2' := h2
  rw [List.getElem?_zip_eq_some] at h2'
  refine ⟨h1, h2, h2'.1, ?_⟩
  rw [← hgids, List.getElem?_map, h2'.2]; rfl

/-- **A stop candidate's restart contract** (`premises`' second part, at the member's index `j`, one of
the last `nStop k`). -/
theorem bootR_at (k N : Nat) (ids ps : List w64) (ctxs : List (List w8)) (boot : List LogEntry)
    (j : Nat) (m : GMember) (id : w64) (hj : k - nStop k ≤ j) (hm : (members k)[j]? = some m)
    (hid : ids[j]? = some id) :
    ([∗list] m; id ∈ (members k).drop (k - nStop k); ids.drop (k - nStop k),
      etcdstart.bootPremiseR (GF := GF) N ps (LogEntry.toEntries boot 0) ctxs (dirN (members k) ids) token
        m.Name' (urlsN (members k) m) id) ⊢
    etcdstart.bootPremiseR N ps (LogEntry.toEntries boot 0) ctxs (dirN (members k) ids) token
      m.Name' (urlsN (members k) m) id := by
  have e : k - nStop k + (j - (k - nStop k)) = j := by omega
  refine BigSepL2.bigSepL2_lookup (i := j - (k - nStop k)) ?_ ?_
  · rw [List.getElem?_drop, e]; exact hm
  · rw [List.getElem?_drop, e]; exact hid

/-- `put(s, j)` at a `w64` argument (restart3's). -/
theorem wp_put' (wp_put : put.spec (GF := GF) (hG := hG)) (s : Loc) (E : apply.AEnv GF)
    (ρ : ReqNames) (γc : GName) (j : w64) (h0 : 0 ≤ sint.Z j) (hj : sint.Z j < r3NPuts)
    [ReceiptBoundLe GF (2 ^ 48)] (hE : E.authOn = false) (hlv : srvLevels (GF := GF)) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.restartN ∗
        isServerReq s E ρ ∗ srvRevokeBuilt s E ∗ threadTok ∗
        r3Inv ρ.kv γc ∗ monoNatAuthOwn γc (1 : Qp).half (sint.nat j) }}
      (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.restartN.put))
        (Val #s)) (Val #j))
    {{ (err : GoInterface), RET #err; threadTok ∗
        ((⌜err = GoInterface.nil⌝ ∗ monoNatAuthOwn γc (1 : Qp).half (sint.nat j + 1)) ∨
          ⌜err ≠ GoInterface.nil⌝) }} := by
  have hw := wp_put s E ρ γc (sint.nat j) (by unfold sint.nat; unfold sint.Z at h0 hj; omega)
    hE hlv
  rwa [show W64 ((sint.nat j : Nat) : Int) = j by unfold sint.nat; word] at hw

set_option maxHeartbeats 8000000 in
theorem Run.wp_proof
    (wp_Members : etcdstart.Members.spec (GF := GF) (hG := hG))
    (wp_startMembers : startMembers.spec (GF := GF) (hG := hG))
    (wp_put : put.spec (GF := GF) (hG := hG))
    (wp_Leader : EtcdServer.Leader.spec (GF := GF) (hG := hG))
    (wp_MemberID : EtcdServer.MemberID.spec (GF := GF) (hG := hG))
    (wp_stop : stop.spec (GF := GF) (hG := hG))
    (wp_restartMember : restartMember.spec (GF := GF) (hG := hG))
    (wp_check : check.spec (GF := GF) (hG := hG))
    (hne : mvcc.api.names_nonempty.law) (hRS : mvcc.api.mvccReaders_split.law (GF := GF))
    (hbcfg : ∀ (dir : w64 → List GoString) (ps : List w64), (∀ f, dir f ≠ [] ↔ f ∈ ps) →
      ps.length ≤ 1000 → rafthttp.bootCfg dir ps)
    -- (premises to axioms, 2026-11-24: until then the premise `bootMarshal`) `proto.Marshal`'s spec at a boot conf change
    (wp_MarshalBoot : proto.MarshalBootConfChange.spec (GF := GF) (hG := hG)) :
    Run.spec (GF := GF) (hG := hG) := by
  intro k lg N ids ps ctxs boot ThB RcB RcN hk Hlen Hbf HLv HwbN Haf Hbuq Hdbo
  have Hrb48 := ReceiptBoundLe.le (GF := GF) (2 ^ 48)
  -- the loops' counters (stated here, in a small context)
  have L1 : ∀ (a b : Int) (j : w64), sint.Z (W64 a) = a → sint.Z (W64 b) = b → 0 ≤ a → a ≤ sint.Z j →
      sint.Z j < b → b < 2 ^ 32 →
      sint.nat (j + W64 1) = sint.nat j + 1 ∧ a ≤ sint.Z (j + W64 1) ∧ sint.Z (j + W64 1) ≤ b := by
    intro a b j ha hb h0 h1 h2 h3
    unfold sint.nat
    refine ⟨by word, by word, by word⟩
  have L3 : ∀ (b : Int) (j : w64), sint.Z (W64 b) = b → 0 ≤ sint.Z j → ¬ sint.Z j < b → sint.Z j ≤ b →
      sint.nat j = b.toNat := by
    intro b j hb h0 h1 h2
    have : sint.Z j = b := by omega
    show (sint.Z j).toNat = b.toNat
    rw [this]
  wp_start as ⟨#Hzlg, Hss, Htok, #Hprem⟩
  iunfold premises at Hprem
  icases Hprem with ⟨#Hbps, #HbRs⟩
  -- (premises to axioms, 2026-11-24: until then the premise `bootMarshal`) `proto.Marshal`'s bytes at the
  -- bootstrap log's conf changes, from its trust-boundary spec and the log's bytes (`Hbf.wire`)
  ihave #Hpp : isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.protobuf.proto $$ []
  · iPkgInit
  ihave #Hmarsh := bootMarshal_of_spec wp_MarshalBoot _ _ _ Hbf.wire $$ Hpp
  ihave #Hcci : context.isClosedchanInit (GF := GF) $$ []
  · iapply context.isClosedchanInit_of_init
    iPkgInit
  ihave #Pes : isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart $$ []
  · iPkgInit
  ihave #Psrv : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver $$ []
  · iPkgInit
  (try wp_auto)
  -- `if k < 2 { return false }`
  wp_if_destruct
  · (try wp_auto)
    iapply HΦ; itrivial
  have hkz : uint.Z (W64 (k : Int)) = k := by word
  have hk2 : 2 ≤ k := by
    rw [hkz] at Hif; simp only [show uint.Z (W64 2) = 2 from rfl] at Hif; omega
  -- the pure facts of the members and their ids (putgetN's)
  obtain ⟨Hpnd, -, -⟩ := idPfxsOf_ok ps Hbf.lowNodup Hbf.lowNz
  have Hpsnd : ps.Nodup := by
    unfold idPfxsOf at Hpnd
    exact List.Pairwise.of_map _ (fun a b h e => h (by rw [e])) Hpnd
  have Hidnd : ids.Nodup := Hbf.perm.nodup_iff.1 Hpsnd
  have Hid0 : W64 0 ∉ ids := fun h => Hbf.lowNz _ (Hbf.perm.symm.subset h) (by decide)
  have Hmlen : (members k).length = ids.length := by rw [membersOf_length, Hlen]
  have Hdok : netDirOk (dirN (members k) ids) :=
    etcd_putgetN.dirN_ok _ ids Hidnd Hid0 (members_peers_nodup k hk) (members_peer_plain k)
  have Hbc : rafthttp.bootCfg (dirN (members k) ids) ps :=
    hbcfg _ ps (fun f => by rw [etcd_putgetN.dirN_ne_nil _ ids Hmlen Hidnd, Hbf.perm.mem_iff])
      (by rw [Hbf.perm.length_eq, Hlen]; exact hk)
  have hblen : boot.length = k := by rw [Hbf.boot.1, Hbf.perm.length_eq, Hlen]
  obtain ⟨id0, hid0⟩ : ∃ id0, id0 ∈ ids := by
    cases ids with
    | nil => simp at Hlen; omega
    | cons a _ => exact ⟨a, by simp⟩
  -- the ghost state of the cluster and its members (`allocN`)
  ihave Hss : [∗list] m ∈ (members k).map (fun m => (m.Name', m.Peer', (none : Option GoString))),
      memberStartRes (GF := GF) m.1 ⟨some m.2.1, m.2.2⟩ $$ [Hss]
  · rw [BigSepL.bigSepL_map]; iexact Hss
  imod (allocN hne ids ps Hbf.perm id0 hid0 ctxs boot Hbf.toBootCore (dirN (members k) ids)
      ((members k).map (fun m => (m.Name', m.Peer', (none : Option GoString)))) Hdok.1
      (fun i h hm => by rw [List.map_map]; exact etcd_putgetN.dirN_host _ ids i h hm)
      (by omega) (by omega) .none lease.runCfg_none (fun h => nomatch h))
      $$ Hmarsh Hss
    with ⟨%γ, %γk, %Φs, %γn, %gs, %Hal, #Hnet, Hbs, Hfrs, Hetcd⟩
  isimp only [ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte] at Hetcd
  obtain ⟨hvs, hrule, hboot, hγn1, hγn2, hgids, hgok, hc0, hch, hlog, -, -⟩ := Hal
  have hglen : (members k).length = gs.length := by
    rw [Hmlen, ← hgids, List.length_map]
  ihave Hfrs : [∗list] m ∈ members k, memberFreshRes m.Name' ⟨some m.Peer', none⟩ γn $$ [Hfrs]
  · rw [BigSepL.bigSepL_map] at *; iexact Hfrs
  -- `ETCD_VERIFY` off (kept from member `0`'s fresh bundle; every incarnation's)
  obtain ⟨m0, mr, hms⟩ : ∃ m0 mr, members k = m0 :: mr := by
    cases h : members k with
    | nil => rw [h] at Hmlen; simp at Hmlen; omega
    | cons a r => exact ⟨a, r, rfl⟩
  ihave Hfrs : [∗list] m ∈ m0 :: mr, memberFreshRes m.Name' ⟨some m.Peer', none⟩ γn $$ [Hfrs]
  · rw [← hms]; iexact Hfrs
  ihave Hfrs := BigSepL.bigSepL_cons.1 $$ Hfrs
  icases Hfrs with ⟨Hfr0, Hfrs⟩
  icases etcdstart.memberFreshRes_verify _ _ _ $$ Hfr0 with ⟨#Hvoff, Hfr0⟩
  ihave Hfrs : [∗list] m ∈ members k, memberFreshRes m.Name' ⟨some m.Peer', none⟩ γn $$ [Hfr0 Hfrs]
  · rw [hms]; iapply BigSepL.bigSepL_cons.2; iframe
  -- each member with its ghost names and its premises; its restart facts
  ihave Hpres := memberPres_of N (members k) ps (LogEntry.toEntries boot 0) ctxs
    (dirN (members k) ids) Φs γn (members k) gs ids hgids hglen $$ Hbps Hnet Hbs Hfrs
  icases pres_restartFacts N (members k) ps (LogEntry.toEntries boot 0) ctxs
    (dirN (members k) ids) Φs γn ((members k).zip gs) $$ Hpres with ⟨Hpres, #Hrfs⟩
  have hxs1 : ((members k).zip gs).map (·.1) = members k := List.map_fst_zip (by omega)
  have hutf : ∀ x ∈ (members k).zip gs, utf8Valid x.1.Name' :=
    fun x hx => members_names_utf8 k _ (List.of_mem_zip hx).1
  have hnlen : ∀ x ∈ (members k).zip gs, x.1.Name'.length ≤ 200 :=
    fun x hx => members_names_len k _ (List.of_mem_zip hx).1
  -- (fmt stage 1, 2026-11-24) the members' addresses within etcd's URL bounds
  have haf : ∀ x ∈ (members k).zip gs, etcdstart.addrFits x.1.Peer' ∧ etcdstart.addrFits x.1.Client' :=
    fun x hx => etcdstart.membersOf_addrFits _ _ _ _ x.1 (List.of_mem_zip hx).1
  have hnd : (((members k).zip gs).map (·.1.Name')).Nodup := by
    rw [show ((members k).zip gs).map (·.1.Name') = (((members k).zip gs).map (·.1)).map (·.Name')
      by rw [List.map_map]; rfl, hxs1]
    exact members_names_nodup k hk
  have hdx : ∀ x ∈ (members k).zip gs, go!"http://" ++ x.1.Peer' ∈ dirN (members k) ids x.2.id := by
    intro x hx
    have hmz : (x.1, x.2.id) ∈ (members k).zip ids := by
      rw [← hgids, List.zip_map_right]
      exact List.mem_map_of_mem (f := Prod.map id (·.id)) hx
    rw [show dirN (members k) ids = etcd_putgetN.dirN (members k) ids from rfl,
      etcd_putgetN.dirN_of_mem _ ids Hidnd _ _ hmz]
    simp
  have hxok : ∀ x ∈ (members k).zip gs, x.2.γ.vs = ps ∧
      x.2.γ.rule = srvRule (W64 0) (LogEntry.toEntries boot 0) ∧
      x.2.γ.boot = LogEntry.toEntries boot 0 ∧ γn.N = srvNet x.2.γ ∧
      go!"http://" ++ x.1.Peer' ∈ dirN (members k) ids x.2.id := by
    intro x hx
    obtain ⟨⟨r, hr⟩, -⟩ := hgok x.2 (List.of_mem_zip hx).2
    rw [hr]
    exact ⟨hvs, hrule, hboot, hγn1, hdx x hx⟩
  -- `restartN`'s KV invariant, at the bootstrap state (no key in the range)
  rw [kvModelSt_boot _ (fun _ _ => True) _ _ (srvBootLogOk_of_BootLog _ _ _ Hbf.boot),
    etcdstart.kvModel_boot _ _ _ (srvBootLogOk_of_BootLog _ _ _ Hbf.boot), hlog]
  imod (r3Inv_alloc γk _ (by rw [kvStateOf_kvs (lt := [])]; simp [mvcc.stateAfter, mvcc.applyChanges])
      (by rw [kvStateOf_rev]; rfl) ⊤) $$ Hetcd with ⟨%γc, #Hinv, Hd⟩
  simp only [github_com.mit_pdos.etcd_grove.examples.etcd.restartN.PeerBase,
    github_com.mit_pdos.etcd_grove.examples.etcd.restartN.ClientBase]
  (try wp_auto)
  -- `ms := etcdstart.Members("restartN", k, PeerBase, ClientBase)`
  wp_apply (wp_Members go!"restartN" (W64 k) (W64 14000) (W64 15000) (by word)) as %msl Hmsl
  imod ownSlice_persist _ _ _ $$ Hmsl with #Hmsl
  ihave #Hmsl' : msl ↦*□ members k $$ []
  · iExactEq Hmsl; rw [show uint.nat (W64 (k : Int)) = k by word]
  iclear Hmsl
  (try wp_auto)
  -- `srvs, mems, cluster, err := startMembers(ms, lg)`
  wp_apply (wp_startMembers N msl lg ((members k).zip gs) ps (LogEntry.toEntries boot 0) ctxs
      (dirN (members k) ids) Φs γn HwbN (by simp [LogEntry.toEntries, hblen]; omega) hγn2 Hdok Hbc
      hnd hutf hnlen haf hxok Haf Hbuq Hdbo) $$ [Htok Hpres] as %ssl %msl2 %cl %serr Hsr
  · rw [hxs1]; iframe; iframe #
  icases Hsr with ⟨Htok, (%Hserr | ⟨%Hserr, %zs, %M, Hssl, Hmsl2, #Hcl, #Hsls, %Hdom, Hups⟩)⟩
  · cases serr with
    | nil => exact absurd rfl Hserr
    | ok ei => ?_
    (try wp_auto)
    iapply HΦ; itrivial
  subst Hserr
  (try wp_auto)
  have Hdom' : ∀ n, (M.lookup n).isSome ↔ n ∈ (members k).map (·.Name') := by
    intro n
    rw [Hdom n, ← congrArg (List.map (·.Name')) hxs1, List.map_map]; rfl
  ihave #Hsls' : [∗map] n ↦ sl ∈ M, sl ↦*□ iuOf (members k) n $$ []
  · iExactEq Hsls; rw [hxs1]
  -- members `0` and `k - 1`, out of the started members
  ihave %Hzl := BigSepL2.bigSepL2_length $$ Hups
  have hxk : ((members k).zip gs).length = k := by
    rw [List.length_zip, ← hglen, Nat.min_self, membersOf_length]
  have hzk : zs.length = k := by rw [Hzl, hxk]
  ihave Hups := BigSepL2.bigSepL2_alt.1 $$ Hups
  icases Hups with ⟨-, Hups⟩
  obtain ⟨p0, hp0⟩ : ∃ p, (zs.zip ((members k).zip gs))[0]? = some p :=
    ⟨_, List.getElem?_eq_getElem (by simp [hzk, hxk]; omega)⟩
  obtain ⟨p1, hp1⟩ : ∃ p, (zs.zip ((members k).zip gs))[k - 1]? = some p :=
    ⟨_, List.getElem?_eq_getElem (by simp [hzk, hxk]; omega)⟩
  obtain ⟨hz0, hx0, hm0, hi0⟩ := cand_facts k gs ids hgids zs 0 p0 hp0
  obtain ⟨hz1, hx1, hm1, hi1⟩ := cand_facts k gs ids hgids zs (k - 1) p1 hp1
  icases (BigSepL.bigSepL_delete hp0).1 $$ Hups with ⟨H0, Hrest⟩
  icases (BigSepL.bigSepL_delete hp1).1 $$ Hrest with ⟨H1, Hrest⟩
  ihave H1 := H1 $$ %(by omega : k - 1 ≠ 0)
  -- member `0`'s request view, and the KV invariant at its names
  icases member0_of hRS lg γn p0.1 p0.2 $$ H0 Htok with ⟨Htok, %Ea₀, %γw₀, %HEa₀, #Hreq₀, #Hrvb₀⟩
  have hgok0 := hgok p0.2.2 (List.of_mem_zip (List.mem_of_getElem? hx0)).2
  ihave #Hinv₀ : r3Inv p0.2.2.ρ.rd.kv γc $$ []
  · rw [r3Inv_st p0.2.2.ρ.rd.kv γk hgok0.2.1 γc]; iexact Hinv
  ihave %Hsll := ownSlice_len $$ Hssl
  have Hb0 : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z ssl.len := by
    obtain ⟨h1, h2⟩ := Hsll; simp only [List.length_map, hzk] at h1; constructor <;> word
  -- the `N1` puts of `key(i) ↦ value(i)` through member 0, the counter's half passed along
  ihave HI : (∃ j : w64, "i" ∷ i_ptr ↦ j ∗ "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ 5⌝ ∗
      "Htok" ∷ threadTok ∗ "Hssl" ∷ ssl ↦* zs.map (·.1) ∗
      "Hd" ∷ monoNatAuthOwn γc (1 : Qp).half (sint.nat j) : IProp GF)
      $$ [i Htok Hd Hssl]
  · iexists W64 0; iframe; ipureintro; constructor <;> word
  wp_for HI
  wp_if_destruct
  · have h5 : sint.Z j < 5 := by
      have := Hif; simp only [show sint.Z (W64 5) = 5 by rfl] at this
      first | exact this | exact of_decide_eq_true (go.intoVal_inj this)
    obtain ⟨hj1, hj1a, hj1b⟩ := L1 0 5 j rfl rfl (by omega) Hj.1 h5 (by omega)
    (try wp_auto)
    (try simp only [Hb0, _root_.and_self, ↓reduceIte])
    wp_apply wp_load_slice_index _ (sint.Z (W64 0)) _ _ p0.1.1 Hb0.1 $$ [Hssl] as Hssl
    · iframe Hssl; ipureintro; simp [hz0]
    (try wp_auto)
    wp_apply (wp_put' wp_put p0.1.1 Ea₀ { p0.2.2.ρ with wait := γw₀ } γc j Hj.1
        (by simp only [r3NPuts]; omega)
        HEa₀ HLv) $$ [Htok Hd] as %perr ⟨Htok, Hput⟩
    · iframe; iframe #
    icases Hput with (⟨%Hperr, Hd⟩ | %Hperr)
    rotate_left
    · cases perr with
      | nil => exact absurd rfl Hperr
      | ok ei => ?_
      wp_auto
      wp_for_post
      iapply HΦ; itrivial
    subst Hperr
    wp_auto
    wp_for_post
    iframe
    iexists j + W64 1
    iframe
    rw [hj1]
    iframe
    ipureintro; exact ⟨hj1a, hj1b⟩
  have hj5 : sint.nat j = 5 := by
    have h5 : ¬ sint.Z j < 5 := by
      have := Hif; simp only [show sint.Z (W64 5) = 5 by rfl] at this
      first | exact this | exact fun h => this (by rw [decide_eq_true h])
    exact L3 5 j rfl Hj.1 h5 Hj.2
  rw [hj5]
  -- candidate `k - 1`: its stop bundle, its leader and member-id fields
  have hxm1 : p1.2.1 ∈ members k := List.mem_of_getElem? hm1
  have hgok1 := hgok p1.2.2 (List.of_mem_zip (List.mem_of_getElem? hx1)).2
  ihave #Hrf1 := (BigSepL.bigSepL_lookup (Φ := fun _ (x : GMember × MemberG GF) =>
    iprop(memberRestartFacts x.2.γ x.2.ρ x.2.id ∗ ⌜x.2.E.cmp = false⌝)) hx1) $$ Hrfs
  ihave #HbR1 := bootR_at k N ids ps ctxs boot (k - 1) p1.2.1 p1.2.2.id (by unfold nStop; omega)
    hm1 hi1 $$ HbRs
  ihave #Hnet1 : netHttpOk γn p1.2.2.id $$ []
  · iapply Hnet
  icases stopCand_of hRS N lg γn γ γk (members k) ids ps ctxs boot p1.1 p1.2 hgok1
      (hdx _ (List.mem_of_getElem? hx1)) hxm1 $$ H1 Htok Hrf1 Hnet1 HbR1
    with ⟨Htok, #Hlead1, ⟨%mid1, #Hmid1⟩, Hc1⟩
  (try wp_auto)
  have hk1z : sint.Z (W64 (k : Int) - W64 1) = (k - 1 : Nat) := by word
  have hk1n : (sint.Z (W64 (k : Int) - W64 1)).toNat = k - 1 := by rw [hk1z]; simp
  -- the `if`, proved with the stopped member as its postcondition
  wp_bind (If _ _ _)
  iapply (wp_wand (Φ := fun v => iprop(⌜v = executeVal⌝ ∗ threadTok ∗ ssl ↦* zs.map (·.1) ∗
      srvs_ptr ↦ ssl ∗ k_ptr ↦ W64 (k : Int) ∗
      ∃ (jn : Nat) (z : Loc × Loc), j_ptr ↦ W64 (jn : Int) ∗ ⌜jn < k ∧ zs[jn]? = some z⌝ ∗
        stopCand N z.2 z.1 γn γ γk (members k) ids ps ctxs boot))) $$ [j k srvs Htok Hssl Hc1 Hrest]
  · have hjv : W64 (k : Int) - W64 1 = W64 ((k - 1 : Nat) : Int) := by word
    wp_if_destruct
    · have hk3 : 2 < k := by
        have := Hif; rw [hkz] at this; simp only [show uint.Z (W64 2) = 2 from rfl] at this; omega
      ihave %Hsll2 := ownSlice_len $$ Hssl
      have Hb1 : 0 ≤ sint.Z (W64 (k : Int) - W64 1) ∧ sint.Z (W64 (k : Int) - W64 1) < sint.Z ssl.len := by
        obtain ⟨h1, h2⟩ := Hsll2; simp only [List.length_map, hzk] at h1; rw [hk1z]; constructor <;> word
      have hl1 : (zs.map (·.1))[(sint.Z (W64 (k : Int) - W64 1)).toNat]? = some p1.1.1 := by
        rw [hk1n]; simp [hz1]
      (try wp_auto)
      (try simp only [Hb1, _root_.and_self, ↓reduceIte])
      wp_apply wp_load_slice_index _ (sint.Z (W64 (k : Int) - W64 1)) _ _ p1.1.1 Hb1.1 $$ [Hssl] as Hssl
      · iframe Hssl; ipureintro; exact hl1
      (try wp_auto)
      wp_apply (wp_Leader p1.1.1) as %l -
      · iframe #
      (try wp_auto)
      (try simp only [Hb1, _root_.and_self, ↓reduceIte])
      wp_apply wp_load_slice_index _ (sint.Z (W64 (k : Int) - W64 1)) _ _ p1.1.1 Hb1.1 $$ [Hssl] as Hssl
      · iframe Hssl; ipureintro; exact hl1
      (try wp_auto)
      wp_apply (wp_MemberID p1.1.1 mid1)
      · iframe #
      (try wp_auto)
      wp_if_destruct
      · -- member `k - 1` leads: member `k - 2` is stopped
        obtain ⟨p2, hp2⟩ : ∃ p, (zs.zip ((members k).zip gs))[k - 2]? = some p :=
          ⟨_, List.getElem?_eq_getElem (by simp [hzk, hxk]; omega)⟩
        obtain ⟨hz2, hx2, hm2, hi2⟩ := cand_facts k gs ids hgids zs (k - 2) p2 hp2
        have hxm2 : p2.2.1 ∈ members k := List.mem_of_getElem? hm2
        have hgok2 := hgok p2.2.2 (List.of_mem_zip (List.mem_of_getElem? hx2)).2
        ihave H2 := (BigSepL.bigSepL_lookup hp2) $$ Hrest
        ihave H2 := H2 $$ %(by omega : k - 2 ≠ k - 1)
        ihave H2 := H2 $$ %(by omega : k - 2 ≠ 0)
        ihave #Hrf2 := (BigSepL.bigSepL_lookup (Φ := fun _ (x : GMember × MemberG GF) =>
          iprop(memberRestartFacts x.2.γ x.2.ρ x.2.id ∗ ⌜x.2.E.cmp = false⌝)) hx2) $$ Hrfs
        ihave #HbR2 := bootR_at k N ids ps ctxs boot (k - 2) p2.2.1 p2.2.2.id (by unfold nStop; omega)
          hm2 hi2 $$ HbRs
        ihave #Hnet2 : netHttpOk γn p2.2.2.id $$ []
        · iapply Hnet
        icases stopCand_of hRS N lg γn γ γk (members k) ids ps ctxs boot p2.1 p2.2 hgok2
            (hdx _ (List.mem_of_getElem? hx2)) hxm2 $$ H2 Htok Hrf2 Hnet2 HbR2
          with ⟨Htok, -, -, Hc2⟩
        isplitr
        · itrivial
        iframe Htok Hssl srvs k
        iexists k - 2, p2.1
        have hjv2 : W64 (k : Int) - W64 2 = W64 ((k - 2 : Nat) : Int) := by word
        rw [hjv2]
        iframe
        ipureintro; exact ⟨by omega, hz2⟩
      · -- member `k - 1` is stopped
        isplitr
        · itrivial
        iframe Htok Hssl srvs k
        iexists k - 1, p1.1
        rw [hjv]
        iframe
        ipureintro; exact ⟨by omega, hz1⟩
    · -- `k = 2`: member `k - 1` is stopped
      isplitr
      · itrivial
      iframe Htok Hssl srvs k
      iexists k - 1, p1.1
      rw [hjv]
      iframe
      ipureintro; exact ⟨by omega, hz1⟩
  iintro %v ⟨%Hv, Htok, Hssl, srvs, k, %jn, %z, j, %Hjz, Hc⟩
  subst Hv
  (try wp_auto)
  iunfold stopCand at Hc
  icases Hc with ⟨%x, %id, %reg, %ρ, %E, %dd, %γS, ⟨%hd, %hxm, %hst, %hsc⟩, Hrec, #Hai, #Hdd, Hsr, Hrds,
    #Hnetx, #HbR, #Hrfx⟩
  -- `stop(srvs[j], k)`
  ihave %Hρr : ⌜ρ.rd.raft.raft = { γ with reg := reg }⌝ $$ []
  · ihave #Hf := Hrfx
    iunfold etcdstart.memberRestartFacts at Hf
    icases Hf with ⟨%Hρ, -⟩
    ipureintro; rw [Hρ.1]
  have Hbk : ρ.rd.raft.raft.boot.length ≤ uint.nat (W64 (k : Int)) := by
    rw [Hρr]; show γ.boot.length ≤ _; rw [hboot]; simp only [LogEntry.toEntries, List.length_map,
      List.length_zipIdx, List.length_mapIdx, hblen]; word
  have hjz : sint.Z (W64 (jn : Int)) = jn := by word
  ihave %Hsll3 := ownSlice_len $$ Hssl
  have Hbj : 0 ≤ sint.Z (W64 (jn : Int)) ∧ sint.Z (W64 (jn : Int)) < sint.Z ssl.len := by
    obtain ⟨h1, h2⟩ := Hsll3; simp only [List.length_map, hzk] at h1; rw [hjz]; constructor <;> word
  (try simp only [Hbj, _root_.and_self, ↓reduceIte])
  wp_apply wp_load_slice_index _ (sint.Z (W64 (jn : Int))) _ _ z.1 Hbj.1 $$ [Hssl] as Hssl
  · iframe Hssl; ipureintro; rw [hjz]; simp [Hjz.2]
  (try wp_auto)
  wp_apply (wp_stop z.1 E E ρ id dd γn x.Name' (W64 (k : Int)) Hbk hsc) $$ [Hsr Hrds] as Hrr
  · iframe; iframe #
  rw [Hρr]
  (try wp_auto)
  -- the `N2` puts, the counter's half passed along
  ihave HI : (∃ j : w64, "i" ∷ i_ptr ↦ j ∗ "%Hj" ∷ ⌜5 ≤ sint.Z j ∧ sint.Z j ≤ 25⌝ ∗
      "Htok" ∷ threadTok ∗ "Hssl" ∷ ssl ↦* zs.map (·.1) ∗
      "Hd" ∷ monoNatAuthOwn γc (1 : Qp).half (sint.nat j) : IProp GF)
      $$ [i Htok Hd Hssl]
  · iexists W64 5; iframe; ipureintro; constructor <;> word
  wp_for HI
  wp_if_destruct
  · have h25 : sint.Z j < 25 := by
      have := Hif; simp only [show sint.Z (W64 25) = 25 by rfl] at this
      first | exact this | exact of_decide_eq_true (go.intoVal_inj this)
    obtain ⟨hj1, hj1a, hj1b⟩ := L1 5 25 j rfl rfl (by omega) Hj.1 h25 (by omega)
    (try wp_auto)
    (try simp only [Hb0, _root_.and_self, ↓reduceIte])
    wp_apply wp_load_slice_index _ (sint.Z (W64 0)) _ _ p0.1.1 Hb0.1 $$ [Hssl] as Hssl
    · iframe Hssl; ipureintro; simp [hz0]
    (try wp_auto)
    wp_apply (wp_put' wp_put p0.1.1 Ea₀ { p0.2.2.ρ with wait := γw₀ } γc j (by omega)
        (by simp only [r3NPuts]; omega) HEa₀ HLv) $$ [Htok Hd] as %perr ⟨Htok, Hput⟩
    · iframe; iframe #
    icases Hput with (⟨%Hperr, Hd⟩ | %Hperr)
    rotate_left
    · cases perr with
      | nil => exact absurd rfl Hperr
      | ok ei => ?_
      wp_auto
      wp_for_post
      iapply HΦ; itrivial
    subst Hperr
    wp_auto
    wp_for_post
    iframe
    iexists j + W64 1
    iframe
    rw [hj1]
    iframe
    ipureintro; exact ⟨hj1a, hj1b⟩
  have hj25 : sint.nat j = r3NPuts := by
    have h25 : ¬ sint.Z j < 25 := by
      have := Hif; simp only [show sint.Z (W64 25) = 25 by rfl] at this
      first | exact this | exact fun h => this (by rw [decide_eq_true h])
    simp only [r3NPuts]; exact L3 25 j rfl (by omega) h25 Hj.2
  rw [hj25]
  ihave #Hlb := monoNatLbOwn_get γc _ r3NPuts $$ Hd
  -- `sR, err := restartMember(mems[j], cluster, lg)`
  ihave %Hmll3 := ownSlice_len $$ Hmsl2
  have Hbj2 : 0 ≤ sint.Z (W64 (jn : Int)) ∧ sint.Z (W64 (jn : Int)) < sint.Z msl2.len := by
    obtain ⟨h1, h2⟩ := Hmll3; simp only [List.length_map, hzk] at h1; rw [hjz]; constructor <;> word
  (try simp only [Hbj2, _root_.and_self, ↓reduceIte])
  wp_apply wp_load_slice_index _ (sint.Z (W64 (jn : Int))) _ _ z.2 Hbj2.1 $$ [Hmsl2] as Hmsl2
  · iframe Hmsl2; ipureintro; rw [hjz]; simp [Hjz.2]
  (try wp_auto)
  wp_apply (wp_restartMember N z.2 γS x.Name' x.Peer' x.Client' cl lg M (iuOf (members k))
      (urlsN (members k) x) ps (LogEntry.toEntries boot 0) ctxs (dirN (members k) ids) id
      { γ with reg := reg } ρ γn HwbN hvs hrule hboot (by simp [LogEntry.toEntries, hblen]; omega)
      hγn1 hγn2 Hdok hd Hbc ⟨rfl, rfl, Hdom', rfl⟩
      (etcdstart.membersOf_addrFits _ _ _ _ x hxm).1 (etcdstart.membersOf_addrFits _ _ _ _ x hxm).2
      Haf Hbuq Hdbo) $$ [Htok Hrec Hrr] as %sR %err Hr
  · iframe; iframe #
  icases Hr with (⟨%Herr, -⟩ | ⟨%Herr, %ρ', %E₀', %Hρ', HupR⟩)
  · cases err with
    | nil => exact absurd rfl Herr
    | ok ei => ?_
    wp_auto
    iapply HΦ; itrivial
  subst Herr
  wp_auto
  -- `check(sR)`, under the invariant at the restarted names
  ihave #HinvR : r3Inv ρ'.rd.kv γc $$ []
  · rw [r3Inv_st ρ'.rd.kv γk (by rw [restartNames_st Hρ', hst]) γc]
    iexact Hinv
  wp_apply (wp_check sR ρ' E₀' lg γn id γc HLv) $$ [HupR] as %b -
  · iframe; iframe #
  iapply HΦ; itrivial

end proof

end etcd_restartN
end EtcdGrove
end Perennial
