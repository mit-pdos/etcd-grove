/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/etcd/restart/Run.lean` (restart3 C2,
2026-11-15). Lean-first (no Rocq counterpart). putget3's three-member start (the peer URLs, the
cluster's map, `etcdstart.alloc3`), each member built (`build.spec`) and started with its peer handler
(`newMember.spec`), restart1's KV invariant at 25 puts (`r3Inv_alloc`, at member 1's KV names, which
the three members share), the `N1` puts through member 1 (`put.spec`, the counter's half passed along);
the stopped member chosen by `s3.Leader() == s3.MemberID()` (the `if` proved with a postcondition naming
the chosen member, `stopCand`, so that the rest is proved once); its stop (`stop.spec`, out of
`memberUp_splitStop`), the `N2` puts, its restart (`restartMember.spec`, with the cluster's persistent
facts kept from its boot bundle) and the check (`check.spec`, under the invariant at the restarted
names, `r3Inv_st`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.restart.Run
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.restart.build
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.restart.newMember
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.restart.put
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.restart.stop
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.restart.check
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__Leader
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__MemberID
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Alloc3
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.restart1.Defs


@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_restart

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.restart.Assumptions]

/-- A host of the directory is one of the three peer addresses (putget3's `dir3_host`). -/
theorem dir3_host (id₁ id₂ id₃ id : w64) (h : GoString)
    (hm : go!"http://" ++ h ∈ dir3 id₁ id₂ id₃ id) : h = peerAddr₁ ∨ h = peerAddr₂ ∨ h = peerAddr₃ := by
  unfold dir3 at hm
  split at hm
  · left; simpa using hm
  split at hm
  · right; left; simpa using hm
  split at hm
  · right; right; simpa using hm
  · simp at hm

/-- **`Run`'s directory names the peers** (`rafthttp.bootCfg`, `NewServer`'s premise; 2026-11-03, the final
whole-`bootOk` review's M2): its members are the ids, which the peers permute. -/
theorem dir3_dirsOk (id₁ id₂ id₃ : w64) (ps : List w64) (ctxs : List (List w8)) (bl : List LogEntry)
    (Hbf : BootFacts id₁ id₂ id₃ ps ctxs bl) : rafthttp.bootCfg (dir3 id₁ id₂ id₃) ps := by
  refine rafthttp.bootCfg_of _ ps (fun f => ?_) (by rw [Hbf.perm.length_eq]; simp)
  rw [Hbf.perm.mem_iff]
  unfold dir3
  constructor
  · intro h
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    by_cases h1 : f = id₁
    · exact Or.inl h1
    by_cases h2 : f = id₂
    · exact Or.inr (Or.inl h2)
    by_cases h3 : f = id₃
    · exact Or.inr (Or.inr h3)
    rw [if_neg h1, if_neg h2, if_neg h3] at h
    exact absurd rfl h
  · intro hm
    split
    · simp
    split
    · simp
    split
    · simp
    · simp_all

/-- **`Run`'s directory is well formed** (putget3's `dir3_ok`). -/
theorem dir3_ok (id₁ id₂ id₃ : w64) (ps : List w64) (ctxs : List (List w8)) (bl : List LogEntry)
    (Hbf : BootFacts id₁ id₂ id₃ ps ctxs bl) :
    netDirOk (dir3 id₁ id₂ id₃) := by
  obtain ⟨hn12, hn13, hn23⟩ := etcdstart.id_ne id₁ id₂ id₃ Hbf.idLow Hbf.idLow0
  have Hnz := etcdstart.id_nz id₁ id₂ id₃ Hbf.idLow Hbf.idLow0
  have h1 := Hnz id₁ (by simp); have h2 := Hnz id₂ (by simp); have h3 := Hnz id₃ (by simp)
  refine ⟨?_, ?_, ?_⟩
  · unfold dir3
    rw [if_neg (fun e => h1 (by rw [← e]; rfl)), if_neg (fun e => h2 (by rw [← e]; rfl)),
      if_neg (fun e => h3 (by rw [← e]; rfl))]
  · intro i j h hi hj
    unfold dir3 at hi hj
    split at hi <;> split at hj <;> (try split at hi) <;> (try split at hj) <;>
      (try split at hi) <;> (try split at hj) <;> simp_all <;> (try decide)
  · intro i s hs
    unfold dir3 at hs
    split at hs
    · simp at hs; subst hs; decide
    split at hs
    · simp at hs; subst hs; decide
    split at hs
    · simp at hs; subst hs; decide
    · simp at hs

/-- **A started server's leader and member-id fields** (what `Leader` and `MemberID` read), from
its request view. -/
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


/-- `put(s, j)` at a `w64` argument. -/
theorem wp_put' (wp_put : put.spec (GF := GF) (hG := hG)) (s : Loc) (E : apply.AEnv GF)
    (ρ : ReqNames) (γc : GName) (j : w64) (h0 : 0 ≤ sint.Z j) (hj : sint.Z j < r3NPuts)
    [ReceiptBoundLe GF (2 ^ 48)] (hE : E.authOn = false) (hlv : srvLevels (GF := GF)) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.restart ∗
        isServerReq s E ρ ∗ srvRevokeBuilt s E ∗ threadTok ∗
        r3Inv ρ.kv γc ∗ monoNatAuthOwn γc (1 : Qp).half (sint.nat j) }}
      (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.restart.put))
        (Val #s)) (Val #j))
    {{ (err : GoInterface), RET #err; threadTok ∗
        ((⌜err = GoInterface.nil⌝ ∗ monoNatAuthOwn γc (1 : Qp).half (sint.nat j + 1)) ∨
          ⌜err ≠ GoInterface.nil⌝) }} := by
  have hw := wp_put s E ρ γc (sint.nat j) (by unfold sint.nat; unfold sint.Z at h0 hj; omega)
    hE hlv
  rwa [show W64 ((sint.nat j : Nat) : Int) = j by unfold sint.nat; word] at hw

/-- **The member a run stops** (the `if`'s postcondition): its record, the right to stop it and what
the stop takes, and what its restart takes (the restart contract, the cluster's persistent facts at its
names), at its name, addresses and id; its KV names the cluster's. -/
def stopCand (N : Nat) (m s : Loc) (γn : NetNames GF) (γ : SrvRaft) (ρ₁ : ReqNames)
    (id₁ id₂ id₃ : w64) (ps : List w64) (ctxs : List (List w8)) (boot : List LogEntry)
    (M : GMap GoString GoSlice) : IProp GF :=
  iprop(∃ (name peerAddr client : GoString) (id : w64) (reg : GName) (ρ : ReqNames)
      (E : apply.AEnv GF) (dd : GoString) (γS : SwNames),
    ⌜go!"http://" ++ peerAddr ∈ dir3 id₁ id₂ id₃ id ∧
      urlsOk peerAddr client ⟨[etcdstart.httpURL peerAddr], [etcdstart.httpURL client], M, initURLs3⟩ ∧
      etcdstart.addrFits peerAddr ∧ etcdstart.addrFits client ∧
      ρ.rd.kv.st = ρ₁.rd.kv.st ∧ srvStop.scope E⌝ ∗
    memberRec m γS γn name peerAddr client ∗ srvAppliedInv s E ρ.rd ∗
    srvDataDir s (memberDataDir name) ∗ srvStopRight s E ρ.rd.raft.raft ρ id dd ∗ srvStopReaders E ∗
    netHttpOk γn id ∗
    etcdstart.bootPremiseR N ps (LogEntry.toEntries boot 0) ctxs (dir3 id₁ id₂ id₃) token name
      (urlsOk peerAddr client) id ∗
    etcdstart.memberRestartFacts { γ with reg := reg } ρ id)

set_option maxHeartbeats 4000000 in
theorem Run.wp_proof
    (wp_build : build.spec (GF := GF) (hG := hG))
    (wp_newMember : newMember.spec (GF := GF) (hG := hG))
    (wp_put : put.spec (GF := GF) (hG := hG))
    (wp_Leader : EtcdServer.Leader.spec (GF := GF) (hG := hG))
    (wp_MemberID : EtcdServer.MemberID.spec (GF := GF) (hG := hG))
    (wp_stop : stop.spec (GF := GF) (hG := hG))
    (wp_restartMember : restartMember.spec (GF := GF) (hG := hG))
    (wp_check : check.spec (GF := GF) (hG := hG))
    (hne : mvcc.api.names_nonempty.law) (hRS : mvcc.api.mvccReaders_split.law (GF := GF))
    -- (premises to axioms, 2026-11-24: until then the premise `bootMarshal`) `proto.Marshal`'s spec at a boot conf change
    (wp_MarshalBoot : proto.MarshalBootConfChange.spec (GF := GF) (hG := hG)) :
    Run.spec (GF := GF) (hG := hG) := by
  intro CS lg N id₁ id₂ id₃ ps ctxs boot ThB RcB RcN Hbf HLv HwbN Haf Hbuq Hdbo
  have Hrb48 := ReceiptBoundLe.le (GF := GF) (2 ^ 48)
  wp_start as ⟨#Hzlg, Hs₁, Hs₂, Hs₃, Htok, #Hprem⟩
  ihave %Hlg := zapLoggerOk_ne_null lg $$ Hzlg
  iunfold premises at Hprem
  icases Hprem with ⟨#Hb₁, #Hb₂, #Hb₃, #HbR₂, #HbR₃⟩
  -- (premises to axioms, 2026-11-24: until then the premise `bootMarshal`) `proto.Marshal`'s bytes at the
  -- bootstrap log's conf changes, from its trust-boundary spec and the log's bytes (`Hbf.wire`)
  ihave #Hpp : isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.protobuf.proto $$ []
  · iPkgInit
  ihave #Hmarsh := bootMarshal_of_spec wp_MarshalBoot _ _ _ Hbf.wire $$ Hpp
  ihave #Hcci : context.isClosedchanInit (GF := GF) $$ []
  · iapply context.isClosedchanInit_of_init
    iPkgInit
  ihave #Psrv : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver $$ []
  · iPkgInit
  (try wp_auto)
  simp only [github_com.mit_pdos.etcd_grove.examples.etcd.restart.peerAddr1,
    github_com.mit_pdos.etcd_grove.examples.etcd.restart.peerAddr2,
    github_com.mit_pdos.etcd_grove.examples.etcd.restart.peerAddr3,
    github_com.mit_pdos.etcd_grove.examples.etcd.restart.clientAddr1,
    github_com.mit_pdos.etcd_grove.examples.etcd.restart.clientAddr2,
    github_com.mit_pdos.etcd_grove.examples.etcd.restart.clientAddr3]
  -- the peer URLs and the initial cluster's map, read-only from here on
  wp_apply wp_slice_literal
  try (isplitr; (ipureintro; rfl))
  iintro %peer₁ ⟨Hpeer₁, -⟩
  simp only [go.arrayLiteralSize, List.foldl]
  (try wp_auto)
  wp_apply wp_slice_literal
  try (isplitr; (ipureintro; rfl))
  iintro %peer₂ ⟨Hpeer₂, -⟩
  simp only [go.arrayLiteralSize, List.foldl]
  (try wp_auto)
  wp_apply wp_slice_literal
  try (isplitr; (ipureintro; rfl))
  iintro %peer₃ ⟨Hpeer₃, -⟩
  simp only [go.arrayLiteralSize, List.foldl]
  (try wp_auto)
  wp_apply wp_map_make1 (K := GoString) (V := go_etcd_io.etcd.client.pkg.v3.types.URLs)
    as %pm Hpm
  wp_apply wp_mapInsert $$ Hpm as Hpm
  wp_apply wp_mapInsert $$ Hpm as Hpm
  wp_apply wp_mapInsert $$ Hpm as Hpm
  (try wp_auto)
  imod ownSlice_persist _ _ _ $$ Hpeer₁ with #Hpeer₁
  imod ownSlice_persist _ _ _ $$ Hpeer₂ with #Hpeer₂
  imod ownSlice_persist _ _ _ $$ Hpeer₃ with #Hpeer₃
  imod ownMap_persist _ _ _ $$ Hpm with #Hpm
  have hsl : ∀ p : Loc, slice.mk p (W64 (max (max (0 + 1) 0) 0)) (W64 (max (max (0 + 1) 0) 0)) =
      slice.mk p (W64 1) (W64 1) := fun _ => rfl
  simp only [hsl] at *
  ihave #Hq₁ : (slice.mk peer₁ (W64 1) (W64 1)) ↦*□ [etcdstart.httpURL peerAddr₁] $$ []
  · iExactEq Hpeer₁; rfl
  ihave #Hq₂ : (slice.mk peer₂ (W64 1) (W64 1)) ↦*□ [etcdstart.httpURL peerAddr₂] $$ []
  · iExactEq Hpeer₂; rfl
  ihave #Hq₃ : (slice.mk peer₃ (W64 1) (W64 1)) ↦*□ [etcdstart.httpURL peerAddr₃] $$ []
  · iExactEq Hpeer₃; rfl
  ihave #Hu₁ : (slice.mk peer₁ (W64 1) (W64 1)) ↦*□ initURLs3 name₁ $$ []
  · iExactEq Hpeer₁; simp [initURLs3]; rfl
  ihave #Hu₂ : (slice.mk peer₂ (W64 1) (W64 1)) ↦*□ initURLs3 name₂ $$ []
  · iExactEq Hpeer₂; simp [initURLs3]; rfl
  ihave #Hu₃ : (slice.mk peer₃ (W64 1) (W64 1)) ↦*□ initURLs3 name₃ $$ []
  · iExactEq Hpeer₃; simp [initURLs3]; rfl
  ihave #Hcm : pm ↦$□ GMap.insert name₃ (slice.mk peer₃ (W64 1) (W64 1))
      (GMap.insert name₂ (slice.mk peer₂ (W64 1) (W64 1))
        (GMap.insert name₁ (slice.mk peer₁ (W64 1) (W64 1)) ∅)) $$ []
  · iExactEq Hpm; rfl
  ihave #Hsls : [∗map] k ↦ sl ∈ GMap.insert name₃ (slice.mk peer₃ (W64 1) (W64 1))
      (GMap.insert name₂ (slice.mk peer₂ (W64 1) (W64 1))
        (GMap.insert name₁ (slice.mk peer₁ (W64 1) (W64 1)) ∅)), sl ↦*□ initURLs3 k $$ []
  · iapply (BigSepM.bigSepM_insert (by
      rw [gmap_get?_eq, GMap.lookup_insert_ne _ _ (by decide : name₂ ≠ name₃),
        GMap.lookup_insert_ne _ _ (by decide : name₁ ≠ name₃)]; rfl)).2
    isplitr; · iexact Hu₃
    iapply (BigSepM.bigSepM_insert (by
      rw [gmap_get?_eq, GMap.lookup_insert_ne _ _ (by decide : name₁ ≠ name₂)]; rfl)).2
    isplitr; · iexact Hu₂
    iapply (BigSepM.bigSepM_insert (GMap.lookup_empty _)).2
    isplitr; · iexact Hu₁
    iapply BigSepM.bigSepM_empty.2; itrivial
  generalize hM : GMap.insert name₃ (slice.mk peer₃ (W64 1) (W64 1))
      (GMap.insert name₂ (slice.mk peer₂ (W64 1) (W64 1))
        (GMap.insert name₁ (slice.mk peer₁ (W64 1) (W64 1)) ∅)) = M at *
  have hU8 : ∀ k, (M.lookup k).isSome → utf8Valid k := by
    rw [← hM]
    exact etcdstart.utf8Keys_insert _ _ _ (by decide) (etcdstart.utf8Keys_insert _ _ _ (by decide)
      (etcdstart.utf8Keys_insert _ _ _ (by decide) etcdstart.utf8Keys_empty))
  have hUok : ∀ (pa cl : GoString),
      urlsOk pa cl ⟨[etcdstart.httpURL pa], [etcdstart.httpURL cl], M, initURLs3⟩ := by
    intro pa cl; rw [← hM]; exact ⟨rfl, rfl, ⟨_, _, _, rfl⟩, rfl⟩
  -- the ghost state of the cluster and its members (`alloc3`)
  have hblen0 : boot.length = 3 := by rw [Hbf.boot.1, Hbf.perm.length_eq]; rfl
  imod (etcdstart.alloc3 hne id₁ id₂ id₃ ps Hbf.perm ctxs boot Hbf.toBootCore
      (dir3 id₁ id₂ id₃) peerAddr₁ peerAddr₂ peerAddr₃ (dir3_ok id₁ id₂ id₃ ps ctxs boot Hbf).1
      (dir3_host id₁ id₂ id₃) (by omega) (by omega) name₁ name₂ name₃ none none none
      .none lease.runCfg_none (fun h => nomatch h))
      $$ Hmarsh Hs₁ Hs₂ Hs₃
    with ⟨%γ, %reg₁, %reg₂, %reg₃, %ρ₁, %ρ₂, %ρ₃, %E₁, %E₂, %E₃, %Φs, %γn, %Hal,
    Hmb₁, ⟨#Hnet₁, Hfr₁⟩, Hmb₂, ⟨#Hnet₂, Hfr₂⟩, Hmb₃, ⟨#Hnet₃, Hfr₃⟩, Hetcd⟩
  isimp only [ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte] at Hetcd
  -- the peer addresses' listen rights and raft protocols, to `newMember`
  icases etcdstart.memberFreshRes_peer _ _ _ _ rfl $$ Hfr₁ with ⟨⟨Ha₁, Ho₁⟩, Hfr₁⟩
  icases etcdstart.memberFreshRes_peer _ _ _ _ rfl $$ Hfr₂ with ⟨⟨Ha₂, Ho₂⟩, Hfr₂⟩
  icases etcdstart.memberFreshRes_peer _ _ _ _ rfl $$ Hfr₃ with ⟨⟨Ha₃, Ho₃⟩, Hfr₃⟩
  obtain ⟨hvs, hrule, hboot, hγn1, hγn2, hlog₁, hst₂, hst₃, -⟩ := Hal
  -- members 2 and 3: out of compaction mode (their stops' scope), the cluster's persistent facts at
  -- their names (their restarts'), `ETCD_VERIFY` off (kept from member 2's fresh bundle)
  icases etcdstart.memberBoot_cmp _ _ _ _ _ _ false $$ Hmb₂ with ⟨%hc₂, Hmb₂⟩
  icases etcdstart.memberBoot_cmp _ _ _ _ _ _ false $$ Hmb₃ with ⟨%hc₃, Hmb₃⟩
  icases etcdstart.memberBoot_restartFacts _ _ _ _ _ _ $$ Hmb₂ with ⟨#Hrfs₂, Hmb₂⟩
  icases etcdstart.memberBoot_restartFacts _ _ _ _ _ _ $$ Hmb₃ with ⟨#Hrfs₃, Hmb₃⟩
  icases etcdstart.memberFreshRes_verify _ _ _ $$ Hfr₂ with ⟨#Hvoff, Hfr₂⟩
  obtain ⟨hn12, hn13, hn23⟩ := etcdstart.id_ne id₁ id₂ id₃ Hbf.idLow Hbf.idLow0
  have hd₁ : go!"http://" ++ peerAddr₁ ∈ dir3 id₁ id₂ id₃ id₁ := by simp [dir3]
  have hd₂ : go!"http://" ++ peerAddr₂ ∈ dir3 id₁ id₂ id₃ id₂ := by simp [dir3, hn12.symm]
  have hd₃ : go!"http://" ++ peerAddr₃ ∈ dir3 id₁ id₂ id₃ id₃ := by
    simp [dir3, hn13.symm, hn23.symm]
  have hown : ∀ (pa : GoString) (i : w64), go!"http://" ++ pa ∈ dir3 id₁ id₂ id₃ i →
      (netRh γn).owner pa = i := by
    intro pa i h
    rw [netRh_owner]
    exact netOwner_of_mem γn.dir (by rw [hγn2]; exact (dir3_ok id₁ id₂ id₃ ps ctxs boot Hbf).2.1)
      i pa (by rw [hγn2]; exact h)
  have hblen : (LogEntry.toEntries boot 0).length ≤ 2 ^ 60 := by
    simp [LogEntry.toEntries, hblen0]
  have hb3 : (LogEntry.toEntries boot 0).length ≤ 3 := by
    simp [LogEntry.toEntries, hblen0]
  -- `restart3`'s KV invariant, at the bootstrap state (no key in the range)
  rw [kvModelSt_boot _ (fun _ _ => True) _ _ (srvBootLogOk_of_BootLog _ _ _ Hbf.boot),
    etcdstart.kvModel_boot _ _ _ (srvBootLogOk_of_BootLog _ _ _ Hbf.boot), hlog₁]
  imod (r3Inv_alloc ρ₁.rd.kv _ (by rw [kvStateOf_kvs (lt := [])]; simp [mvcc.stateAfter, mvcc.applyChanges])
      (by rw [kvStateOf_rev]; rfl) ⊤) $$ Hetcd with ⟨%γc, #Hinv, Hd⟩
  wp_apply (wp_build N name₁ peerAddr₁ clientAddr₁ (slice.mk peer₁ (W64 1) (W64 1)) pm lg M initURLs3
      (urlsOk peerAddr₁ clientAddr₁) ps (LogEntry.toEntries boot 0) ctxs (dir3 id₁ id₂ id₃) id₁
      { γ with reg := reg₁ } ρ₁ E₁ Φs γn HwbN hvs hrule hboot hblen hγn1 hγn2
      (dir3_ok id₁ id₂ id₃ ps ctxs boot Hbf) hd₁ (dir3_dirsOk id₁ id₂ id₃ ps ctxs boot Hbf)
      (hUok _ _) (by decide) (by decide) hU8 (by decide) Haf Hbuq Hdbo) $$ [Htok Hmb₁ Hfr₁] as %s₁ %err Hr
  · iframe; iframe #
  icases Hr with (⟨%Herr, -⟩ | ⟨%Herr, Htok, Hmb₁, #Hdd₁⟩)
  · cases err with
    | nil => exact absurd rfl Herr
    | ok ei => ?_
    wp_auto
    iapply HΦ; itrivial
  subst Herr
  wp_auto
  wp_apply (wp_build N name₂ peerAddr₂ clientAddr₂ (slice.mk peer₂ (W64 1) (W64 1)) pm lg M initURLs3
      (urlsOk peerAddr₂ clientAddr₂) ps (LogEntry.toEntries boot 0) ctxs (dir3 id₁ id₂ id₃) id₂
      { γ with reg := reg₂ } ρ₂ E₂ Φs γn HwbN hvs hrule hboot hblen hγn1 hγn2
      (dir3_ok id₁ id₂ id₃ ps ctxs boot Hbf) hd₂ (dir3_dirsOk id₁ id₂ id₃ ps ctxs boot Hbf)
      (hUok _ _) (by decide) (by decide) hU8 (by decide) Haf Hbuq Hdbo) $$ [Htok Hmb₂ Hfr₂] as %s₂ %err Hr
  · iframe; iframe #
  icases Hr with (⟨%Herr, -⟩ | ⟨%Herr, Htok, Hmb₂, #Hdd₂⟩)
  · cases err with
    | nil => exact absurd rfl Herr
    | ok ei => ?_
    wp_auto
    iapply HΦ; itrivial
  subst Herr
  wp_auto
  wp_apply (wp_build N name₃ peerAddr₃ clientAddr₃ (slice.mk peer₃ (W64 1) (W64 1)) pm lg M initURLs3
      (urlsOk peerAddr₃ clientAddr₃) ps (LogEntry.toEntries boot 0) ctxs (dir3 id₁ id₂ id₃) id₃
      { γ with reg := reg₃ } ρ₃ E₃ Φs γn HwbN hvs hrule hboot hblen hγn1 hγn2
      (dir3_ok id₁ id₂ id₃ ps ctxs boot Hbf) hd₃ (dir3_dirsOk id₁ id₂ id₃ ps ctxs boot Hbf)
      (hUok _ _) (by decide) (by decide) hU8 (by decide) Haf Hbuq Hdbo) $$ [Htok Hmb₃ Hfr₃] as %s₃ %err Hr
  · iframe; iframe #
  icases Hr with (⟨%Herr, -⟩ | ⟨%Herr, Htok, Hmb₃, #Hdd₃⟩)
  · cases err with
    | nil => exact absurd rfl Herr
    | ok ei => ?_
    wp_auto
    iapply HΦ; itrivial
  subst Herr
  wp_auto
  wp_apply (wp_newMember N s₁ name₁ peerAddr₁ clientAddr₁ (slice.mk peer₁ (W64 1) (W64 1)) ρ₁ E₁
      lg γn id₁ (hown _ _ hd₁)) $$ [Htok Hmb₁ Ha₁ Ho₁] as %m₁ %err Hr
  · iframe; iframe #
  icases Hr with (⟨%Herr, -⟩ | ⟨%Herr, %γS₁, Hup₁, Hrec₁⟩)
  · cases err with
    | nil => exact absurd rfl Herr
    | ok ei => ?_
    wp_auto
    iapply HΦ; itrivial
  subst Herr
  wp_auto
  icases etcd_restart1.memberUp_splitStop hRS s₁ ρ₁ E₁ lg γn id₁ .none $$ Hup₁ with
    ⟨%Ea₁, %γw₁, %dd₁, %HE₁, #Hreq₁, #Hrd₁, #Hrvb₁, Hgo₁, Hsr₁, Hrds₁⟩
  iunfold srvGoRes at Hgo₁
  icases Hgo₁ with ⟨-, Htok⟩
  wp_apply (wp_newMember N s₂ name₂ peerAddr₂ clientAddr₂ (slice.mk peer₂ (W64 1) (W64 1)) ρ₂ E₂
      lg γn id₂ (hown _ _ hd₂)) $$ [Htok Hmb₂ Ha₂ Ho₂] as %m₂ %err Hr
  · iframe; iframe #
  icases Hr with (⟨%Herr, -⟩ | ⟨%Herr, %γS₂, Hup₂, Hrec₂⟩)
  · cases err with
    | nil => exact absurd rfl Herr
    | ok ei => ?_
    wp_auto
    iapply HΦ; itrivial
  subst Herr
  wp_auto
  icases etcd_restart1.memberUp_splitStop hRS s₂ ρ₂ E₂ lg γn id₂ .none $$ Hup₂ with
    ⟨%Ea₂, %γw₂, %dd₂, %HE₂, #Hreq₂, #Hrd₂, #Hrvb₂, Hgo₂, Hsr₂, Hrds₂⟩
  iunfold srvGoRes at Hgo₂
  icases Hgo₂ with ⟨-, Htok⟩
  wp_apply (wp_newMember N s₃ name₃ peerAddr₃ clientAddr₃ (slice.mk peer₃ (W64 1) (W64 1)) ρ₃ E₃
      lg γn id₃ (hown _ _ hd₃)) $$ [Htok Hmb₃ Ha₃ Ho₃] as %m₃ %err Hr
  · iframe; iframe #
  icases Hr with (⟨%Herr, -⟩ | ⟨%Herr, %γS₃, Hup₃, Hrec₃⟩)
  · cases err with
    | nil => exact absurd rfl Herr
    | ok ei => ?_
    wp_auto
    iapply HΦ; itrivial
  subst Herr
  wp_auto
  icases etcd_restart1.memberUp_splitStop hRS s₃ ρ₃ E₃ lg γn id₃ .none $$ Hup₃ with
    ⟨%Ea₃, %γw₃, %dd₃, %HE₃, #Hreq₃, #Hrd₃, #Hrvb₃, Hgo₃, Hsr₃, Hrds₃⟩
  iunfold srvGoRes at Hgo₃
  icases Hgo₃ with ⟨-, Htok⟩
  -- the `N1` puts of `key(i) ↦ value(i)` through member 1, the counter's half passed along
  ihave HI : (∃ j : w64, "i" ∷ i_ptr ↦ j ∗ "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ 5⌝ ∗
      "Htok" ∷ threadTok ∗ "Hd" ∷ monoNatAuthOwn γc (1 : Qp).half (sint.nat j) : IProp GF)
      $$ [i Htok Hd]
  · iexists W64 0; iframe; ipureintro; constructor <;> word
  wp_for HI
  wp_if_destruct
  · wp_apply (wp_put' wp_put s₁ Ea₁ { ρ₁ with wait := γw₁ } γc j Hj.1
        (by have := Hif; simp only [show sint.Z (W64 5) = 5 by rfl] at this; simp only [r3NPuts]; omega)
        HE₁.2 HLv) $$ [Htok Hd] as %perr ⟨Htok, Hput⟩
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
    have hj1 : sint.nat (j + W64 1) = sint.nat j + 1 := by
      have := Hif; simp only [show sint.Z (W64 5) = 5 by rfl] at this
      unfold sint.nat; word
    rw [hj1]
    iframe
    ipureintro; constructor <;> word
  have hj5 : sint.nat j = 5 := by
    have := Hif; simp only [show sint.Z (W64 5) = 5 by rfl] at this
    unfold sint.nat; word
  rw [hj5]
  ihave #Hlb5 := monoNatLbOwn_get γc _ 5 $$ Hd
  -- `s3.Leader() == s3.MemberID()`
  ihave ⟨#Hlead₃, %mid₃, #Hmid₃⟩ := leadInv_memberID_of_req s₃ Ea₃ { ρ₃ with wait := γw₃ } $$ Hreq₃
  wp_apply (wp_Leader s₃) as %l -
  · iframe #
  wp_apply (wp_MemberID s₃ mid₃)
  · iframe #
  -- the `if`, proved with the stopped member as its postcondition
  ihave #Hai₂ := isServerRead_applied s₂ Ea₂ ρ₂.rd $$ Hrd₂
  ihave #Hai₃ := isServerRead_applied s₃ Ea₃ ρ₃.rd $$ Hrd₃
  wp_bind (If _ _ _)
  iapply (wp_wand (Φ := fun v => iprop(⌜v = executeVal⌝ ∗ ∃ mm ss : Loc, m_ptr ↦ mm ∗ s_ptr ↦ ss ∗
      stopCand N mm ss γn γ ρ₁ id₁ id₂ id₃ ps ctxs boot M))) $$ [m s m2 s2 Hrec₂ Hrec₃ Hsr₂ Hsr₃ Hrds₂ Hrds₃]
  · wp_if_destruct
    · -- member 3 leads: member 2 is stopped
      isplitr; · itrivial
      iexists m₂, s₂
      iframe m s
      iunfold stopCand
      iexists name₂, peerAddr₂, clientAddr₂, id₂, reg₂, ρ₂, Ea₂, dd₂, γS₂
      iframe Hrec₂ Hsr₂ Hrds₂
      iframe Hnet₂
      iframe #
      ipureintro
      exact ⟨hd₂, hUok _ _, by decide, by decide, hst₂, HE₂.2, by rw [HE₂.1.2.2.2, hc₂]⟩
    · -- member 3 is stopped
      isplitr; · itrivial
      iexists m₃, s₃
      iframe m s
      iunfold stopCand
      iexists name₃, peerAddr₃, clientAddr₃, id₃, reg₃, ρ₃, Ea₃, dd₃, γS₃
      iframe Hrec₃ Hsr₃ Hrds₃
      iframe Hnet₃
      iframe #
      ipureintro
      exact ⟨hd₃, hUok _ _, by decide, by decide, hst₃, HE₃.2, by rw [HE₃.1.2.2.2, hc₃]⟩
  iintro %v ⟨%Hv, %mm, %ss, Hm, Hs, Hc⟩
  subst Hv
  wp_auto
  iunfold stopCand at Hc
  icases Hc with ⟨%name, %peerAddr, %client, %id, %reg, %ρ, %E, %dd, %γS, ⟨%hd, %hU, %hpf, %hcf, %hst, %hsc⟩,
    Hrec, #Hai, #Hdd, Hsr, Hrds, #Hnet, #HbR, #Hrfs⟩
  -- `stop(s)`
  ihave %Hρr : ⌜ρ.rd.raft.raft = { γ with reg := reg }⌝ $$ []
  · ihave #Hf := Hrfs
    iunfold etcdstart.memberRestartFacts at Hf
    icases Hf with ⟨%Hρ, -⟩
    ipureintro; rw [Hρ.1]
  have Hb3 : ρ.rd.raft.raft.boot.length ≤ 3 := by
    rw [Hρr]; show γ.boot.length ≤ 3; rw [hboot]; exact hb3
  wp_apply (wp_stop ss E E ρ id dd γn name Hb3 hsc) $$ [Hsr Hrds] as Hrr
  · iframe; iframe #
  rw [Hρr]
  (try wp_auto)
  -- the `N2` puts, the counter's half passed along
  ihave HI : (∃ j : w64, "i" ∷ i_ptr ↦ j ∗ "%Hj" ∷ ⌜5 ≤ sint.Z j ∧ sint.Z j ≤ 25⌝ ∗
      "Htok" ∷ threadTok ∗ "Hd" ∷ monoNatAuthOwn γc (1 : Qp).half (sint.nat j) : IProp GF)
      $$ [i Htok Hd]
  · iexists W64 5; iframe; ipureintro; constructor <;> word
  wp_for HI
  wp_if_destruct
  · wp_apply (wp_put' wp_put s₁ Ea₁ { ρ₁ with wait := γw₁ } γc j (by have := Hj.1; omega)
        (by have := Hif; simp only [show sint.Z (W64 25) = 25 by rfl] at this; simp only [r3NPuts]; omega)
        HE₁.2 HLv) $$ [Htok Hd] as %perr ⟨Htok, Hput⟩
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
    have hj1 : sint.nat (j + W64 1) = sint.nat j + 1 := by
      have := Hif; simp only [show sint.Z (W64 25) = 25 by rfl] at this
      unfold sint.nat; word
    rw [hj1]
    iframe
    ipureintro; constructor <;> word
  have hj25 : sint.nat j = r3NPuts := by
    have := Hif; simp only [show sint.Z (W64 25) = 25 by rfl] at this
    simp only [r3NPuts]; unfold sint.nat; word
  rw [hj25]
  ihave #Hlb := monoNatLbOwn_get γc _ r3NPuts $$ Hd
  -- `sR, err := restartMember(m, cluster, lg)`
  wp_apply (wp_restartMember N mm γS name peerAddr client pm lg M initURLs3 (urlsOk peerAddr client) ps
      (LogEntry.toEntries boot 0) ctxs (dir3 id₁ id₂ id₃) id { γ with reg := reg } ρ γn HwbN hvs hrule
      hboot hblen hγn1 hγn2 (dir3_ok id₁ id₂ id₃ ps ctxs boot Hbf) hd
      (dir3_dirsOk id₁ id₂ id₃ ps ctxs boot Hbf) hU hpf hcf Haf Hbuq Hdbo) $$ [Htok Hrec Hrr] as %sR %err Hr
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
  · rw [← r3Inv_st ρ₁.rd.kv ρ'.rd.kv (hst.symm.trans (restartNames_st Hρ').symm) γc]
    iexact Hinv
  wp_apply (wp_check sR ρ' E₀' lg γn id γc HLv) $$ [HupR] as %b -
  · iframe; iframe #
  iapply HΦ; itrivial

end proof

end etcd_restart
end EtcdGrove
end Perennial
