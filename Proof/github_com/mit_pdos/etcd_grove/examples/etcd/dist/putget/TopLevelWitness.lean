/- Lean-first (no Rocq counterpart).

# `etcd/dist/putget`: its top-level statement's premises are satisfiable

`premise_sat%` (`Robustness/PremiseSat.lean`): the premises of `putget_safe`
(`Spec/github_com/mit_pdos/etcd_grove/examples/etcd/dist/putget/TopLevelRobustness.lean`) hold together
with `Robust`'s antecedents, at the deployment `putget_test.go` runs (`robust.NewNetwork`'s first machine,
the member, at `10.77.1.1`): the member `putgetd` (`name`) at the peer address `10.77.1.1:2380` and the
client address `10.77.1.1:2379`.

- **`bootstrap`'s results** (`Hbf : BootFacts id ctxs boot`, `Hbg : BootGo1 name peer client id ctxs
  boot`) at the values Go computes: the member id `pgId`, the first eight bytes of
  `sha1("http://10.77.1.1:2380" ++ "putgetd")` (`bootGo.memberID`, evaluated by the kernel:
  `pgId_eq`), the one context `json.Marshal` of the member (`bootGo.memberJSON pgMember`), and the
  bootstrap log of its one conf change, whose bytes are `proto.Marshal`'s (`ccBootWire`) and decode back
  (`ccDecodeV1`, a definition since 2026-11-24, `ccDecodeV1_bootWire`). `BootGo1`'s facts hold at every
  `BootURLs` `urls1` admits (its initial cluster the one entry `putgetd`).
- **The start states**: the member machine's file system has the two roots its member uses, its data
  directory `/tmp/etcd-grove-data/putgetd.etcd` and WAL area `/tmp/etcd-grove-wal/putgetd.etcd`, both
  empty (`fsRoots`, `MemberFiles`); the client machine's the root `/tmp`, empty (`ClientFiles`); no
  listener, no connection, an empty issue record.
- **Left out** (`etc/premise-witness-baseline.txt`, class `opaque`): the environment premises stated over
  opaque propositions or values, which no Lean proof can establish: `Haf` (`authRecordsFit`), `Hbuq`
  (`apply.backendUnderQuota`), `Hrf` (`grpcRepliesFit`), `Hdbo` (`storage.diskOk`: the opaque
  `dbOpensOk`, `snap.dirReadOk`, `backend.renameOk`), `Hfips` (`GodebugFips140Off`, over the opaque
  `godebugFips140`) and `HEnv` (`EtcdVerifyOff`, over the opaque `etcdVerifyEnv`; its value predicate
  holds of the unset variable, `etcdVerifyOffValue_unset`).

Checked by `etc/premise-witness.py`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.putget.TopLevelRobustness
public import Robustness.FsStart
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.RaftModel.Varint
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.BootBuild

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial
namespace EtcdGrove
namespace etcd_putget_dist

open go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver Wire Robustness Fs

attribute [local instance] etcdNetExts etcdNetExtsSemantics etcdNetExtsInterp etcdNetExts_hasIdIssue
  etcdNetExts_hasFs etcdNetExts_hasNet etcdFsSem

/-! ## The deployment's values -/

/-- The member's peer address (`putget_test.go`: the first machine's `10.77.1.1`, port `2380`). -/
def peerA : GoString := go!"10.77.1.1:2380"

/-- The member's client address (port `2379`). -/
def clientA : GoString := go!"10.77.1.1:2379"

/-- **The member id** Go computes for `putgetd` at `http://10.77.1.1:2380` (`computeMemberID`: the first
eight bytes, big-endian, of `sha1("http://10.77.1.1:2380putgetd")`, `0x056ec5b9d2ed9cd0`). -/
def pgId : w64 := W64 391467619526221008

/-- The member `NewMember` makes (`bootGo.memberOf`): its id, its peer URL, a voter, its name, no client
URLs. -/
def pgMember : apply.MemberM := ⟨pgId, [go!"http://" ++ peerA], false, name, []⟩

/-- Its context, `json.Marshal` of it. -/
def pgCtx : List w8 := bootGo.memberJSON pgMember

/-- **The bootstrap log**: one conf-change entry of term `1`, `proto.Marshal`'s bytes of
`ConfChange{Type: AddNode, NodeId: pgId, Context: pgCtx}`. -/
def pgBoot : List LogEntry := [⟨W64 1, W32 1, ccBootWire pgId pgCtx⟩]

/-! ## The member id and context -/

/-- **The member id is SHA-1's**: the kernel evaluates `bootGo.sha1` (Perennial's `crypto.sha1.sha1`,
`bootGo.sha1_eq`), its message schedule's `for` loops restated as folds (`crypto.sha1.schedule_eq`; the
kernel does not reduce the loops' `forIn`, nor `List.mergeSort`'s well-founded recursion). -/
theorem pgId_eq : bootGo.memberID [go!"http://" ++ peerA] name = pgId := by
  unfold bootGo.memberID
  rw [List.mergeSort_singleton, List.flatten_singleton, bootGo.sha1_eq]
  unfold crypto.sha1.sha1 crypto.sha1.compress
  rw [show crypto.sha1.schedule = _ from funext crypto.sha1.schedule_eq]
  decide +kernel

theorem pgMember_plain : membership.memberPlain pgMember := by
  refine ⟨by decide +kernel, by decide +kernel, by simp [pgMember]⟩

/-- `decNat n` has at most `k` digits for `n < 10 ^ k`. -/
theorem decNat_length_le : ∀ (k n : Nat), n < 10 ^ k → (models_lab.jsoncodec.decNat n).length ≤ k + 1 := by
  intro k
  induction k with
  | zero => intro n h; rw [models_lab.jsoncodec.decNat]; simp at h; simp [h]
  | succ k ih =>
    intro n hn
    rw [models_lab.jsoncodec.decNat]
    by_cases h : n < 10
    · simp [h]
    · simp only [h, ↓reduceIte, List.length_append, List.length_singleton]
      have := ih (n / 10) (by rw [Nat.pow_succ] at hn; omega)
      omega

theorem pgCtx_length : pgCtx.length ≤ 200 := by
  have hq : ∀ s : List w8, (∀ c ∈ s, JsonScan.plainEnc c) →
      (models_lab.jsoncodec.jsonQuote s).length = s.length + 2 := by
    intro s hs; rw [models_lab.jsoncodec.jsonQuote_plain s hs]; simp
  have hd : (models_lab.jsoncodec.decU64 pgId).length ≤ 20 := by
    unfold models_lab.jsoncodec.decU64
    exact decNat_length_le 19 _ (by unfold pgId; decide +kernel)
  have hu := hq (go!"http://" ++ peerA) (pgMember_plain.2.1 _ (List.mem_singleton_self _))
  have hn := hq name pgMember_plain.1
  have hne : (name : GoString) ≠ [] := by decide +kernel
  simp only [pgCtx, bootGo.memberJSON, pgMember, membership.jsonStrSlice, membership.jsonStrs,
    Bool.false_eq_true, ↓reduceIte, hne, List.length_append, List.length_cons, List.length_nil, hu, hn]
  have h1 : (go!"http://" ++ peerA).length ≤ 30 := by decide +kernel
  have h6 : peerA.length ≤ 20 := by decide +kernel
  have h2 : (name : GoString).length ≤ 10 := by decide +kernel
  have h3 : (go!"\"id\":" : GoString).length ≤ 10 := by decide +kernel
  have h4 : (go!",\"peerURLs\":" : GoString).length ≤ 20 := by decide +kernel
  have h5 : (go!",\"name\":" : GoString).length ≤ 10 := by decide +kernel
  omega

/-! ## The bootstrap log's bytes decode -/

theorem pgDecode : ccDecodeV1 (ccBootWire pgId pgCtx) = some ⟨W32 0, pgId, pgCtx, W64 0⟩ :=
  ccDecodeV1_bootWire pgId pgCtx (by have := pgCtx_length; omega)

/-! ## `bootstrap`'s results -/

theorem pgBootLog : BootLog [pgId] [pgCtx] pgBoot := by
  refine ⟨rfl, by simp [pgBoot], ?_⟩
  intro k e hk
  rcases k with _ | k
  · simp only [pgBoot, List.getElem?_cons_zero, Option.some.injEq] at hk
    subst hk
    exact ⟨pgId, pgCtx, rfl, rfl, rfl, rfl, pgDecode⟩
  · simp [pgBoot] at hk

theorem pgBootCore : BootCore [pgId] [pgCtx] pgBoot := by
  refine ⟨pgBootLog, ?_, ?_, by simp, ?_, ?_, ?_⟩
  · intro e he
    simp only [pgBoot, LogEntry.toEntries, List.mapIdx_cons, List.mapIdx_nil, List.mem_singleton] at he
    subst he
    refine ⟨ccIdOf_of_decode pgDecode, ?_⟩
    intro m hm
    rw [show (LogEntry.toEntryM _ _ : EntryM).Data' = ccBootWire pgId pgCtx from rfl, pgDecode] at hm
    cases hm
    refine ⟨rfl, (GMap.elem_of_list_to_set _ _).2 (List.mem_singleton_self _), ?_, ?_⟩
    · exact bootGo.ccContextOf_memberJSON pgMember pgMember_plain
    · rw [show (⟨W32 0, pgId, pgCtx, W64 0⟩ : ConfChangeM).context = bootGo.memberJSON pgMember from rfl,
        bootGo.ccMemberOf_memberJSON pgMember pgMember_plain]
      rfl
  · have hm : bootMembers (LogEntry.toEntries pgBoot 0) = [pgMember] := by
      simp only [bootMembers, pgBoot, LogEntry.toEntries, List.mapIdx_cons, List.mapIdx_nil,
        List.filterMap_cons, List.filterMap_nil]
      rw [show (LogEntry.toEntryM _ _ : EntryM).Data' = ccBootWire pgId pgCtx from rfl, pgDecode]
      simp only [Option.map_some]
      show [membership.ccMemberOf (bootGo.memberJSON pgMember)] = [pgMember]
      rw [bootGo.ccMemberOf_memberJSON pgMember pgMember_plain]
    rw [bootURLsOk, hm]
    refine ⟨?_, by simp⟩
    intro mm hmm u hu
    simp only [List.mem_singleton] at hmm
    subst hmm
    simp only [pgMember, List.mem_singleton] at hu
    subst hu
    decide +kernel
  · intro id hid
    simp only [List.mem_singleton] at hid
    subst hid
    unfold pgId; decide +kernel
  · intro e he
    simp only [pgBoot, List.mem_singleton] at he
    subst he
    show (ccBootWire pgId pgCtx).length + 64 ≤ bootCtxMax
    have hv1 := varintEnc_length_w64 (uint.nat pgId) (by simp [uint.nat]; exact pgId.isLt)
    have hv2 := varintEnc_length_w64 pgCtx.length (by have := pgCtx_length; omega)
    have hl := pgCtx_length
    rw [ccBootWire_bytes]
    by_cases hc : pgCtx = []
    · simp only [hc, ↓reduceIte, List.length_append, List.length_cons, List.length_nil, bootCtxMax]
      omega
    · simp only [hc, ↓reduceIte, List.length_append, List.length_cons, List.length_nil, bootCtxMax]
      omega
  · intro k e id ctx he hi hc
    rcases k with _ | k
    · simp [pgBoot] at he hi hc
      subst he hi hc
      rfl
    · simp [pgBoot] at he

/-- The domain of a one-entry map is its key. -/
theorem domList_single {V : Type} (k : GoString) (v : V) :
    (GMap.insert k v (∅ : GMap GoString V)).domList = [k] := by
  have hnd := GMap.nodup_dom_list (GMap.insert k v (∅ : GMap GoString V))
  have hmem : ∀ x, x ∈ (GMap.insert k v (∅ : GMap GoString V)).domList ↔ x = k := by
    intro x
    rw [GMap.mem_dom_list]
    by_cases h : k = x <;> simp [h, eq_comm]
  generalize (GMap.insert k v (∅ : GMap GoString V)).domList = l at hnd hmem
  rcases l with _ | ⟨a, t⟩
  · exact absurd ((hmem k).2 rfl) (by simp)
  · have ha : a = k := (hmem a).1 (List.mem_cons_self ..)
    subst ha
    rcases t with _ | ⟨b, t⟩
    · rfl
    · have hb : b = a := (hmem b).1 (by simp)
      subst hb
      simp at hnd

theorem pgBootGo : etcdstart.BootGo1 name peerA clientA pgId [pgCtx] pgBoot := by
  refine ⟨⟨by unfold pgId; decide +kernel, by unfold pgId; decide +kernel⟩, pgBootLog, ?_⟩
  intro U ⟨_, _, ⟨sl, hmap⟩, hurls⟩
  have hdom : U.initMap.domList = [name] := by rw [hmap]; exact domList_single _ _
  have hsome : ∀ k, (U.initMap.lookup k).isSome → k = name := by
    intro k hk
    have : k ∈ U.initMap.domList := (GMap.mem_dom_list _ k).2 hk
    rw [hdom] at this
    exact List.mem_singleton.1 this
  have hof : bootGo.memberOf U name name = pgMember := by
    simp only [bootGo.memberOf, hurls, List.map_cons, List.map_nil, bootGo.urlStr,
      etcdstart.httpURL]
    rw [pgId_eq]
    rfl
  have hmembers : bootGo.members U name = [pgMember] := by
    simp only [bootGo.members, hdom, List.map_cons, List.map_nil, hof, List.mergeSort_singleton]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k hk u hu
    rw [hsome k hk, hurls, List.mem_singleton] at hu
    subst hu
    refine ⟨rfl, ?_, rfl, ?_, ?_, ?_, ?_, rfl, rfl, ?_, by decide +kernel, ?_⟩
    · simp [etcdstart.httpURL, stringToGoString]
    · simp [etcdstart.httpURL, stringToGoString]
    · simp [etcdstart.httpURL, stringToGoString]
    · simp [etcdstart.httpURL, stringToGoString]
    · simp [etcdstart.httpURL, stringToGoString]
    · simp [etcdstart.httpURL, stringToGoString]
    · show ∀ c ∈ peerA, http.hostByteNoEscape c
      unfold http.hostByteNoEscape
      decide +kernel
  · simp [bootGo.ps, hmembers, pgMember]
  · simp [bootGo.ctxs, hmembers, pgCtx]
  · funext i
    simp only [bootGo.dir, hmembers, etcdstart.dir1, dirOne, List.find?_cons, List.find?_nil]
    by_cases h : pgId = i
    · subst h; simp [pgMember, peerA]
    · simp [pgMember, h, Ne.symm h]
  · rw [hof]; rfl
  · intro k hk
    rw [hsome k hk, hurls]
    simp
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simp [hdom]
    · simp only [hdom, List.map_cons, List.map_nil, hof, List.mem_singleton]
      unfold pgMember pgId; decide +kernel
    · rw [GMap.size_eq_dom_list_length, hdom]; simp
    · simp [hdom, hurls]
    · simp only [hdom, hurls, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        bootGo.urlStr, etcdstart.httpURL]
      unfold peerA; decide +kernel

/-! ## The start states -/

/-- The member machine's roots: its WAL area and its data directory. -/
def memberRoots : List GoString := [walAreaOf (memberDataDir name), memberDataDir name]

theorem memberRoots_init : Fs.FsInit (fsRoots memberRoots) := by
  refine fsInit_fsRoots _ (by decide +kernel) ?_ (by decide +kernel)
  intro r hr
  simp only [memberRoots,
    List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨[go!"tmp", go!"etcd-grove-wal", go!"putgetd.etcd"], by simp, by decide +kernel,
      by decide +kernel⟩
  · exact ⟨[go!"tmp", go!"etcd-grove-data", go!"putgetd.etcd"], by simp, by decide +kernel,
      by decide +kernel⟩

/-- (As `etcdWalAreasInit_fsRoots`, `WalAreasInitSat.lean`, which `etc/api/etcdstart.txt` does not list.) -/
theorem memberRoots_walAreas : etcdWalAreasInit (fsRoots memberRoots) [memberDataDir name] := by
  intro d hd
  simp only [List.mem_singleton] at hd
  subst hd
  refine ⟨⟨name, rfl⟩, ?_, ?_⟩
  · obtain ⟨j, hj⟩ := fsRoots_root memberRoots (r := walAreaOf (memberDataDir name)) (by simp [memberRoots])
    exact ⟨j, hj, fun b _ => fsRoots_entry _ _ _⟩
  · obtain ⟨j, hj⟩ := fsRoots_root memberRoots (r := memberDataDir name) (by simp [memberRoots])
    exact ⟨j, hj, fun b => fsRoots_entry _ _ _⟩

/-- The client machine's root `/tmp`. -/
theorem tmp_rootForm : RootForm (slashB :: go!"tmp") := rootForm_one _ (by decide)


theorem putget_safe.premisesSat :
    premise_sat% putget_safe.spec without [Haf, Hbuq, Hrf, Hdbo, Hfips, HEnv] := by
  intros
  refine ⟨peerA, clientA, pgId, [pgCtx], pgBoot, pgBootCore, pgBootGo,
    freshState ((∅ : IdIssueState), fsRoots memberRoots, (default : Net.NetLocal), ()),
    freshState ((∅ : IdIssueState), fsOneRoot (slashB :: go!"tmp"), (default : Net.NetLocal), ()),
    ⟨((), (), (default : Net.NetGlobal), ()), ∅⟩,
    ⟨memberRoots_init, memberRoots_walAreas⟩, fsInit_fsOneRoot _ tmp_rootForm,
    by unfold peerA; decide +kernel, by unfold clientA; decide +kernel, ?_, by exts_init, ?_⟩
  · intro m hm
    simp only [system, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl <;> exact fresh_freshState _
  · intro m hm
    simp only [system, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl <;> exts_init

end etcd_putget_dist
end EtcdGrove
end Perennial

end
