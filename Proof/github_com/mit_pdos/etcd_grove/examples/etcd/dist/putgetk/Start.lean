/- Lean-first (no Rocq counterpart).

# `etcd/dist/putgetk`: the start, and `putgetK_safe` over S5's named hypotheses (plan item 4, §13b)

`putgetKBoot_of`: `PutgetKBoot` (the skeleton's named hypothesis, `TopLevelRobustness.lean`) from two named
hypotheses of phase 7 S5 (#24/#18), neither an axiom nor a premise of the statement:
* `HS5`: S5's names exist at every global ghost state and protocol registry (`etcd_dist.S5Holds`, the
  PLACEHOLDER structure `S5Draft`: rafthttp's peer-address fact and its start law);
* `HSM`: `etcdstart.StartMember` on a member machine (`etcd_dist.StartMember_dist.spec`, PLACEHOLDER).

The start: the protocol registry (`netProto_alloc`); then a case split on the program's check
(`cfgOk`):
* **`cfgOk`**: the cluster's start `etcd_dist.etcdClusterStart` (every peer address set to rafthttp's
  protocol, the cluster's allocation, each member's publication name and client address), the client's
  putget invariant allocated from the cluster's `etcdKV` (`client.putGetInv_alloc_all`), which gives every
  member's publication obligation (`memberPubOkK` at `putgetPub`); member `i`'s share is its
  `memberStartShare`, the client's is member `0`'s address and publication facts;
* **not `cfgOk`**: every member's `Valid` fails, so its share is trivial; the client's address (member
  `0`'s client address, if any) is set with a fresh publication name that no member publishes at.
`putgetK_safe_of_S5 : putgetK_safe.spec` over `HS5` and `HSM` (`putgetK_safe_of_boot`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.putgetk.TopLevelRobustness
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.putgetk.AdequacyMember
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.putgetk.AdequacyClient
public import Proof.go_etcd_io.etcd.client.v3.PutGetInvAlloc

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

namespace client

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3 go_etcd_io.etcd.server.v3.etcdserver

attribute [local instance] GooseGlobalGS.gooseInvGS

section allocG
variable [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext] {GF : BundledGFunctors}
variable [lctx : GoLocalContext] [sem : go.Semantics] [G : GooseGlobalGS .hasLC GF]

/-- **The client's putget invariant, allocated over the global ghost state** (`putGetInv_alloc_log` at no
machine's heap: the invariant reads the heap only through its global part,
`etcd_putget_dist.putGetInv_heap`), at every local ghost state over `G`. -/
theorem putGetInv_alloc_all (γr : ReadNames) (σ : KVState) (key val : GoString) :
    etcdKV (GF := GF) γr.kv σ ⊢ |={⊤}=> ∃ γf : GName,
      ∀ L : GooseLocalGS GF,
        putGetInv (hG := etcd_putget_dist.heapAt G L lctx) γr γf key val := by
  iintro Hσ
  imod (mono_nat_own_alloc (GF := GF) 0) with ⟨%γf, Hm, -⟩
  imod inv_alloc kvClientN ⊤ (iprop(∃ (σ : KVState) (n : Nat), etcdKV γr.kv σ ∗
      monoNatAuthOwn γf 1 n ∗ ⌜putGetOk key val σ n⌝)) $$ [Hσ Hm] with #Hinv
  · inext; iexists σ, 0; iframe Hσ Hm
    ipureintro; exact ⟨KVState.kvs_sorted _, fun h => absurd h (by omega)⟩
  imodintro
  iexists γf
  iintro %L
  iunfold putGetInv
  iexact Hinv

end allocG

end client

namespace etcd_putgetk_dist

open Iris Iris.BI Iris.ProofMode Iris.ProgramLogic Robustness go_etcd_io.raft.v3
  go_etcd_io.etcd.server.v3.etcdserver Net etcd_putget_dist

attribute [local instance] etcdNetExts etcdNetExtsSemantics etcdNetExtsInterp etcdNetExts_hasIdIssue
  etcdNetExts_hasFs etcdNetExts_hasNet etcdFsSem GooseGlobalGS.gooseInvGS

/-! ## Pure facts -/

theorem cms_clients [GooseExts] (peers clients : List GoString) (h : peers.length = clients.length) :
    (cmsOf (membersOf peers clients) (idsOf peers)).map (·.client) = clients := by
  rw [cms_eq]
  apply List.ext_getElem (by simp [h])
  intro n h1 h2
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]

theorem cms_length [GooseExts] (peers clients : List GoString) :
    (cmsOf (membersOf peers clients) (idsOf peers)).length = peers.length := by
  rw [cms_eq]; simp

theorem zip_getD_fst {α β : Type _} (d : α) : ∀ {l1 : List α} {l2 : List β} {k : Nat} {x : α × β},
    (l1.zip l2)[k]? = some x → l1.getD k d = x.1
  | [], _, _, _, h => by simp at h
  | _ :: _, [], _, _, h => by simp at h
  | a :: l1, b :: l2, 0, x, h => by
    simp only [List.zip_cons_cons, List.getElem?_cons_zero, Option.some.injEq] at h
    subst h; rfl
  | a :: l1, b :: l2, k + 1, x, h => by
    simp only [List.zip_cons_cons, List.getElem?_cons_succ] at h
    show l1.getD k d = x.1
    exact zip_getD_fst d h

theorem svc_head [GooseExts] (p0 c0 : GoString) (pr cr : List GoString) (γ0 : GName)
    (γr : List GName) :
    ∃ rest, etcd_dist.svcList ((cmsOf (membersOf (p0 :: pr) (c0 :: cr)) (idsOf (p0 :: pr))).zip
      (γ0 :: γr)) = ((c0, memberIdOf p0), γ0) :: rest := by
  rw [cms_eq]
  simp [etcd_dist.svcList]

/-- Read names at the cluster's KV names (the client's invariant reads only `kv`). -/
abbrev rnOf [GooseExts] (c : etcd_dist.ClusterNames) : ReadNames :=
  ⟨default, default, default, default, default, default, ⟨c.γ, [], W64 0⟩, c.γk⟩

section bigops
variable {GF : BundledGFunctors}

/-- A big separating conjunction whose body reads only the index, over two lists of one length. -/
theorem bigSepL_idx {A B : Type _} :
    ∀ (Φ : Nat → IProp GF) (l : List A) (l' : List B), l.length = l'.length →
      ([∗list] i ↦ _x ∈ l, Φ i) ⊢ [∗list] i ↦ _y ∈ l', Φ i
  | _, [], [], _ => by
    iintro -
    iapply BigSepL.bigSepL_nil.2
    iempintro
  | Φ, a :: l, b :: l', h => by
    iintro H
    ihave H := BigSepL.bigSepL_cons.1 $$ H
    icases H with ⟨H0, H⟩
    iapply BigSepL.bigSepL_cons.2
    isplitl [H0]
    · iexact H0
    iapply (bigSepL_idx (fun i => Φ (i + 1)) l l' (by simpa using h))
    iexact H
  | _, [], _ :: _, h => by simp at h
  | _, _ :: _, [], h => by simp at h

/-- A big separating conjunction each of whose conjuncts holds. -/
theorem bigSepL_of_all {A : Type _} :
    ∀ (l : List A) (Φ : Nat → A → IProp GF), (∀ k x, l[k]? = some x → ⊢ Φ k x) →
      ⊢ [∗list] k ↦ x ∈ l, Φ k x
  | [], _, _ => BigSepL.bigSepL_nil.2
  | a :: l, Φ, h => by
    iapply BigSepL.bigSepL_cons.2
    isplitl []
    · iapply (h 0 a rfl)
    · iapply (bigSepL_of_all l (fun k x => Φ (k + 1) x) (fun k x hk => h (k + 1) x hk))

end bigops

/-! ## The machines' shares -/

section shares
variable [GoGlobalContext] [lctx : GoLocalContext] [sem : go.Semantics]
  [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.putgetk.Assumptions]
  [G : GooseGlobalGS .hasLC putgetGF] [π : NetProtoGS]

/-- Member `i`'s machine's share (`member_bootK`'s). -/
def memberPK (S5 : etcd_dist.S5Draft putgetGF) (peers clients : List GoString) (ps : List w64)
    (ctxs : List (List w8)) (boot : List LogEntry) (i : Nat) : IProp putgetGF :=
  iprop(⌜cfgOk peers clients ∧ i < peers.length⌝ -∗ ∃ (c : etcd_dist.ClusterNames) (γE : GName),
    memberShareK S5 c peers clients ps ctxs boot i γE (putgetPub (GF := putgetGF)))

/-- The client machine's share (`client_bootK`'s). -/
def clientPK (ep : GoString) (γE : GName) (mid : w64) : IProp putgetGF :=
  iprop(⌜ep ≠ []⌝ -∗ ⌜Net.addrOk ep = true⌝ ∗ clientShare ep γE mid (putgetPub (GF := putgetGF)))

/-- The machines' shares: member `i`'s for `i < n`, then the client's. -/
def sharesK (S5 : etcd_dist.S5Draft putgetGF) (peers clients : List GoString) (ps : List w64)
    (ctxs : List (List w8)) (boot : List LogEntry) (γE : GName) (mid : w64) (i : Nat) :
    IProp putgetGF :=
  if i < peers.length then memberPK S5 peers clients ps ctxs boot i
  else clientPK (clients.headD go!"") γE mid

end shares

set_option maxHeartbeats 1600000 in
/-- **Every machine's boot is safe from its share** (`member_bootK`, `client_bootK`). -/
theorem system_boots [GoGlobalContext] [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.putgetk.Assumptions]
    [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]
    [go_etcd_io.etcd.client.v3.DialWithBalancerBody] [log.NewModel] [net.FieldAssumptions]
    (Hctx : ∀ hG : HeapGS .hasLC putgetGF,
      ContextReadErrs (GF := putgetGF) (hG := putgetHeapAt hG lctx))
    (Hcec : ∀ hG : HeapGS .hasLC putgetGF,
      ContextErrsClient (GF := putgetGF) (hG := putgetHeapAt hG lctx))
    (HEnvTok : ⊢ envVerifyOff (GF := putgetGF))
    (HSM : ∀ (hG : HeapGS .hasLC putgetGF) [π : NetProtoGS]
      (S5 : etcd_dist.S5Draft (G := (putgetHeapAt hG lctx).goose_globalGS) putgetGF),
      etcd_dist.StartMember_dist.spec (GF := putgetGF) (hG := putgetHeapAt hG lctx) S5)
    (peers clients : List GoString) (ps : List w64) (ctxs : List (List w8)) (boot : List LogEntry)
    (Hbl : BootLogFacts (idsOf peers) ps ctxs boot)
    (Haf : authRecordsFit) (Hbuq : apply.backendUnderQuota) (Hrf : grpcRepliesFit)
    (Hdbo : storage.diskOk)
    (Hprem : ∀ n : Nat, n + 12 ≤ 2 ^ 40 → ∀ hG : HeapGS .hasLC putgetGF,
      ⊢ premises (GF := putgetGF) (hG := putgetHeapAt hG lctx) n peers clients ps ctxs boot)
    (σs : Nat → state) (σc : state) (Hm : ∀ i < peers.length, MemberFiles i (σs i))
    (Hfips : crypto.fips140.GodebugFips140Off)
    [G : GooseGlobalGS .hasLC putgetGF] [π : NetProtoGS] (S5 : etcd_dist.S5Draft putgetGF)
    (γE : GName) (mid : w64) :
    ∀ (i : Nat) (m : Expr × state), (system peers clients σs σc)[i]? = some m →
      Net.DistBootWpSL srvLevelK (2 ^ 28 - 1) m.1 m.2
        (sharesK S5 peers clients ps ctxs boot γE mid i) := by
  intro i m hm
  unfold system at hm
  have hlen : (peers.mapIdx (fun i _ => (bootMember peers clients i, σs i))).length = peers.length := by
    simp
  by_cases hi : i < peers.length
  · rw [List.getElem?_append_left (by rw [hlen]; exact hi), List.getElem?_mapIdx] at hm
    obtain ⟨p, -, rfl⟩ := Option.map_eq_some_iff.1 hm
    unfold sharesK
    rw [if_pos hi]
    exact member_bootK HEnvTok Hctx HSM peers clients ps ctxs boot Hbl Haf Hbuq Hrf Hdbo Hprem Hfips i hi
      (σs i) (Hm i hi) S5
  · rw [List.getElem?_append_right (by omega), hlen] at hm
    have hm' : m = (bootClient (clients.headD go!""), σc) := by
      rcases h : i - peers.length with _ | k
      · rw [h] at hm
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hm
        exact hm.symm
      · rw [h] at hm; simp at hm
    subst hm'
    unfold sharesK
    rw [if_neg hi]
    exact client_bootK Hctx Hcec (clients.headD go!"") σc γE mid

set_option maxHeartbeats 3200000 in
/-- **`PutgetKBoot` over S5's named hypotheses** (see the file header). -/
theorem putgetKBoot_of
    (HS5 : ∀ [GoGlobalContext], etcd_dist.S5Holds putgetGF)
    (HSM : ∀ [GoGlobalContext] [lctx : GoLocalContext] [sem : go.Semantics]
      [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.putgetk.Assumptions]
      (hG : HeapGS .hasLC putgetGF) [π : NetProtoGS]
      (S5 : etcd_dist.S5Draft (G := (putgetHeapAt hG lctx).goose_globalGS) putgetGF),
      etcd_dist.StartMember_dist.spec (GF := putgetGF) (hG := putgetHeapAt hG lctx) S5) :
    PutgetKBoot := by
  intro _ lctx _ _ _ _ _ _ Hctx Hcec peers clients ps ctxs boot Hbl Haf Hbuq Hrf Hdbo Hprem σs σc Hm Hc
    Hfips Hnd Hok HEnv HEnvTok G hlo hb
  have hS5' : ∀ [G : GooseGlobalGS .hasLC putgetGF] [π : NetProtoGS],
      Nonempty (etcd_dist.S5Draft putgetGF) := HS5
  have HSM' : ∀ (hG : HeapGS .hasLC putgetGF) [π : NetProtoGS]
      (S5 : etcd_dist.S5Draft (G := (putgetHeapAt hG lctx).goose_globalGS) putgetGF),
      etcd_dist.StartMember_dist.spec (GF := putgetGF) (hG := putgetHeapAt hG lctx) S5 := by
    intro hG π S5
    exact @HSM _ lctx _ _ hG π S5
  iintro Hs
  imod netProto_alloc ⊤ with ⟨%π, #Hreg⟩
  have S5 : etcd_dist.S5Draft putgetGF := Classical.choice hS5'
  rcases Classical.em (cfgOk peers clients) with hcfg | hcfg
  · -- the cluster's start
    have hcfg' := hcfg
    obtain ⟨hne, hlen, hids⟩ := hcfg'
    obtain ⟨Hpfxnd, -, HidsLen⟩ := idPfxsOf_ok (idsOf peers) hids.1 hids.2
    obtain ⟨p0, pr, rfl⟩ : ∃ p0 pr, peers = p0 :: pr := by
      cases peers with
      | nil => exact absurd rfl hne
      | cons a r => exact ⟨a, r, rfl⟩
    obtain ⟨c0, cr, rfl⟩ : ∃ c0 cr, clients = c0 :: cr := by
      cases clients with
      | nil => simp at hlen
      | cons a r => exact ⟨a, r, rfl⟩
    have hperm : ps.Perm ((cmsOf (membersOf (p0 :: pr) (c0 :: cr)) (idsOf (p0 :: pr))).map (·.id)) := by
      rw [cms_ids]; exact Hbl.perm
    have hmsne : cmsOf (membersOf (p0 :: pr) (c0 :: cr)) (idsOf (p0 :: pr)) ≠ [] := by
      intro h
      have := congrArg List.length h
      rw [cms_length] at this
      simp at this
    have Hbc : BootCore ps ctxs boot :=
      { boot := Hbl.boot, cc := Hbl.cc, urls := Hbl.urls, data := Hbl.data,
        lowNodup := (Hbl.perm.map _).nodup_iff.2 hids.1,
        lowNz := fun id h => hids.2 id (Hbl.perm.subset h) }
    have hbl : boot.length ≤ 2 ^ 16 := by rw [Hbl.boot.1, Hbl.perm.length_eq]; omega
    -- the addresses, per member
    ihave Hs2 : [∗list] m ∈ cmsOf (membersOf (p0 :: pr) (c0 :: cr)) (idsOf (p0 :: pr)),
        addrUnset m.peer ∗ addrUnset m.client $$ [Hs]
    · iapply BigSepL.bigSepL_sep_eqv.2
      unfold addrs
      ihave Hs := BigSepL.bigSepL_append.1 $$ Hs
      icases Hs with ⟨Hp, Hcl⟩
      isplitl [Hp]
      · iapply (show ([∗list] a ∈ (cmsOf (membersOf (p0 :: pr) (c0 :: cr)) (idsOf (p0 :: pr))).map
            (·.peer), addrUnset (GF := putgetGF) a) ⊢ [∗list] m ∈ cmsOf (membersOf (p0 :: pr) (c0 :: cr))
            (idsOf (p0 :: pr)), addrUnset (GF := putgetGF) m.peer by rw [BigSepL.bigSepL_map])
        rw [cms_peers]
        iexact Hp
      · iapply (show ([∗list] a ∈ (cmsOf (membersOf (p0 :: pr) (c0 :: cr)) (idsOf (p0 :: pr))).map
            (·.client), addrUnset (GF := putgetGF) a) ⊢ [∗list] m ∈ cmsOf (membersOf (p0 :: pr) (c0 :: cr))
            (idsOf (p0 :: pr)), addrUnset (GF := putgetGF) m.client by rw [BigSepL.bigSepL_map])
        rw [cms_clients _ _ hlen]
        iexact Hcl
    imod (etcd_dist.etcdClusterStart S5 (cmsOf (membersOf (p0 :: pr) (c0 :: cr)) (idsOf (p0 :: pr))) ps
        hperm hmsne ctxs boot Hbc (by omega) (by omega) .none (fun h => nomatch h) false 0
        (fun _ _ => putgetPub (GF := putgetGF))) $$ Hreg Hs2
      with ⟨%c, %γEs, %Hγ, Hms, #Hcs, Hetcd⟩
    obtain ⟨Hcok, hγlen⟩ := Hγ
    rw [cms_ids] at Hcok
    isimp only [ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte] at Hetcd
    -- the client's invariant, from the cluster's `etcdKV`
    ihave Hetcd' : etcdKV (GF := putgetGF) (rnOf c).kv
        (kvModelSt c.γk (bootEntries (LogEntry.toEntries boot 0))) $$ [Hetcd]
    · rw [show (rnOf c).kv = c.γk from rfl]
      iexact Hetcd
    imod (client.putGetInv_alloc_all (GF := putgetGF) (rnOf c)
        (kvModelSt c.γk (bootEntries (LogEntry.toEntries boot 0))) go!"k" go!"v") $$ Hetcd'
      with ⟨%γf, #Hinv⟩
    ihave #Hpub : memberPubOkK c.γk (putgetPub (GF := putgetGF)) $$ []
    · iunfold memberPubOkK
      imodintro
      iintro %ρ %hρ
      iunfold putgetPub
      iexists (rnOf c), γf
      isplitr
      · ipureintro; exact hρ.1.symm
      iexact Hinv
    obtain ⟨γ0, γr, rfl⟩ : ∃ γ0 γr, γEs = γ0 :: γr := by
      cases γEs with
      | nil => rw [cms_length] at hγlen; simp at hγlen
      | cons a r => exact ⟨a, r, rfl⟩
    obtain ⟨rest, hrest⟩ := svc_head p0 c0 pr cr γ0 γr
    -- the client's share: member `0`'s address and publication facts
    iunfold etcd_dist.clientStartShare at Hcs
    icases Hcs with ⟨-, #Hsvc⟩
    iunfold etcd_dist.clientSvcFacts at Hsvc
    isimp only [hrest] at Hsvc
    icases BigSepL.bigSepL_cons.1 $$ Hsvc with ⟨⟨#Hat0, #Hinv0⟩, -⟩
    imodintro
    iexists sharesK S5 (p0 :: pr) (c0 :: cr) ps ctxs boot γ0 (memberIdOf p0)
    isplitr
    · ipureintro
      exact system_boots Hctx Hcec HEnvTok HSM' (p0 :: pr) (c0 :: cr) ps ctxs boot Hbl Haf Hbuq Hrf Hdbo
        Hprem σs σc Hm Hfips S5 γ0 (memberIdOf p0)
    unfold system
    iapply BigSepL.bigSepL_append.2
    isplitl [Hms]
    · iapply (bigSepL_idx (sharesK S5 (p0 :: pr) (c0 :: cr) ps ctxs boot γ0 (memberIdOf p0))
        ((cmsOf (membersOf (p0 :: pr) (c0 :: cr)) (idsOf (p0 :: pr))).zip (γ0 :: γr)) _
        (by rw [List.length_zip, hγlen, Nat.min_self, cms_length, List.length_mapIdx]))
      iapply (BigSepL.bigSepL_impl (Ψ := fun k _ => sharesK S5 (p0 :: pr) (c0 :: cr) ps ctxs boot γ0
        (memberIdOf p0) k)) $$ Hms
      imodintro
      iintro %k %x %hk Hx
      have hkn : k < (p0 :: pr).length := by
        have := (List.getElem?_eq_some_iff.1 hk).1
        rw [List.length_zip, hγlen, Nat.min_self, cms_length] at this
        exact this
      unfold sharesK
      rw [if_pos hkn]
      iunfold memberPK
      iintro %-
      iexists c, x.2
      iunfold memberShareK
      rw [zip_getD_fst ⟨go!"", go!"", W64 0⟩ hk]
      isplitr
      · ipureintro; exact ⟨Hcok, Hnd, Hok⟩
      isplitl [Hx]
      · iexact Hx
      · iexact Hpub
    · iapply BigSepL.bigSepL_singleton.2
      unfold sharesK
      rw [if_neg (by simp)]
      simp only [List.headD_cons]
      iunfold clientPK
      iintro %-
      isplitr
      · ipureintro
        exact Hok c0 (by simp [addrs])
      iunfold clientShare
      isplitl
      · iexact Hat0
      · iexact Hinv0
  · -- no cluster: every member returns at once; the client's address set alone
    imod (etcd_dist.envPub_start ⊤ (putgetPub (GF := putgetGF))) with ⟨%γE, -, #HinvE⟩
    have hmem : ∀ k x, (peers.mapIdx (fun i _ => (bootMember peers clients i, σs i)))[k]? = some x →
        k < peers.length := by
      intro k x hk
      have := (List.getElem?_eq_some_iff.1 hk).1
      simpa using this
    cases clients with
    | nil =>
      imodintro
      iexists sharesK S5 peers [] ps ctxs boot γE (W64 0)
      isplitr
      · ipureintro
        exact system_boots Hctx Hcec HEnvTok HSM' peers [] ps ctxs boot Hbl Haf Hbuq Hrf Hdbo Hprem
          σs σc Hm Hfips S5 γE (W64 0)
      unfold system
      iapply BigSepL.bigSepL_append.2
      isplitl []
      · iapply (bigSepL_of_all _ _ (fun k x hk => by
          unfold sharesK
          rw [if_pos (hmem k x hk)]
          iunfold memberPK
          iintro %h
          exact absurd h.1 hcfg))
      · iapply BigSepL.bigSepL_singleton.2
        unfold sharesK
        rw [if_neg (by simp)]
        iunfold clientPK
        iintro %h
        exact absurd rfl h
    | cons c0 cr =>
      unfold addrs
      ihave Hs := BigSepL.bigSepL_append.1 $$ Hs
      icases Hs with ⟨-, Hcl⟩
      icases BigSepL.bigSepL_cons.1 $$ Hcl with ⟨Hu, -⟩
      imod (etcd_dist.etcdAddr_set ⊤ c0 γE (W64 0)) $$ Hreg Hu with #Hat
      imodintro
      iexists sharesK S5 peers (c0 :: cr) ps ctxs boot γE (W64 0)
      isplitr
      · ipureintro
        exact system_boots Hctx Hcec HEnvTok HSM' peers (c0 :: cr) ps ctxs boot Hbl Haf Hbuq Hrf Hdbo
          Hprem σs σc Hm Hfips S5 γE (W64 0)
      unfold system
      iapply BigSepL.bigSepL_append.2
      isplitl []
      · iapply (bigSepL_of_all _ _ (fun k x hk => by
          unfold sharesK
          rw [if_pos (hmem k x hk)]
          iunfold memberPK
          iintro %h
          exact absurd h.1 hcfg))
      · iapply BigSepL.bigSepL_singleton.2
        unfold sharesK
        rw [if_neg (by simp)]
        simp only [List.headD_cons]
        iunfold clientPK
        iintro %-
        isplitr
        · ipureintro
          exact Hok c0 (by simp [addrs])
        iunfold clientShare
        isplitl
        · iexact Hat
        · iexact HinvE

/-- **`putgetK_safe` over S5's named hypotheses** (see the file header): S5's names exist (`HS5`), and
`StartMember` on a member machine meets its PLACEHOLDER spec (`HSM`). Neither is an axiom or a premise of
`putgetK_safe.spec`; the trust base is otherwise the interim cross-machine axioms of `putget_safe`
(`notes/putget-dist-plan.md` §12). -/
theorem putgetK_safe_of_S5
    (HS5 : ∀ [GoGlobalContext], etcd_dist.S5Holds putgetGF)
    (HSM : ∀ [GoGlobalContext] [lctx : GoLocalContext] [sem : go.Semantics]
      [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.putgetk.Assumptions]
      (hG : HeapGS .hasLC putgetGF) [π : NetProtoGS]
      (S5 : etcd_dist.S5Draft (G := (putgetHeapAt hG lctx).goose_globalGS) putgetGF),
      etcd_dist.StartMember_dist.spec (GF := putgetGF) (hG := putgetHeapAt hG lctx) S5) :
    putgetK_safe.spec :=
  putgetK_safe_of_boot (putgetKBoot_of HS5 HSM)

end etcd_putgetk_dist
end EtcdGrove
end Perennial

end
