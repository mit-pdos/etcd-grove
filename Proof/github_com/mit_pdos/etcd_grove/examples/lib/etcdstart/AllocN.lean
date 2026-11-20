/-
**The ghost state an example's `Main` allocates before the members of a cluster of any size**
(the clusterN Scope, `notes/clusterN-scope.md`, 2026-11-15, its stage S2; the Scope's probes A-C).
Lean-first (no Rocq counterpart). `alloc3` for a list of members.

`allocN`: for the cluster of the members' ids `ids` (in the members' order), its peers `ps` in
`bootstrap`'s order (a permutation of the ids) and its bootstrap log (`BootCore`), each member's
start bundle (its name, its peer address, its optional client address) becomes its fresh bundle at
the raft network `γn` (the peer addresses reserved for the raft protocol, `netHttp_reserveL`), and
each member gets its ghost names (`MemberG`: its id, the cluster's names with its own storage
registry, its request names, its stand-in environment) with its `memberBoot`
(`newServerNames_allocL`, `srvClusterBoot_alloc`, `memberBoots_of`); the claimers' facts at a
member's prefix are its store's (`ΦsOf`, by the prefixes' distinctness). In the lease mode `none`
the client's `etcdKV` at the cluster's KV names `γk`, which every member's KV names agree with.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Alloc3
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.MembersDefs
import all Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.StartRes

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcdstart

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

section alloc
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [v3rpc_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- **Every address of a list reserved for the raft protocol** (`netHttp_reserve3` for any number
of addresses; probe A): the network's HTTP side for every member, and each address's protocol. -/
theorem netHttp_reserveL (γn : NetNames GF) (As : List GoString) (hd0 : γn.dir 0 = [])
    (hhost : ∀ (i : w64) (h : GoString), go!"http://" ++ h ∈ γn.dir i → h ∈ As) :
    ⊢ inv streamRegN iprop(∃ m : GMap GName StreamKey, ghostMapAuth γn.reg 1 m) -∗
      ([∗list] a ∈ As, httpProtoFree a) ==∗
      (□ ∀ lid : w64, netHttpOk γn lid) ∗
        [∗list] a ∈ As, http.httpProtoOwn a (raftProto (netRh γn)) := by
  have hres : ∀ (L : List GoString),
      ⊢ ([∗list] a ∈ L, httpProtoFree (GF := GF) a) ==∗
        (□ ∀ h, ⌜h ∈ L⌝ -∗ http.httpProtoAt h (raftProto (netRh γn))) ∗
        [∗list] a ∈ L, http.httpProtoOwn a (raftProto (netRh γn)) := by
    intro L
    induction L with
    | nil =>
      iintro -
      imodintro
      isplitl
      · iintro !> %h %hm
        simp at hm
      · iempintro
    | cons a L ih =>
      iintro Hfs
      ihave Hfs := BigSepL.bigSepL_cons.1 $$ Hfs
      icases Hfs with ⟨Hf, Hfs⟩
      imod (http.reserve a (raftProto (netRh γn)) (raftProto_srvOk _)) $$ Hf with ⟨#Hat, Ho⟩
      imod ih $$ Hfs with ⟨#Hats, Hos⟩
      imodintro
      isplitr [Ho Hos]
      · iintro !> %h %hm
        rcases List.mem_cons.1 hm with rfl | hm'
        · iexact Hat
        · iapply Hats $$ %h %hm'
      · iapply BigSepL.bigSepL_cons.2
        iframe
  iintro #Hreg Hfs
  imod (hres As) $$ Hfs with ⟨#Hats, Hos⟩
  imodintro
  iframe Hos
  iintro !> %lid
  iapply netHttpOk_of_dir γn lid hd0 $$ [Hreg]
  iframe Hreg
  iintro !> %i %h %Hm
  iapply Hats $$ %h %(hhost i h Hm.2)

/-- **Each member's names chosen before its `NewServer`, as functions of its id** (probe B): its
store's names, its certificate and revision maps and its storage registry. -/
theorem newServerNames_allocL (ps : List w64) (hnd : ps.Nodup) :
    ⊢ |==> ∃ (idx : w64 → srvApi.KVSNames) (cok rev reg : w64 → GName),
      [∗list] id ∈ ps, srvApi.newServerStoreFreshA (GF := GF) (idx id) ∗
        ghostMapAuth (cok id) 1 (∅ : GMap w64 mvcc.Log) ∗
        ghostMapAuth (rev id) 1 (∅ : GMap w64 Unit) ∗
        ghostMapAuth (reg id) 1 (∅ : GMap Loc MemStorNamesRec) := by
  let idx0 : srvApi.KVSNames := ⟨default, default, default, default⟩
  induction ps with
  | nil =>
    istart
    imodintro
    iexists (fun _ => idx0), (fun _ => default), (fun _ => default),
      (fun _ => default)
    iempintro
  | cons p ps ih =>
    istart
    imod (ih (List.nodup_cons.1 hnd).2) with ⟨%idx, %cok, %rev, %reg, Hs⟩
    imod newServerNames_alloc (GF := GF) with ⟨%i₀, %c₀, %r₀, Hi₀, Hc₀, Hr₀⟩
    imod ghost_map_alloc_empty (GF := GF) (K := Loc) (V := MemStorNamesRec) with ⟨%g₀, Hg₀⟩
    imodintro
    obtain ⟨hp, hnd'⟩ := List.nodup_cons.1 hnd
    iexists (fun id => if id = p then i₀ else idx id), (fun id => if id = p then c₀ else cok id),
      (fun id => if id = p then r₀ else rev id), (fun id => if id = p then g₀ else reg id)
    iapply BigSepL.bigSepL_cons.2
    simp only [ite_true]
    iframe Hi₀ Hc₀ Hr₀ Hg₀
    iapply (BigSepL.bigSepL_mono (fun {k x} hk => by
      have hx : x ≠ p := fun e => hp (e ▸ List.mem_of_getElem? hk)
      simp only [if_neg hx]; exact BI.entails_refl)) $$ Hs

/-- **The claimers' facts of a list of members** (probe C1): at a member's prefix, its store's. -/
def ΦsOf (ps : List w64) (idx : w64 → srvApi.KVSNames) : w64 → w64 → List w8 → GName → IProp GF :=
  fun p => srvFloorFacts ((idx ((ps.find? (fun id => decide (idPfxOf (W16 (uint.Z id)) = p))).getD 0)).slog)

/-- **The key registrations of a list of members**: at a member's prefix, its store's index. -/
def xsOf (ps : List w64) (idx : w64 → srvApi.KVSNames) : w64 → GName :=
  fun p => (idx ((ps.find? (fun id => decide (idPfxOf (W16 (uint.Z id)) = p))).getD 0)).slog

theorem find_pfx (ps : List w64) (hnd : (idPfxsOf ps).Nodup) (id : w64) (hid : id ∈ ps) :
    ps.find? (fun id' => decide (idPfxOf (W16 (uint.Z id')) = idPfxOf (W16 (uint.Z id)))) =
      some id := by
  induction ps with
  | nil => simp at hid
  | cons q ps ih =>
    simp only [idPfxsOf, List.map_cons, List.nodup_cons] at hnd
    rw [List.find?_cons]
    by_cases hq : q = id
    · subst hq; simp
    · have hid' : id ∈ ps := (List.mem_cons.1 hid).resolve_left (Ne.symm hq)
      have hne : idPfxOf (W16 (uint.Z q)) ≠ idPfxOf (W16 (uint.Z id)) := fun e =>
        hnd.1 (by rw [e]; exact List.mem_map_of_mem hid')
      simp only [hne, decide_false]
      exact ih hnd.2 hid'

theorem ΦsOf_at (ps : List w64) (idx : w64 → srvApi.KVSNames) (hnd : (idPfxsOf ps).Nodup)
    (id : w64) (hid : id ∈ ps) :
    ΦsOf (GF := GF) ps idx (idPfxOf (W16 (uint.Z id))) = srvFloorFacts (GF := GF) (idx id).slog := by
  unfold ΦsOf; rw [find_pfx ps hnd id hid]; rfl

theorem xsOf_at (ps : List w64) (idx : w64 → srvApi.KVSNames) (hnd : (idPfxsOf ps).Nodup)
    (id : w64) (hid : id ∈ ps) : xsOf ps idx (idPfxOf (W16 (uint.Z id))) = (idx id).slog := by
  unfold xsOf; rw [find_pfx ps hnd id hid]; rfl

/-- **What a member's ghost names agree on with the cluster's** (`allocN`'s per-member facts): its
server raft names the cluster's `γ` with its own registry, its KV names agreeing with the
cluster's KV names `γk`. -/
def memberGOk (γ : SrvRaft) (γk : KVNames) (g : MemberG GF) : Prop :=
  (∃ r, g.γ = { γ with reg := r }) ∧ g.ρ.rd.kv.st = γk.st ∧ g.ρ.rd.kv.c0 = γk.c0 ∧
    g.ρ.rd.kv.ch0 = γk.ch0 ∧ g.ρ.rd.kv.log0 = γk.log0 ∧ kvSame g.ρ.rd.kv γk

/-- **Every member's `memberBoot`, from the cluster's allocation** (probe C2, its ghost names
chosen): `memberBoot_of` folded over any list `L` of the members' ids. -/
theorem memberBoots_of (γ : SrvRaft) (ps : List w64) (ctxs : List (List w8))
    (issued cnt wn fs : GName) (γk : KVNames) (Φs : w64 → w64 → List w8 → GName → IProp GF)
    (γm : mvcc.api.MvccName) (idx : w64 → srvApi.KVSNames) (cok rev reg : w64 → GName)
    (xs : w64 → GName)
    (Hiss : γk.ids.issued = issued) (Hwn : γk.ids.wn = wn) (Hfs : γk.ids.fs = fs)
    (Hc0 : γk.c0 = W64 0)
    (Hch : γk.ch0 = apply.alarmChain false false false) (Hlog : γk.log0 = [[], []])
    (Hvs : γ.vs = ps) (cmp : Bool) (Hkc : γk.cmp = cmp)
    (lm : lease.Mode) (hrun : lease.runCfg (GF := GF) lm lm)
    (Hklg : γk.lm = lm) (hpo : kvPfxOk γk)
    -- (auth-lease S4, 2026-11-16) the cluster outside raft's no-snapshot mode
    (Hnsn : ¬ clusterNoSnap γ.cl) (L : List w64)
    (hpfx : ∀ id ∈ L, lm = .revocable → idPfxOf (W16 (uint.Z id)) ∈ γk.gps)
    (HΦ : ∀ id ∈ L, Φs (idPfxOf (W16 (uint.Z id))) = srvFloorFacts (GF := GF) (idx id).slog)
    (Hx : ∀ id ∈ L, xs (idPfxOf (W16 (uint.Z id))) = (idx id).slog) :
    ⊢ srvRaftLogInv (⟨γ, [], W64 0⟩ : ServerRaftNames) -∗
      idClusterInv issued cnt wn fs srvFloorFacts -∗ (W64 0) ↪[issued]□ (none : Option IdClaimV) -∗
      srvPropMint ⟨γ, [], W64 0⟩ γk.ids -∗ srvRdCtxInv ⟨γ, [], W64 0⟩ issued -∗
      kvInv ⟨γ, [], W64 0⟩ γk -∗
      ([∗list] id ∈ L, ((idPfxOf (W16 (uint.Z id)), 0) ↪[cnt] ((([] : List w64), (none : Option Loc)) : IdKeyEntry) ∗
          idKeyFactAt fs (idPfxOf (W16 (uint.Z id)), 0) (xs (idPfxOf (W16 (uint.Z id)))) ∗
          (nodeBoot γ.cl srvClusterN ps ctxs id ∗ raftState γ.cl id RaftState.init ∗
            nodeVacant γ.cl id) ∗
          ∃ γd : GName, ⌜γ.snapLoc id = some γd⌝ ∗ ghostMapAuth γd 1 (∅ : GMap w64 Unit))) -∗
      ([∗list] id ∈ L, idWaitTokAt wn (idPfxOf (W16 (uint.Z id)), 0)) -∗
      ([∗list] id ∈ L, srvApi.newServerStoreFreshA (GF := GF) (idx id) ∗
        ghostMapAuth (cok id) 1 (∅ : GMap w64 mvcc.Log) ∗
        ghostMapAuth (rev id) 1 (∅ : GMap w64 Unit) ∗
        ghostMapAuth (reg id) 1 (∅ : GMap Loc MemStorNamesRec)) ==∗
      ∃ gs : List (MemberG GF), ⌜gs.map (·.id) = L ∧ ∀ g ∈ gs, memberGOk γ γk g⌝ ∗
        [∗list] g ∈ gs, memberBoot g.γ ctxs g.ρ g.E Φs g.id cmp lm := by
  induction L with
  | nil =>
    iintro #_ #_ #_ #_ #_ #_ _ _ _
    imodintro
    iexists []
    isplitr
    · ipureintro; exact ⟨rfl, fun g h => by simp at h⟩
    iempintro
  | cons q L ih =>
    iintro #Hsrl #Hcl #H0 #Hpm #Hrc #Hkv Hms Hws Hns
    ihave Hms := BigSepL.bigSepL_cons.1 $$ Hms
    ihave Hws := BigSepL.bigSepL_cons.1 $$ Hws
    ihave Hns := BigSepL.bigSepL_cons.1 $$ Hns
    icases Hms with ⟨Hm, Hms⟩
    icases Hws with ⟨Hw, Hws⟩
    icases Hns with ⟨⟨Hi, Hc, Hr, Hg⟩, Hns⟩
    imod (memberBoot_of γ ps ctxs (reg q) issued cnt wn fs γk Φs q γm (idx q) (cok q) (rev q)
        (xs (idPfxOf (W16 (uint.Z q)))) (Hx q (by simp)) Hiss Hwn Hfs Hc0 Hch Hlog Hvs cmp Hkc lm
        hrun Hklg (hpfx q (by simp)) hpo (HΦ q (by simp)) Hnsn)
      $$ Hsrl Hcl H0 Hpm Hrc Hkv Hm Hw Hg Hi Hc Hr with ⟨%ρ, %Hρ, Hb⟩
    imod (ih (fun id h => hpfx id (List.mem_cons_of_mem _ h)) (fun id h => HΦ id (List.mem_cons_of_mem _ h))
        (fun id h => Hx id (List.mem_cons_of_mem _ h)))
      $$ Hsrl Hcl H0 Hpm Hrc Hkv Hms Hws Hns with ⟨%gs, %Hgs, Hbs⟩
    imodintro
    iexists ⟨q, { γ with reg := reg q }, ρ, env₀ γm (idx q) (rev q) (srvApi.kvNx ρ.rd false) cmp⟩ :: gs
    isplitr
    · ipureintro
      refine ⟨by simp [Hgs.1], fun g hg => ?_⟩
      rcases List.mem_cons.1 hg with rfl | hg
      · exact ⟨⟨reg q, rfl⟩, Hρ.1, Hρ.2.1, Hρ.2.2.1, Hρ.2.2.2.1, Hρ.2.2.2.2⟩
      · exact Hgs.2 g hg
    iapply BigSepL.bigSepL_cons.2
    iframe

/-- **A start bundle with a peer address, split at its HTTP protocol**: the unregistered protocol,
and the fresh bundle at any network once the protocol is the network's raft protocol. -/
theorem memberStartRes_split (n p : GoString) (c : Option GoString) :
    memberStartRes (GF := GF) n ⟨some p, c⟩ ⊢
      httpProtoFree p ∗ (∀ γn : NetNames GF,
        http.httpProtoOwn p (raftProto (netRh γn)) -∗ memberFreshRes n ⟨some p, c⟩ γn) := by
  simp only [memberStartRes, memberFreshRes]
  iintro ⟨#Hv, Hw, ⟨Ha, Hf⟩, Hc⟩
  iframe Hf
  iintro %γn Ho
  iframe; iframe #

/-- **What `Main` takes of the ghost state, for a cluster of any size** (see the file header):
`alloc3` for the members `ms` (each its name, its peer address and its optional client address),
whose ids are `ids` in the members' order, `id0` one of them. -/
theorem allocN (hne : mvcc.api.names_nonempty.law) (ids ps : List w64) (hperm : ps.Perm ids)
    (id0 : w64) (hid0 : id0 ∈ ids)
    (ctxs : List (List w8)) (boot : List LogEntry) (Hbc : BootCore ps ctxs boot)
    (dir : w64 → List GoString) (ms : List (GoString × GoString × Option GoString))
    (Hd0 : dir 0 = [])
    (Hhost : ∀ (i : w64) (h : GoString), go!"http://" ++ h ∈ dir i → h ∈ ms.map (·.2.1))
    (Hrb : receiptBound GF ≤ 2 ^ 64 - 2) (Hrb2 : receiptBound GF + boot.length ≤ 2 ^ 61)
    (lm : lease.Mode) (hrun : lease.runCfg (GF := GF) lm lm)
    (hap : lm = .revocable → leaseIdsApart ids)
    (cmp : Bool := false) (cret : Nat := 0) :
    ⊢ bootMarshal (GF := GF) ps ctxs (LogEntry.toEntries boot 0) -∗
      ([∗list] m ∈ ms, memberStartRes (GF := GF) m.1 ⟨some m.2.1, m.2.2⟩) ={⊤}=∗
      ∃ (γ : SrvRaft) (γk : KVNames) (Φs : w64 → w64 → List w8 → GName → IProp GF)
        (γn : NetNames GF) (gs : List (MemberG GF)),
      ⌜γ.vs = ps ∧ γ.rule = srvRule (W64 0) (LogEntry.toEntries boot 0) ∧
        γ.boot = LogEntry.toEntries boot 0 ∧ γn.N = srvNet γ ∧ γn.dir = dir ∧
        gs.map (·.id) = ids ∧ (∀ g ∈ gs, memberGOk γ γk g) ∧
        γk.c0 = W64 0 ∧ γk.ch0 = apply.alarmChain false false false ∧ γk.log0 = [[], []] ∧
        γk.cmp = cmp ∧ γk.cret = cret⌝ ∗
      (□ ∀ lid : w64, netHttpOk γn lid) ∗
      ([∗list] g ∈ gs, memberBoot g.γ ctxs g.ρ g.E Φs g.id cmp lm) ∗
      ([∗list] m ∈ ms, memberFreshRes m.1 ⟨some m.2.1, m.2.2⟩ γn) ∗
      (if decide (lm ≠ .none) then iprop(True) else
        etcdKV γk (kvModelSt γk (bootEntries (LogEntry.toEntries boot 0)))) := by
  obtain ⟨Hpnd, -, -⟩ := idPfxsOf_ok ps Hbc.lowNodup Hbc.lowNz
  have Hpsnd : ps.Nodup := by
    unfold idPfxsOf at Hpnd
    exact List.Pairwise.of_map _ (fun a b h e => h (by rw [e])) Hpnd
  have Hidnd : ids.Nodup := hperm.nodup_iff.1 Hpsnd
  have Hipnd : (idPfxsOf ids).Nodup := (hperm.map _).nodup_iff.1 Hpnd
  have Hpsne : ps ≠ [] := fun h => by rw [h] at hperm; exact absurd (hperm.symm.subset hid0) (by simp)
  have Hnz : W64 0 ∉ ps := fun h => Hbc.lowNz _ h (by decide)
  iintro #Hmarsh Hss
  -- each start bundle's HTTP protocol, apart
  ihave Hss := BigSepL.bigSepL_mono (fun {k m} _ => memberStartRes_split (GF := GF) m.1 m.2.1 m.2.2) $$ Hss
  ihave Hss := BigSepL.bigSepL_sep_eqv.1 $$ Hss
  icases Hss with ⟨Hfs, Hws⟩
  imod (newServerNames_allocL (GF := GF) ids Hidnd) with ⟨%idx, %cok, %rev, %reg, Hns⟩
  have γm : mvcc.api.MvccName := Classical.choice hne.1
  imod (srvClusterBoot_alloc (GF := GF) ps ctxs boot (xsOf ids idx) (reg id0) Hrb Hrb2 Hbc Hpsnd
      Hpsne Hnz cmp cret lm (idPfxOf (W16 (uint.Z id0))) (idPfxsOf ids)
      (gpsOk_of_apart lm ids id0 hid0 hap)) $$ Hmarsh
    with ⟨%γ, %issued, %cnt, %wn, %fs, %γk, %Hγ, %HnoSnap, #Hsrl, #Hkv, Hetcd, #Hcl, #H0, #Hpm, #Hrc, Hms,
      Hwns⟩
  obtain ⟨hvs, hrule, hboot, -, hc0, hch, hlog, hiss, -, hwn, hfs, hkc, hkr, hklg, hgp, hgps⟩ := Hγ
  have HnoSnap : ¬ clusterNoSnap γ.cl := fun h => Bool.false_ne_true (HnoSnap.1 h)
  have hpo : kvPfxOk γk := kvPfxOk_of_apart γk ids id0 hid0 hgp hgps (fun h => hap (hklg ▸ h))
  ihave Hms := (BigSepL.bigSepL_perm hperm).1 $$ Hms
  ihave Hwns := (BigSepL.bigSepL_perm hperm).1 $$ Hwns
  imod (memberBoots_of γ ps ctxs issued cnt wn fs γk (ΦsOf ids idx) γm idx cok rev reg (xsOf ids idx)
      hiss hwn hfs hc0 hch hlog hvs cmp hkc lm hrun hklg hpo HnoSnap ids
      (fun id hid _ => by rw [hgps]; exact idPfxOf_mem_idPfxsOf _ id hid)
      (fun id hid => ΦsOf_at ids idx Hipnd id hid) (fun id hid => xsOf_at ids idx Hipnd id hid))
    $$ Hsrl Hcl H0 Hpm Hrc Hkv Hms Hwns Hns with ⟨%gs, %Hgs, Hbs⟩
  -- the raft network, each peer address reserved for the raft protocol
  imod (netNames_alloc (srvNet γ) dir (∅ : GMap w64 Unit) ⊤) with ⟨%γn, %Hγn, -, #Hreg⟩
  have Hd0' : γn.dir 0 = [] := by rw [Hγn.2]; exact Hd0
  ihave Hfs : [∗list] a ∈ ms.map (·.2.1), httpProtoFree (GF := GF) a $$ [Hfs]
  · rw [BigSepL.bigSepL_map]; iexact Hfs
  imod (netHttp_reserveL γn (ms.map (·.2.1)) Hd0' (fun i h hm => Hhost i h (by rw [← Hγn.2]; exact hm)))
    $$ Hreg Hfs with ⟨#Hnet, Hos⟩
  rw [BigSepL.bigSepL_map] at *
  ihave Hfr := BigSepL.bigSepL_wand $$ Hos [Hws]
  · iapply BigSepL.bigSepL_mono (fun {k m} _ => forall_elim γn) $$ Hws
  imodintro
  iexists γ, γk, ΦsOf ids idx, γn, gs
  isimp only [KVNames.lg, hklg, hboot] at Hetcd
  iframe Hbs Hfr Hetcd
  isplitr
  · ipureintro
    exact ⟨hvs, hrule, hboot, Hγn.1, Hγn.2, Hgs.1, Hgs.2, hc0, hch, hlog, hkc, hkr⟩
  iexact Hnet

end alloc

end etcdstart
end EtcdGrove
end Perennial
