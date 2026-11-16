/-
**The cluster's ghost state with auth on, for a cluster of any size** (authN, 2026-11-15): `allocN`
(`AllocN.lean`) with the mode-`on` allocators (`alloc3On`'s: `srvClusterBootOn_alloc`,
`memberBootOn_of`), and every member's names of one cluster (`sameCluster` with the head member's).
Lean-first (no Rocq counterpart).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.AllocN
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Alloc3On

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

/-- A member's names at the cluster's, with auth on (`memberGOk`'s, and the auth history's and the
raft names' fields, what `sameCluster` reads). -/
def memberGOkOn (γ : SrvRaft) (γk : KVNames) (g : MemberG GF) : Prop :=
  ∃ r, g.γ = { γ with reg := r } ∧ g.ρ.rd.raft = ⟨{ γ with reg := r }, [], W64 0⟩ ∧
    g.ρ.rd.kv.st = γk.st ∧ g.ρ.rd.kv.c0 = γk.c0 ∧ g.ρ.rd.kv.ch0 = γk.ch0 ∧
    g.ρ.rd.kv.log0 = γk.log0 ∧ g.ρ.rd.kv.hist = γk.hist

theorem sameCluster_of_gOkOn (γ : SrvRaft) (γk : KVNames) (g g' : MemberG GF)
    (h : memberGOkOn γ γk g) (h' : memberGOkOn γ γk g') : sameCluster g.ρ g'.ρ := by
  obtain ⟨r, -, hr, h1, h2, h3, h4, h5⟩ := h
  obtain ⟨r', -, hr', h1', h2', h3', h4', h5'⟩ := h'
  refine ⟨by rw [h1, h1'], by rw [h2, h2'], by rw [h3, h3'], by rw [h4, h4'], by rw [h5, h5'],
    ?_, ?_, ?_, ?_⟩ <;> rw [hr, hr']

/-- **Every member's `memberBootOn`, from the cluster's allocation with auth on**: `memberBoots_of`
with `memberBootOn_ofM`, at the lease mode `lm` (auth-lease S4, 2026-11-16). -/
theorem memberBootsOn_ofM (γ : SrvRaft) (ps : List w64) (ctxs : List (List w8))
    (issued cnt wn fs : GName) (γk : KVNames) (Φs : w64 → w64 → List w8 → GName → IProp GF)
    (γm : mvcc.api.MvccName) (idx : w64 → srvApi.KVSNames) (cok rev reg : w64 → GName)
    (xs : w64 → GName)
    (Hiss : γk.ids.issued = issued) (Hwn : γk.ids.wn = wn) (Hfs : γk.ids.fs = fs)
    (Hc0 : γk.c0 = W64 0)
    (Hch : γk.ch0 = apply.alarmChain true false false) (Hlog : γk.log0 = [[], []])
    (Hvs : γ.vs = ps) (Hkc : γk.cmp = false)
    (lm : lease.Mode) (hrun : lease.runCfg (GF := GF) lm lm)
    (hne : lm = .revocable → lease.leasesNoExpiry) (Hklm : γk.lm = lm) (hpo : kvPfxOk γk)
    (L : List w64) (hpfx : ∀ id ∈ L, lm = .revocable → idPfxOf (W16 (uint.Z id)) ∈ γk.gps)
    (HΦ : ∀ id ∈ L, Φs (idPfxOf (W16 (uint.Z id))) = srvFloorFacts (GF := GF) (idx id).slog)
    (Hx : ∀ id ∈ L, xs (idPfxOf (W16 (uint.Z id))) = (idx id).slog) :
    ⊢ srvRaftLogInv (⟨γ, [], W64 0⟩ : ServerRaftNames) -∗
      idClusterInv issued cnt wn fs srvFloorFacts -∗ (W64 0) ↪[issued]□ (none : Option IdClaimV) -∗
      srvPropMint ⟨γ, [], W64 0⟩ γk.ids -∗ srvRdCtxInv ⟨γ, [], W64 0⟩ issued -∗
      kvInvOn ⟨γ, [], W64 0⟩ γk srvAuthSt0 -∗
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
      ∃ gs : List (MemberG GF), ⌜gs.map (·.id) = L ∧ ∀ g ∈ gs, memberGOkOn γ γk g⌝ ∗
        [∗list] g ∈ gs, memberBootOn g.γ ctxs g.ρ g.E Φs g.id false lm := by
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
    imod (memberBootOn_ofM γ ps ctxs (reg q) issued cnt wn fs γk Φs q γm (idx q) (cok q) (rev q)
        (xs (idPfxOf (W16 (uint.Z q)))) (Hx q (by simp)) Hiss Hwn Hfs Hc0 Hch Hlog Hvs Hkc
        lm hrun hne Hklm (hpfx q (by simp)) hpo (HΦ q (by simp)))
      $$ Hsrl Hcl H0 Hpm Hrc Hkv Hm Hw Hg Hi Hc Hr with ⟨%ρ, %Hρ, Hb⟩
    imod (ih (fun id h => hpfx id (List.mem_cons_of_mem _ h))
        (fun id h => HΦ id (List.mem_cons_of_mem _ h))
        (fun id h => Hx id (List.mem_cons_of_mem _ h)))
      $$ Hsrl Hcl H0 Hpm Hrc Hkv Hms Hws Hns with ⟨%gs, %Hgs, Hbs⟩
    imodintro
    iexists ⟨q, { γ with reg := reg q }, ρ, env₀ γm (idx q) (rev q) (srvApi.kvNx ρ.rd true)⟩ :: gs
    isplitr
    · ipureintro
      refine ⟨by simp [Hgs.1], fun g hg => ?_⟩
      rcases List.mem_cons.1 hg with rfl | hg
      · obtain ⟨h1, h2, h3, h4, h5, h6⟩ := Hρ
        exact ⟨reg q, rfl, h6, h1, h2, h3, h4, h5⟩
      · exact Hgs.2 g hg
    iapply BigSepL.bigSepL_cons.2
    iframe

/-- **What `Main` takes of the ghost state with auth on, for a cluster of any size**: `allocN`'s with
the mode-`on` allocators (`alloc3On`'s), for the members `ms` whose ids are `ids` in the members'
order, `id0` one of them: every member's `memberBootOn` at names of one cluster (`memberGOkOn`), the
head KV names' store at the boot state and the auth history's view; (auth-lease S4, 2026-11-16) at the
lease mode `lm`, in the revocable mode with the members' ids apart (`leaseIdsApart`) and no lease
expiring. -/
theorem allocNOnM (hne : mvcc.api.names_nonempty.law) (ids ps : List w64) (hperm : ps.Perm ids)
    (id0 : w64) (hid0 : id0 ∈ ids)
    (ctxs : List (List w8)) (boot : List LogEntry) (Hbc : BootCore ps ctxs boot)
    (dir : w64 → List GoString) (ms : List (GoString × GoString × Option GoString))
    (Hd0 : dir 0 = [])
    (Hhost : ∀ (i : w64) (h : GoString), go!"http://" ++ h ∈ dir i → h ∈ ms.map (·.2.1))
    (Hrb : receiptBound GF ≤ 2 ^ 64 - 2) (Hrb2 : receiptBound GF + boot.length ≤ 2 ^ 61)
    (lm : lease.Mode) (hrun : lease.runCfg (GF := GF) lm lm)
    (hnx : lm = .revocable → lease.leasesNoExpiry) (hap : lm = .revocable → leaseIdsApart ids) :
    ⊢ bootMarshal (GF := GF) ps ctxs (LogEntry.toEntries boot 0) -∗
      ([∗list] m ∈ ms, memberStartRes (GF := GF) m.1 ⟨some m.2.1, m.2.2⟩) ={⊤}=∗
      ∃ (γ : SrvRaft) (γk : KVNames) (Φs : w64 → w64 → List w8 → GName → IProp GF)
        (γn : NetNames GF) (gs : List (MemberG GF)),
      ⌜γ.vs = ps ∧ γ.rule = srvRule (W64 0) (LogEntry.toEntries boot 0) ∧
        γ.boot = LogEntry.toEntries boot 0 ∧ γn.N = srvNet γ ∧ γn.dir = dir ∧
        gs.map (·.id) = ids ∧ (∀ g ∈ gs, memberGOkOn γ γk g) ∧
        γk.c0 = W64 0 ∧ γk.log0 = [[], []]⌝ ∗
      (□ ∀ lid : w64, netHttpOk γn lid) ∗
      ([∗list] g ∈ gs, memberBootOn g.γ ctxs g.ρ g.E Φs g.id false lm) ∗
      ([∗list] m ∈ ms, memberFreshRes m.1 ⟨some m.2.1, m.2.2⟩ γn) ∗
      etcdKV γk (kvStateOf (kvModelOn γk srvAuthSt0 (bootEntries (LogEntry.toEntries boot 0)))) ∗
      authHistView γk [srvAuthSt0] := by
  obtain ⟨Hpnd, -, -⟩ := idPfxsOf_ok ps Hbc.lowNodup Hbc.lowNz
  have Hpsnd : ps.Nodup := by
    unfold idPfxsOf at Hpnd
    exact List.Pairwise.of_map _ (fun a b h e => h (by rw [e])) Hpnd
  have Hidnd : ids.Nodup := hperm.nodup_iff.1 Hpsnd
  have Hipnd : (idPfxsOf ids).Nodup := (hperm.map _).nodup_iff.1 Hpnd
  have Hpsne : ps ≠ [] := fun h => by rw [h] at hperm; exact absurd (hperm.symm.subset hid0) (by simp)
  have Hnz : W64 0 ∉ ps := fun h => Hbc.lowNz _ h (by decide)
  iintro #Hmarsh Hss
  ihave Hss := BigSepL.bigSepL_mono (fun {k m} _ => memberStartRes_split (GF := GF) m.1 m.2.1 m.2.2) $$ Hss
  ihave Hss := BigSepL.bigSepL_sep_eqv.1 $$ Hss
  icases Hss with ⟨Hfs, Hws⟩
  imod (newServerNames_allocL (GF := GF) ids Hidnd) with ⟨%idx, %cok, %rev, %reg, Hns⟩
  have γm : mvcc.api.MvccName := Classical.choice hne.1
  imod (srvClusterBootOn_alloc (GF := GF) ps ctxs boot (xsOf ids idx) (reg id0) Hrb Hrb2 Hbc Hpsnd
      Hpsne Hnz lm (idPfxOf (W16 (uint.Z id0))) (idPfxsOf ids)
      (gpsOk_of_apart lm ids id0 hid0 hap)) $$ Hmarsh
    with ⟨%γ, %issued, %cnt, %wn, %fs, %γk, %Hγ, #Hsrl, #Hkv, Hetcd, Hview, #Hcl, #H0, #Hpm, #Hrc,
      Hms, Hwns⟩
  obtain ⟨hvs, hrule, hboot, -, hc0, hch, hlog, hiss, -, hwn, hfs, hkc, hklm, hgp, hgps⟩ := Hγ
  have hpo : kvPfxOk γk := kvPfxOk_of_apart γk ids id0 hid0 hgp hgps (fun h => hap (hklm ▸ h))
  ihave Hms := (BigSepL.bigSepL_perm hperm).1 $$ Hms
  ihave Hwns := (BigSepL.bigSepL_perm hperm).1 $$ Hwns
  imod (memberBootsOn_ofM γ ps ctxs issued cnt wn fs γk (ΦsOf ids idx) γm idx cok rev reg (xsOf ids idx)
      hiss hwn hfs hc0 hch hlog hvs hkc lm hrun hnx hklm hpo ids
      (fun id hid _ => by rw [hgps]; exact idPfxOf_mem_idPfxsOf _ id hid)
      (fun id hid => ΦsOf_at ids idx Hipnd id hid) (fun id hid => xsOf_at ids idx Hipnd id hid))
    $$ Hsrl Hcl H0 Hpm Hrc Hkv Hms Hwns Hns with ⟨%gs, %Hgs, Hbs⟩
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
  rw [← hboot]
  iframe Hbs Hfr Hetcd Hview
  isplitr
  · ipureintro
    exact ⟨hvs, by rw [hboot]; exact hrule, rfl, Hγn.1, Hγn.2, Hgs.1, Hgs.2, hc0, hlog⟩
  iexact Hnet



/-- **What `Main` takes of the ghost state with auth on, for a cluster of any size**, at the lease mode
`none` (`allocNOnM`'s). -/
theorem allocNOn (hne : mvcc.api.names_nonempty.law) (ids ps : List w64) (hperm : ps.Perm ids)
    (id0 : w64) (hid0 : id0 ∈ ids)
    (ctxs : List (List w8)) (boot : List LogEntry) (Hbc : BootCore ps ctxs boot)
    (dir : w64 → List GoString) (ms : List (GoString × GoString × Option GoString))
    (Hd0 : dir 0 = [])
    (Hhost : ∀ (i : w64) (h : GoString), go!"http://" ++ h ∈ dir i → h ∈ ms.map (·.2.1))
    (Hrb : receiptBound GF ≤ 2 ^ 64 - 2) (Hrb2 : receiptBound GF + boot.length ≤ 2 ^ 61) :
    ⊢ bootMarshal (GF := GF) ps ctxs (LogEntry.toEntries boot 0) -∗
      ([∗list] m ∈ ms, memberStartRes (GF := GF) m.1 ⟨some m.2.1, m.2.2⟩) ={⊤}=∗
      ∃ (γ : SrvRaft) (γk : KVNames) (Φs : w64 → w64 → List w8 → GName → IProp GF)
        (γn : NetNames GF) (gs : List (MemberG GF)),
      ⌜γ.vs = ps ∧ γ.rule = srvRule (W64 0) (LogEntry.toEntries boot 0) ∧
        γ.boot = LogEntry.toEntries boot 0 ∧ γn.N = srvNet γ ∧ γn.dir = dir ∧
        gs.map (·.id) = ids ∧ (∀ g ∈ gs, memberGOkOn γ γk g) ∧
        γk.c0 = W64 0 ∧ γk.log0 = [[], []]⌝ ∗
      (□ ∀ lid : w64, netHttpOk γn lid) ∗
      ([∗list] g ∈ gs, memberBootOn g.γ ctxs g.ρ g.E Φs g.id) ∗
      ([∗list] m ∈ ms, memberFreshRes m.1 ⟨some m.2.1, m.2.2⟩ γn) ∗
      etcdKV γk (kvStateOf (kvModelOn γk srvAuthSt0 (bootEntries (LogEntry.toEntries boot 0)))) ∗
      authHistView γk [srvAuthSt0] :=
  allocNOnM hne ids ps hperm id0 hid0 ctxs boot Hbc dir ms Hd0 Hhost Hrb Hrb2 .none lease.runCfg_none
    (fun h => nomatch h) (fun h => nomatch h)

end alloc

end etcdstart
end EtcdGrove
end Perennial
