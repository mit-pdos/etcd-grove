/-
**The ghost state a three-member example with auth on allocates before its members** (the auth3
Scope's A1, `notes/auth3-scope.md`, 2026-11-14). Lean-first (no Rocq counterpart).

`alloc3On`: `alloc3`'s allocation (`Alloc3.lean`) with the mode-`on` cluster and members, as
authkv's `ak_alloc` does for one member: the cluster's resources once (`srvClusterBootOn_alloc`:
the mode-`on` KV invariant `kvInvOn` at the bootstrap log, the start chain with auth on, the
client's view of the auth history at the start), each member's names and share
(`srvMemberBootOn_alloc`, `memberBootOn_of`) at its own storage registry, the raft network with the
directory `dir`, its HTTP side ready for each member, and the client's `etcdKV` at the bootstrap
log's mode-`on` model at the first member's names. The
cluster's auth history is one (`KVNames.hist`): every member's KV names carry it, so the client's
view, at the first member's names, is every member's. Each member's own auth store, with its own
auth names, is built later by its `NewServer.specM true`.

No compactor (`cmp = false`) and no lease grants (`lm = .none`), as `NewServer.specM true` asks.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Alloc3
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.NewServerAllocOn
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

/-- The mode-`on` KV invariant does not read the storage registry's name (`kvInv_reg`'s). -/
theorem kvInvOn_reg (γ : SrvRaft) (r : GName) (γk : KVNames) :
    kvInvOn (GF := GF) (⟨γ, [], W64 0⟩ : ServerRaftNames) γk srvAuthSt0 ⊢
      kvInvOn ⟨{ γ with reg := r }, [], W64 0⟩ γk srvAuthSt0 := BI.entails_refl

/-- **`memberBootOn` from the allocations**, for one member (`memberBoot_of`'s, with auth on;
authkv's `ak_alloc`'s framing): at the cluster's names `γ` with the member's own storage registry
`reg`. -/
theorem memberBootOn_of (γ : SrvRaft) (ps : List w64) (ctxs : List (List w8)) (reg : GName)
    (issued cnt wn fs : GName) (γk : KVNames) (Φs : w64 → w64 → List w8 → GName → IProp GF)
    (id : w64) (γm : mvcc.api.MvccName) (γs : srvApi.KVSNames) (cok rev : GName) (x : GName)
    (Hx : x = γs.slog)
    (Hiss : γk.ids.issued = issued) (Hwn : γk.ids.wn = wn) (Hfs : γk.ids.fs = fs)
    (Hc0 : γk.c0 = W64 0)
    (Hch : γk.ch0 = apply.alarmChain true false false) (Hlog : γk.log0 = [[], []])
    (Hvs : γ.vs = ps) (Hkc : γk.cmp = false) (Hklg : γk.lg = false)
    (HΦ : Φs (idPfxOf (W16 (uint.Z id))) = srvFloorFacts (GF := GF) γs.slog) :
    ⊢ srvRaftLogInv (⟨γ, [], W64 0⟩ : ServerRaftNames) -∗
      idClusterInv issued cnt wn fs srvFloorFacts -∗ (W64 0) ↪[issued]□ (none : Option IdClaimV) -∗
      srvPropMint ⟨γ, [], W64 0⟩ γk.ids -∗ srvRdCtxInv ⟨γ, [], W64 0⟩ issued -∗
      kvInvOn ⟨γ, [], W64 0⟩ γk srvAuthSt0 -∗
      ((idPfxOf (W16 (uint.Z id)), 0) ↪[cnt] ((([] : List w64), (none : Option Loc)) : IdKeyEntry) ∗
        idKeyFactAt fs (idPfxOf (W16 (uint.Z id)), 0) x ∗
        (nodeBoot γ.cl srvClusterN ps ctxs id ∗ raftState γ.cl id RaftState.init ∗
          nodeVacant γ.cl id) ∗
        ∃ γd : GName, ⌜γ.snapLoc id = some γd⌝ ∗ ghostMapAuth γd 1 (∅ : GMap w64 Unit)) -∗
      idWaitTokAt wn (idPfxOf (W16 (uint.Z id)), 0) -∗
      ghostMapAuth reg 1 (∅ : GMap Loc MemStorNamesRec) -∗
      srvApi.newServerStoreFreshA γs -∗ ghostMapAuth cok 1 (∅ : GMap w64 mvcc.Log) -∗
      ghostMapAuth rev 1 (∅ : GMap w64 Unit) ==∗
      ∃ ρ : ReqNames, ⌜ρ.rd.kv.st = γk.st ∧ ρ.rd.kv.c0 = γk.c0 ∧ ρ.rd.kv.ch0 = γk.ch0 ∧
        ρ.rd.kv.log0 = γk.log0 ∧ ρ.rd.kv.hist = γk.hist⌝ ∗
        memberBootOn { γ with reg := reg } ctxs ρ (env₀ γm γs rev (srvApi.kvNx ρ.rd true)) Φs id := by
  subst Hx
  have hlm : γk.lm = .none := by simpa [KVNames.lg_eq] using Hklg
  iintro #Hsrl #Hcl #H0 #Hpm #Hrc #Hkv ⟨Hp, #Hkf, Hnb, Hsd⟩ Hwt0 Hreg Hidx Hcok Hrev
  ihave #Hkv' := kvInvOn_reg γ reg γk $$ Hkv
  imod (srvMemberBootOn_alloc (GF := GF) { γ with reg := reg } cnt γk id cok) $$ Hkv' Hp [Hwt0]
    with ⟨%ρ, %Hρ, #Hkvρ, Hsh, Hnk, Hwt⟩
  · rw [Hwn]; iexact Hwt0
  obtain ⟨hraft, hst, hc0', hch', hlog', hcok, hiss', hcnt, hpfx, hhist, hkc', hklg', hwn', hfs', hinc'⟩ := Hρ
  ihave #Hkf' : idKeyFactAt ρ.ids.fs ρ.ids.key γs.slog $$ []
  · simp only [IdNames.key]; rw [hpfx, hinc', hfs', Hfs]; iexact Hkf
  ihave #Hcl' : idClusterInv ρ.ids.issued ρ.ids.cnt ρ.ids.wn ρ.ids.fs srvFloorFacts $$ []
  · rw [hiss', hcnt, hwn', hfs', Hiss, Hwn, Hfs]; iexact Hcl
  imodintro
  iexists ρ
  isplitr
  · ipureintro
    exact ⟨hst, hc0', hch', hlog', hhist⟩
  iunfold memberBootOn
  simp only [env₀]
  rw [hiss', hcnt, hraft, Hiss]
  rw [← srvPropMint_congr _ γk.ids ρ.ids (by rw [hiss', Hiss])]
  ihave #Hsrl' := srvRaftLogInv_reg γ reg $$ Hsrl
  ihave #Hpm' := srvPropMint_reg γ reg γk.ids $$ Hpm
  ihave #Hrc' := srvRdCtxInv_reg γ reg issued $$ Hrc
  ihave Hnb' : nodeBoot γ.cl srvClusterN γ.vs ctxs id ∗ raftState γ.cl id RaftState.init ∗
      nodeVacant γ.cl id $$ [Hnb]
  · rw [Hvs]; iexact Hnb
  rw [hcok]
  iframe Hnb' Hsrl' Hcl' Hkf' Hpm' Hrc' Hsh Hidx Hcok Hrev Hnk Hkvρ Hwt Hsd Hreg
  isplitr
  · ipureintro
    exact ⟨rfl, by rw [hc0', Hc0], by rw [hch', Hch], by rw [hlog', Hlog],
      hpfx, by rw [hpfx]; exact HΦ, trivial, by rw [hkc', Hkc], trivial,
      ⟨.none, by rw [hklg', hlm]; exact lease.runCfg_none (GF := GF)⟩,
      by rw [KVNames.lg_eq, hklg', hlm]; rfl⟩
  iunfold idNoZero
  rw [hiss', Hiss]
  iexact H0

/-- **The cluster's ghost state with auth on, from the peers' unregistered HTTP protocols**
(`alloc3Http`'s, with the mode-`on` allocators). -/
private theorem alloc3OnHttp (hne : mvcc.api.names_nonempty.law) (id₁ id₂ id₃ : w64) (ps : List w64)
    (hperm : ps.Perm [id₁, id₂, id₃])
    (ctxs : List (List w8)) (boot : List LogEntry)
    (Hbc : BootCore ps ctxs boot)
    (dir : w64 → List GoString)
    (a₁ a₂ a₃ : GoString) (Hd0 : dir 0 = [])
    (Hhost : ∀ (i : w64) (h : GoString), go!"http://" ++ h ∈ dir i → h = a₁ ∨ h = a₂ ∨ h = a₃)
    (Hrb : receiptBound GF ≤ 2 ^ 64 - 2) (Hrb2 : receiptBound GF + boot.length ≤ 2 ^ 61) :
    ⊢ bootMarshal (GF := GF) ps ctxs (LogEntry.toEntries boot 0) -∗
      httpProtoFree (GF := GF) a₁ -∗ httpProtoFree (GF := GF) a₂ -∗ httpProtoFree (GF := GF) a₃ ={⊤}=∗
      ∃ (γ : SrvRaft) (reg₁ reg₂ reg₃ : GName) (ρ₁ ρ₂ ρ₃ : ReqNames)
        (E₁ E₂ E₃ : apply.AEnv GF) (Φs : w64 → w64 → List w8 → GName → IProp GF)
        (γn : NetNames GF),
      ⌜γ.vs = ps ∧ γ.rule = srvRule (W64 0) (LogEntry.toEntries boot 0) ∧
        γ.boot = LogEntry.toEntries boot 0 ∧
        γn.N = srvNet γ ∧ γn.dir = dir ∧ ρ₁.rd.kv.c0 = W64 0 ∧ ρ₁.rd.kv.log0 = [[], []]⌝ ∗
      memberBootOn { γ with reg := reg₁ } ctxs ρ₁ E₁ Φs id₁ ∗
      (netHttpOk γn id₁ ∗ http.httpProtoOwn a₁ (raftProto (netRh γn))) ∗
      memberBootOn { γ with reg := reg₂ } ctxs ρ₂ E₂ Φs id₂ ∗
      (netHttpOk γn id₂ ∗ http.httpProtoOwn a₂ (raftProto (netRh γn))) ∗
      memberBootOn { γ with reg := reg₃ } ctxs ρ₃ E₃ Φs id₃ ∗
      (netHttpOk γn id₃ ∗ http.httpProtoOwn a₃ (raftProto (netRh γn))) ∗
      etcdKV ρ₁.rd.kv (kvStateOf (kvModelOn ρ₁.rd.kv srvAuthSt0
        (bootEntries (LogEntry.toEntries boot 0)))) ∗
      authHistView ρ₁.rd.kv [srvAuthSt0] := by
  have Hlow : ([id₁, id₂, id₃].map (fun id => uint.Z id % 2 ^ 16)).Nodup :=
    (hperm.map _).nodup_iff.1 Hbc.lowNodup
  have Hlow0 : ∀ id ∈ [id₁, id₂, id₃], uint.Z id % 2 ^ 16 ≠ 0 :=
    fun id hid => Hbc.lowNz id (hperm.mem_iff.2 hid)
  obtain ⟨hn12, hn13, hn23⟩ := id_ne id₁ id₂ id₃ Hlow Hlow0
  obtain ⟨hp12, hp13, hp23⟩ := pfx_ne id₁ id₂ id₃ Hlow Hlow0
  have Hnz := id_nz id₁ id₂ id₃ Hlow Hlow0
  iintro #Hmarsh Hf₁ Hf₂ Hf₃
  imod newServerNames_alloc (GF := GF) with ⟨%idx₁, %cok₁, %rev₁, Hidx₁, Hcok₁, Hrev₁⟩
  imod newServerNames_alloc (GF := GF) with ⟨%idx₂, %cok₂, %rev₂, Hidx₂, Hcok₂, Hrev₂⟩
  imod newServerNames_alloc (GF := GF) with ⟨%idx₃, %cok₃, %rev₃, Hidx₃, Hcok₃, Hrev₃⟩
  have γm : mvcc.api.MvccName := Classical.choice hne.1
  imod ghost_map_alloc_empty (GF := GF) (K := Loc) (V := MemStorNamesRec) with ⟨%reg₁, Hreg₁⟩
  imod ghost_map_alloc_empty (GF := GF) (K := Loc) (V := MemStorNamesRec) with ⟨%reg₂, Hreg₂⟩
  imod ghost_map_alloc_empty (GF := GF) (K := Loc) (V := MemStorNamesRec) with ⟨%reg₃, Hreg₃⟩
  let Φs : w64 → w64 → List w8 → GName → IProp GF := fun p =>
    if p = idPfxOf (W16 (uint.Z id₁)) then srvFloorFacts idx₁.slog
    else if p = idPfxOf (W16 (uint.Z id₂)) then srvFloorFacts idx₂.slog
    else srvFloorFacts idx₃.slog
  have HΦ₁ : Φs (idPfxOf (W16 (uint.Z id₁))) = srvFloorFacts (GF := GF) idx₁.slog := by
    simp only [Φs, if_true]
  have HΦ₂ : Φs (idPfxOf (W16 (uint.Z id₂))) = srvFloorFacts (GF := GF) idx₂.slog := by
    simp only [Φs, Ne.symm hp12, if_false, if_true]
  have HΦ₃ : Φs (idPfxOf (W16 (uint.Z id₃))) = srvFloorFacts (GF := GF) idx₃.slog := by
    simp only [Φs, Ne.symm hp13, Ne.symm hp23, if_false]
  let xs : w64 → GName := fun p =>
    if p = idPfxOf (W16 (uint.Z id₁)) then idx₁.slog
    else if p = idPfxOf (W16 (uint.Z id₂)) then idx₂.slog else idx₃.slog
  have Hx₁ : xs (idPfxOf (W16 (uint.Z id₁))) = idx₁.slog := by simp only [xs, if_true]
  have Hx₂ : xs (idPfxOf (W16 (uint.Z id₂))) = idx₂.slog := by
    simp only [xs, Ne.symm hp12, if_false, if_true]
  have Hx₃ : xs (idPfxOf (W16 (uint.Z id₃))) = idx₃.slog := by
    simp only [xs, Ne.symm hp13, Ne.symm hp23, if_false]
  imod (srvClusterBootOn_alloc (GF := GF) ps ctxs boot xs reg₁ Hrb Hrb2 Hbc
      (hperm.nodup_iff.2 (by simp [hn12, hn13, hn23]))
      (fun h => by rw [h] at hperm; exact absurd hperm.length_eq (by simp))
      (fun h => Hnz _ (hperm.subset h) rfl)) $$ Hmarsh
    with ⟨%γ, %issued, %cnt, %wn, %fs, %γk, %Hγ, #Hsrl, #Hkv, Hetcd, Hview, #Hcl, #H0, #Hpm, #Hrc,
      Hms, Hwns⟩
  obtain ⟨hvs, hrule, hboot, hreg, hc0, hch, hlog, hiss, -, hwn, hfs, hkc, hklg⟩ := Hγ
  ihave Hms' := (BigSepL.bigSepL_perm hperm).1 $$ Hms
  ihave Hwns' := (BigSepL.bigSepL_perm hperm).1 $$ Hwns
  icases Hms' with ⟨Hm₁, Hm₂, Hm₃, -⟩
  icases Hwns' with ⟨Hw₁, Hw₂, Hw₃, -⟩
  imod (memberBootOn_of γ ps ctxs reg₁ issued cnt wn fs γk Φs id₁ γm idx₁ cok₁ rev₁
      (xs (idPfxOf (W16 (uint.Z id₁)))) Hx₁ hiss hwn hfs hc0 hch hlog hvs hkc hklg HΦ₁)
      $$ Hsrl Hcl H0 Hpm Hrc Hkv Hm₁ Hw₁ Hreg₁ Hidx₁ Hcok₁ Hrev₁
    with ⟨%ρ₁, %Hρ₁, Hb₁⟩
  imod (memberBootOn_of γ ps ctxs reg₂ issued cnt wn fs γk Φs id₂ γm idx₂ cok₂ rev₂
      (xs (idPfxOf (W16 (uint.Z id₂)))) Hx₂ hiss hwn hfs hc0 hch hlog hvs hkc hklg HΦ₂)
      $$ Hsrl Hcl H0 Hpm Hrc Hkv Hm₂ Hw₂ Hreg₂ Hidx₂ Hcok₂ Hrev₂
    with ⟨%ρ₂, -, Hb₂⟩
  imod (memberBootOn_of γ ps ctxs reg₃ issued cnt wn fs γk Φs id₃ γm idx₃ cok₃ rev₃
      (xs (idPfxOf (W16 (uint.Z id₃)))) Hx₃ hiss hwn hfs hc0 hch hlog hvs hkc hklg HΦ₃)
      $$ Hsrl Hcl H0 Hpm Hrc Hkv Hm₃ Hw₃ Hreg₃ Hidx₃ Hcok₃ Hrev₃
    with ⟨%ρ₃, -, Hb₃⟩
  imod (netNames_alloc (srvNet γ) dir (∅ : GMap w64 Unit) ⊤) with ⟨%γn, %Hγn, -, #Hreg⟩
  have Hd0' : γn.dir 0 = [] := by rw [Hγn.2]; exact Hd0
  imod (netHttp_reserve3 γn a₁ a₂ a₃ Hd0' (fun i h hm => Hhost i h (by rw [← Hγn.2]; exact hm)))
    $$ Hreg Hf₁ Hf₂ Hf₃ with ⟨#Hnet, Ho₁, Ho₂, Ho₃⟩
  ihave #Hs₁ := Hnet $$ %id₁
  ihave #Hs₂ := Hnet $$ %id₂
  ihave #Hs₃ := Hnet $$ %id₃
  obtain ⟨hst₁, hc0₁, hch₁, hlog₁, hhist₁⟩ := Hρ₁
  imodintro
  iexists γ, reg₁, reg₂, reg₃, ρ₁, ρ₂, ρ₃,
    env₀ γm idx₁ rev₁ (srvApi.kvNx ρ₁.rd true), env₀ γm idx₂ rev₂ (srvApi.kvNx ρ₂.rd true),
    env₀ γm idx₃ rev₃ (srvApi.kvNx ρ₃.rd true), Φs, γn
  iframe Hb₁ Hb₂ Hb₃ Hs₁ Hs₂ Hs₃ Ho₁ Ho₂ Ho₃
  isplitr
  · ipureintro
    exact ⟨hvs, hrule, hboot, Hγn.1, Hγn.2, by rw [hc0₁, hc0], by rw [hlog₁, hlog]⟩
  rw [← hboot]
  rw [etcdKV_congr ρ₁.rd.kv γk hst₁,
    show kvModelOn ρ₁.rd.kv srvAuthSt0 (bootEntries γ.boot) = kvModelOn γk srvAuthSt0 (bootEntries γ.boot) by
      unfold kvModelOn; rw [hc0₁, hch₁, hlog₁]]
  iframe Hetcd
  unfold authHistView
  rw [hhist₁]
  iexact Hview

/-- **What a three-member `Main` with auth on takes of the ghost state, for its cluster**
(`alloc3`'s, with auth on): `alloc3OnHttp` on the members' start bundles, each member's start bundle
becoming its fresh bundle at the network `γn`. -/
theorem alloc3On (hne : mvcc.api.names_nonempty.law) (id₁ id₂ id₃ : w64) (ps : List w64)
    (hperm : ps.Perm [id₁, id₂, id₃])
    (ctxs : List (List w8)) (boot : List LogEntry)
    (Hbc : BootCore ps ctxs boot)
    (dir : w64 → List GoString)
    (a₁ a₂ a₃ : GoString) (Hd0 : dir 0 = [])
    (Hhost : ∀ (i : w64) (h : GoString), go!"http://" ++ h ∈ dir i → h = a₁ ∨ h = a₂ ∨ h = a₃)
    (Hrb : receiptBound GF ≤ 2 ^ 64 - 2) (Hrb2 : receiptBound GF + boot.length ≤ 2 ^ 61)
    (n₁ n₂ n₃ : GoString) (c₁ c₂ c₃ : Option GoString) :
    ⊢ bootMarshal (GF := GF) ps ctxs (LogEntry.toEntries boot 0) -∗
      memberStartRes (GF := GF) n₁ ⟨some a₁, c₁⟩ -∗ memberStartRes (GF := GF) n₂ ⟨some a₂, c₂⟩ -∗
      memberStartRes (GF := GF) n₃ ⟨some a₃, c₃⟩ ={⊤}=∗
      ∃ (γ : SrvRaft) (reg₁ reg₂ reg₃ : GName) (ρ₁ ρ₂ ρ₃ : ReqNames)
        (E₁ E₂ E₃ : apply.AEnv GF) (Φs : w64 → w64 → List w8 → GName → IProp GF)
        (γn : NetNames GF),
      ⌜γ.vs = ps ∧ γ.rule = srvRule (W64 0) (LogEntry.toEntries boot 0) ∧
        γ.boot = LogEntry.toEntries boot 0 ∧
        γn.N = srvNet γ ∧ γn.dir = dir ∧ ρ₁.rd.kv.c0 = W64 0 ∧ ρ₁.rd.kv.log0 = [[], []]⌝ ∗
      memberBootOn { γ with reg := reg₁ } ctxs ρ₁ E₁ Φs id₁ ∗
      (netHttpOk γn id₁ ∗ memberFreshRes n₁ ⟨some a₁, c₁⟩ γn) ∗
      memberBootOn { γ with reg := reg₂ } ctxs ρ₂ E₂ Φs id₂ ∗
      (netHttpOk γn id₂ ∗ memberFreshRes n₂ ⟨some a₂, c₂⟩ γn) ∗
      memberBootOn { γ with reg := reg₃ } ctxs ρ₃ E₃ Φs id₃ ∗
      (netHttpOk γn id₃ ∗ memberFreshRes n₃ ⟨some a₃, c₃⟩ γn) ∗
      etcdKV ρ₁.rd.kv (kvStateOf (kvModelOn ρ₁.rd.kv srvAuthSt0
        (bootEntries (LogEntry.toEntries boot 0)))) ∗
      authHistView ρ₁.rd.kv [srvAuthSt0] := by
  simp only [memberStartRes, memberFreshRes]
  iintro #Hmarsh ⟨#Hv₁, Hw₁, ⟨Ha₁, Hf₁⟩, Hc₁⟩ ⟨#Hv₂, Hw₂, ⟨Ha₂, Hf₂⟩, Hc₂⟩ ⟨#Hv₃, Hw₃, ⟨Ha₃, Hf₃⟩, Hc₃⟩
  imod (alloc3OnHttp hne id₁ id₂ id₃ ps hperm ctxs boot Hbc dir a₁ a₂ a₃ Hd0 Hhost Hrb Hrb2)
      $$ Hmarsh Hf₁ Hf₂ Hf₃
    with ⟨%γ, %reg₁, %reg₂, %reg₃, %ρ₁, %ρ₂, %ρ₃, %E₁, %E₂, %E₃, %Φs, %γn, %Hγ, Hb₁, ⟨Hn₁, Ho₁⟩,
      Hb₂, ⟨Hn₂, Ho₂⟩, Hb₃, ⟨Hn₃, Ho₃⟩, Hetcd, Hview⟩
  imodintro
  iexists γ, reg₁, reg₂, reg₃, ρ₁, ρ₂, ρ₃, E₁, E₂, E₃, Φs, γn
  iframe; iframe #
  ipureintro; exact Hγ

end alloc

end etcdstart
end EtcdGrove
end Perennial
