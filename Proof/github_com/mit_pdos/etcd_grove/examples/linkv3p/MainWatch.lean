/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/linkv3p/MainWatch.lean` (W4d of
`notes/watch-cut-plan.md`, 2026-10-22). Lean-first (no Rocq counterpart).

`genAll` picks the writers' puts `trs` first. The cluster is `startCluster`'s with the watch
prefix `wk/`. The client's half of etcd's KV state goes into the clients' adapter (`kmInv γ`,
D48), whose application property is the plan's (`γ.W = wkW P`: every revision from `2` one put of
the puts picked; D45, 2026-10-26: until then watchkv's server workload). Each member's watch facts
(`memberWatch`) and its `Watch` stream at its bridge (`isGrpcStream_forwards`) give the watcher's
facts at the first client's connection (`watchEnv_conn`, `isNewClient_watcher_of`), a watcher of
the cluster's KV (`isKvWatcher`), so etcd's watch contract at the adapter's model
(`isEtcdWatcher_of_km`); the prefix watch from revision `1` (the read at `0`, `km_reached_of`).
The partitioner forked as `Main`'s. Then watchkv's `Main`: the log under its mutex (`wsInvH`),
the writer goroutines (each member's `memberPut`, the adapter's write update), the log's puts
taken under the lock, `maxRev`, `collect` (each response by `resp_km`), the cancel, and the
check: `CheckOk` from `collectOk` and the puts' `okFactK`s (`revAtK_agree`). The start's failure
ends `MainWatch` with `WatchFailed`; `collect`'s `false` with `WatchEnded`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.linkv3p.MainWatch
public import Spec.github_com.mit_pdos.etcd_grove.examples.linkv3p.startCluster
public import Spec.github_com.mit_pdos.etcd_grove.examples.linkv3p.partitioner
public import Spec.github_com.mit_pdos.etcd_grove.examples.common.GenAll
public import Spec.github_com.mit_pdos.etcd_grove.examples.linkv3p.writer
public import Spec.github_com.mit_pdos.etcd_grove.examples.common.MaxRev
public import Spec.github_com.mit_pdos.etcd_grove.examples.common.Collect
public import Proof.github_com.mit_pdos.etcd_grove.examples.common.CollectPlan
public import Spec.github_com.mit_pdos.etcd_grove.examples.common.Check
public import Proof.github_com.mit_pdos.etcd_grove.examples.linkv3p.WatchWrites
public import Proof.github_com.mit_pdos.etcd_grove.examples.linkvtxn.Boot
public import Spec.go_uber_org.zap.NewNop
public import Spec.go_etcd_io.etcd.client.v3.watcher__Watch
public import Spec.context.ErrAny
public import Spec.go_etcd_io.etcd.client.v3.WithPrefix
public import Spec.go_etcd_io.etcd.client.v3.WithRev
public import Spec.go_etcd_io.etcd.client.v3.WithProgressNotify
public import Spec.go_etcd_io.etcd.client.v3.WithCreatedNotify
public import Perennial.Proof.sync.WaitGroupJoin
public import Perennial.Proof.sync.Link
public import Perennial.Proof.context.Link
public import Perennial.Proof.context.Results
public import Proof.go_etcd_io.etcd.cache.v3.Cache__watchEvents
public import Proof.github_com.mit_pdos.etcd_grove.examples.linkv3p.WatchEnv

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace linkv3p

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.linkv3p.Assumptions]

omit package_sem in
/-- **The check's premise** (`CheckOk`; watchkv's `checkOk_of`, over the KV state): each successful
put's revision is a watched event's, whose key and value are the put's (`revAtK_agree`). -/
theorem checkOkK_of (γ : client.KMNames) (trs : List wkv) (upTo : w64) (evs : List wev) (oks : List wrec)
    (hup : ∀ p ∈ oks, sint.Z p.Rev' ≤ sint.Z upTo) :
    common.collectOk (GF := GF) (revAtK γ) (trs.map pairOf) upTo evs ∗
        □ ([∗list] p ∈ oks, okFactK γ p) ⊢
      ⌜CheckOk evs trs oks⌝ := by
  unfold common.collectOk
  iintro ⟨⟨%Hc, #Hrevs⟩, #Hoks⟩
  obtain ⟨hup0, hlen, hevs⟩ := Hc
  ihave %H : ⌜∀ p, p ∈ oks → 2 ≤ sint.Z p.Rev' ∧ ∃ e, evs[(sint.Z p.Rev' - 2).toNat]? = some e ∧
      e.Key' = p.Key' ∧ e.Val' = p.Val'⌝ $$ []
  · iapply BI.pure_forall.2
    iintro %p
    by_cases hp : p ∈ oks
    · obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hp
      ihave Hf := BigSepL.bigSepL_lookup (Φ := fun _ p => okFactK (GF := GF) γ p) hk $$ Hoks
      iunfold okFactK at Hf
      icases Hf with ⟨%h2, #Hra⟩
      have hle := hup p hp
      have hlt : (sint.Z p.Rev' - 2).toNat < evs.length := by
        rcases hup0 with h0 | h0
        · rw [h0] at hle; simp at hle; omega
        · omega
      obtain ⟨e, he⟩ : ∃ e, evs[(sint.Z p.Rev' - 2).toNat]? = some e :=
        ⟨_, List.getElem?_eq_getElem hlt⟩
      have hidx : 2 + (sint.Z p.Rev' - 2).toNat = (sint.Z p.Rev').toNat := by omega
      ihave #He : revAtK γ (sint.Z p.Rev').toNat e.Key' e.Val' $$ []
      · rw [← hidx]; iapply Hrevs; ipureintro; exact he
      ihave %Hag := revAtK_agree γ (sint.Z p.Rev').toNat e.Key' e.Val' p.Key' p.Val' $$ [He Hra]
      · iframe #
      ipureintro; intro _; exact ⟨h2, e, he, Hag.1, Hag.2⟩
    · ipureintro; intro h; exact absurd h hp
  ipureintro
  exact ⟨hlen, hevs, H⟩

set_option maxHeartbeats 1600000 in
set_option maxRecDepth 8192 in
theorem MainWatch.wp_proof
    (wp_GenAll : common.GenAll.spec (GF := GF) (hG := hG))
    (wp_NewNop : zap.NewNop.spec (GF := GF) (hG := hG))
    (wp_startCluster : startCluster.spec (GF := GF) (hG := hG))
    (wp_partitioner : partitioner.spec (GF := GF) (hG := hG))
    (wp_writer : writer.spec (GF := GF) (hG := hG))
    (wp_MaxRev : common.MaxRev.spec (GF := GF) (hG := hG))
    (wp_Collect : common.Collect.spec (GF := GF) (hG := hG))
    (wp_Check : common.Check.spec (GF := GF) (hG := hG))
    (wp_ErrAny : context.ErrAny.spec (GF := GF) (hG := hG))
    (wp_Watch : watcher.Watch.spec (GF := GF) (hG := hG))
    (wp_WithPrefix : WithPrefix.spec (GF := GF) (hG := hG))
    (wp_WithRev : WithRev.spec (GF := GF) (hG := hG))
    (wp_WithProgressNotify : WithProgressNotify.spec (GF := GF) (hG := hG))
    (wp_WithCreatedNotify : WithCreatedNotify.spec (GF := GF) (hG := hG)) :
    MainWatch.spec (GF := GF) (hG := hG) := by
  intro CS ES FS RS CRE CEC N id₁ id₂ id₃ ctxs boot nw nops sched steps Hbf Htb Hrb48
    HrbN Hck Haf Hbuq Hrf Hdbo Hms hAs H0 H31 Hops Hmul
  wp_start as ⟨Ha₁, Ha₂, Ha₃, Hc₁, Hc₂, Hc₃, Hba₁, Hba₂, Hba₃, Hf₁, Hf₂, Hf₃, #Hsched, Htok, #Hprem⟩
  -- `io.EOF` (the watch client's) and `context`'s `closedchan`, from their packages' facts
  ihave #Heo : client.eofOk (GF := GF) $$ []
  · iapply (client.eofOk_of_init hAs)
    iPkgInit
  ihave #Hcci : context.isClosedchanInit (GF := GF) $$ []
  · iapply context.isClosedchanInit_of_init
    iPkgInit
  ihave #Pctx : isPkgInit (PROP := IProp GF) pkg_id.context $$ []
  · iPkgInit
  ihave #Psync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  ihave #Pcli : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 $$ []
  · iPkgInit
  ihave #Ppb : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb $$ []
  · iPkgInit
  ihave #Pzap : isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap $$ []
  · iPkgInit
  -- `tried := genAll(nw * nops)`: the puts, picked before the members start
  have hmul : sint.Z (nw * nops) = sint.Z nw * sint.Z nops := by
    have h1 : 0 ≤ sint.Z nw * sint.Z nops := Int.mul_nonneg H0 Hops
    word
  (try wp_auto)
  wp_apply wp_slice_literal (l := genKeys)
  isplitr
  · ipureintro; rfl
  iintro %ksl ⟨Hks, -⟩
  simp only [go.arrayLiteralSize, List.foldl, Int.reduceAdd,
    show max (max (3 : Int) 0) 0 = 3 from rfl]
  imod ownSlice_persist _ _ _ $$ Hks with #Hks
  (try wp_auto)
  wp_apply (wp_GenAll (nw * nops) _ genKeys (by rw [hmul]; exact Int.mul_nonneg H0 Hops)
      (by decide) (by decide)) as %tsl ⟨%trs, Htrs, %Htrs⟩
  · iframe #
  imod ownSlice_persist _ _ _ $$ Htrs with #Htrs
  have hpk : ∀ kv ∈ trs.map pairOf, wkPfx <+: kv.1 := by
    intro kv hkv
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hkv
    have hk := (Htrs.2 p hp).1
    simp only [pairOf]
    simp only [genKeys, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with h | h | h <;> rw [h] <;> decide
  have hsz : ∀ p ∈ trs, common.wkvSizeOk p := fun p hp =>
    common.GenKv.sizeOk (by decide) (Htrs.2 p hp)
  (try wp_auto)
  -- the cluster, its clients' watch prefix `wk/`
  wp_apply wp_NewNop as %lg %Hlg
  (try wp_auto)
  wp_apply (wp_startCluster N id₁ id₂ id₃ ctxs boot lg wkPfx Hbf Hlg Htb Hrb48 HrbN Hck Haf Hbuq Hrf Hdbo Hms)
    $$ [Ha₁ Ha₂ Ha₃ Hc₁ Hc₂ Hc₃ Hba₁ Hba₂ Hba₃ Hf₁ Hf₂ Hf₃ Htok] as %srvs %brs %clis %ok Hup
  · iframe; iframe #
  icases Hup with (%Hok | ⟨%Hok, Htok, Hup⟩)
  · subst Hok
    (try wp_auto)
    iapply HΦ; ipureintro; right; left; rfl
  subst Hok
  (try wp_auto)
  iunfold clusterUp at Hup
  icases Hup with ⟨%γ, %γn, %ρ₁, %ρ₂, %ρ₃, %E₁, %E₂, %E₃, %cid₁, %cid₂, %cid₃, %mid₁, %mid₂,
    %mid₃, %R₁, %R₂, %R₃, %s₁, %s₂, %s₃, %cl₁, %cl₂, %cl₃, %br₁, %br₂, %br₃, #Hsrvs, #Hbrs, #Hclis,
    #Hm₁, #Hm₂, #Hm₃, Hctl₁, Hctl₂, Hctl₃, Hob₁, Hob₂, Hob₃, #Hnc₁, #Hnc₂, #Hnc₃, Hetcd, %Hal⟩
  obtain ⟨hst₂, hst₃⟩ := Hal
  iunfold memberAt at Hm₁ Hm₂ Hm₃
  icases Hm₁ with ⟨#Hfw₁, #Hrd₁, #HPut₁, #HRange₁, #HDel₁, #HTxn₁, %Hnr₁, ⟨%pw₁, #Hws₁⟩,
    %HR₁, #Hstr₁, %Hp₁⟩
  icases Hm₂ with ⟨#Hfw₂, #Hrd₂, #HPut₂, #HRange₂, #HDel₂, #HTxn₂, %Hnr₂, ⟨%pw₂, #Hws₂⟩,
    %HR₂, #Hstr₂, %Hp₂⟩
  icases Hm₃ with ⟨#Hfw₃, #Hrd₃, #HPut₃, #HRange₃, #HDel₃, #HTxn₃, %Hnr₃, ⟨%pw₃, #Hws₃⟩,
    %HR₃, #Hstr₃, %Hp₃⟩
  obtain ⟨hr₁, hc₁, hch₁, hlog₁, hoff₁⟩ := Hp₁
  obtain ⟨hr₂, hc₂, hch₂, hlog₂, hoff₂⟩ := Hp₂
  obtain ⟨hr₃, hc₃, hch₃, hlog₃, hoff₃⟩ := Hp₃
  -- the members' names are the history's (the first member's)
  -- (2026-10-27, the server port) the members' raft names are the cluster's but for each one's
  -- storage registry
  obtain ⟨r₁, hr₁⟩ := hr₁
  obtain ⟨r₂, hr₂⟩ := hr₂
  obtain ⟨r₃, hr₃⟩ := hr₃
  have hm₁ : v3rpc.memberOf ρ₁.rd.raft ρ₁.rd.kv ρ₁.rd :=
    v3rpc.memberOf_of_eq _ _ _ rfl rfl rfl rfl
  have hm₂ : v3rpc.memberOf ρ₁.rd.raft ρ₁.rd.kv ρ₂.rd :=
    ⟨by rw [hr₂, hr₁], hc₂.trans hc₁.symm, hch₂.trans hch₁.symm, hlog₂.trans hlog₁.symm⟩
  have hm₃ : v3rpc.memberOf ρ₁.rd.raft ρ₁.rd.kv ρ₃.rd :=
    ⟨by rw [hr₃, hr₁], hc₃.trans hc₁.symm, hch₃.trans hch₁.symm, hlog₃.trans hlog₁.symm⟩
  -- the clients' adapter over the KV state, its property the plan's (the start: revision `1`, no
  -- change)
  have hboot : kvModel ρ₁.rd.kv (bootEntries (LogEntry.toEntries boot 0)) = [[], []] := by
    unfold kvModel
    rw [linkv.kvRaftOf_boot _ _ _ (fun _ _ => True) (ids id₁ id₂ id₃)
      (LogEntry.toEntries boot 0) (srvBootLogOk_of_BootLog _ _ _ Hbf.boot), hlog₁]
  have hW0 : wkW (trs.map pairOf) (kvModelSt ρ₁.rd.kv (bootEntries (LogEntry.toEntries boot 0))).changes := by
    rw [kvModelSt_boot _ (fun _ _ => True) _ _ (srvBootLogOk_of_BootLog _ _ _ Hbf.boot), hboot]; exact wkW_start _
  imod (client.kmInv_alloc ρ₁.rd.kv _ (wkW (trs.map pairOf)) hW0) $$ Hetcd
    with ⟨%γ, %Hγ, #Hkm, #Hlb0⟩
  obtain ⟨hγk, hγW⟩ := Hγ
  -- each member's watch facts
  ihave #Hmw₁ : memberWatch ρ₁.rd s₁ E₁ ρ₁ R₁ $$ []
  · iunfold memberWatch
    isplitr
    · iexact Hrd₁
    isplitr
    · iexists pw₁; iexact Hws₁
    ipureintro; exact ⟨HR₁.2, hm₁, rfl, hoff₁⟩
  ihave #Hmw₂ : memberWatch ρ₁.rd s₂ E₂ ρ₂ R₂ $$ []
  · iunfold memberWatch
    isplitr
    · iexact Hrd₂
    isplitr
    · iexists pw₂; iexact Hws₂
    ipureintro; exact ⟨HR₂.2, hm₂, hst₂, hoff₂⟩
  ihave #Hmw₃ : memberWatch ρ₁.rd s₃ E₃ ρ₃ R₃ $$ []
  · iunfold memberWatch
    isplitr
    · iexact Hrd₃
    isplitr
    · iexists pw₃; iexact Hws₃
    ipureintro; exact ⟨HR₃.2, hm₃, hst₃, hoff₃⟩
  -- each member's `Watch` stream at its bridge
  ihave #Hb₁ := isGrpcStream_forwards bridgeAddr₁ clientAddr₁ _ _ _ $$ [Hfw₁ Hstr₁]
  · iframe #
  ihave #Hb₂ := isGrpcStream_forwards bridgeAddr₂ clientAddr₂ _ _ _ $$ [Hfw₂ Hstr₂]
  · iframe #
  ihave #Hb₃ := isGrpcStream_forwards bridgeAddr₃ clientAddr₃ _ _ _ $$ [Hfw₃ Hstr₃]
  · iframe #
  -- the first client's `Watcher`, with the members' facts, etcd's watch contract at the history
  ihave #Hconn := watchEnv_conn wp_ErrAny hAs R₁ R₂ R₃ ρ₁.rd wkPfx (by decide) hlog₁
    (by omega) s₁ s₂ s₃
    E₁ E₂ E₃ ρ₁ ρ₂ ρ₃ $$ [Pcli Ppb Pctx Heo Hmw₁ Hmw₂ Hmw₃ Hb₁ Hb₂ Hb₃]
  · iframe #
  ihave ⟨%w, %conn, %wc, %lgw, %ics, #HWf, #Hcw⟩ := isNewClient_watcher_of cl₁
    [bridgeAddr₁, bridgeAddr₂, bridgeAddr₃] (watchEnv R₁ R₂ R₃ ρ₁.rd wkPfx) $$ [Hnc₁ Hconn]
  · iframe #
  ihave #Hkw : client.isKvWatcher (GF := GF) w γ.kv $$ []
  · iunfold client.isKvWatcher
    iexists { watchEnv R₁ R₂ R₃ ρ₁.rd wkPfx with conn := conn, ics := ics, wc := wc, lg := lgw }
    iframe Hcw
    ipureintro; rw [hγk]; rfl
  ihave #Hew := client.isEtcdWatcher_of_km w γ wkPfx (by decide) (by decide) $$ [Pcli Ppb Pctx Hkw]
  · iframe #
  (try wp_auto)
  -- `wctx, cancel := context.WithCancel(context.Background())`
  wp_apply context.wp_Background
  wp_apply context.wp_WithCancel_Background iprop(True) $$ [$Pctx $Hcci]
    as %wctx %γc %cancel ⟨#Hcancel, #Hwctx, -⟩
  (try wp_auto)
  -- the watch's options (the cache's `watchEvents`')
  wp_apply wp_WithPrefix as %f1 #Hf1
  wp_apply wp_WithRev (W64 1) as %f2 #Hf2
  wp_apply wp_WithProgressNotify as %f3 #Hf3
  wp_apply wp_WithCreatedNotify as %f4 #Hf4
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %osl ⟨Hosl, -⟩
  ipersist Hosl
  (try wp_auto)
  generalize hosl : slice.mk osl _ _ = optsSl
  have hfs : (([f1, zero_val GoFunc, zero_val GoFunc, zero_val GoFunc].set
      (sint.nat (W64 (0 + 1))) f2).set (sint.nat (W64 (0 + 1 + 1))) f3).set
      (sint.nat (W64 (0 + 1 + 1 + 1))) f4 = [f1, f2, f3, f4] := rfl
  ihave #Hopts : optsAt optsSl ([withPrefixM, withRevM (W64 1), withProgressNotifyM,
      withCreatedNotifyM] : List (OpFull → OpFull)) $$ []
  · iunfold optsAt
    iexists _
    iframe Hosl
    isplitr
    · ipureintro; rw [hfs]; rfl
    imodintro
    iintro %i %f %g %Hf %Hg
    rw [hfs] at Hf
    rcases i with _ | _ | _ | _ | i
    · cases Hf; cases Hg; iexact Hf1
    · cases Hf; cases Hg; iexact Hf2
    · cases Hf; cases Hg; iexact Hf3
    · cases Hf; cases Hg; iexact Hf4
    · simp at Hf
  -- `wch := clis[0].Watcher.Watch(wctx, prefix, ...)`: etcd's watch contract, from revision `1`
  -- (the read at `0`: the start's changes seen)
  have h10 : (W64 1 - W64 1 : w64) = W64 0 := by decide
  ihave ⟨#Hre0, #Hra0⟩ := client.km_reached_of γ _ 0 (by omega) (by decide) $$ Hlb0
  ihave #Hrd0' : etcdRead (EM := client.etcdModelOfKV γ) (W64 1 - W64 1) $$ []
  · rw [h10]
    iunfold etcdRead
    isplitl
    · iexists W64 ((0 : Nat) : Int)
      isplitr
      · ipureintro; decide
      rw [client.etcdModelOfKV_etcdReadAt]
      iexact Hra0
    iunfold etcdReached
    ileft; ipureintro; decide
  ihave %Hcl := ownSlice_len $$ Hclis
  have hb : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z clis.len := by
    obtain ⟨h1, -⟩ := Hcl
    unfold sint.nat at h1
    simp at h1
    refine ⟨by decide, ?_⟩
    show (0 : Int) < BitVec.toInt clis.len
    omega
  simp only [hb, _root_.and_self, ↓reduceIte]
  wp_apply wp_load_slice_index _ (sint.Z (W64 0)) [cl₁, cl₂, cl₃] _ cl₁ hb.1 $$ [] as -
  · iframe #; ipureintro; rfl
  (try wp_auto)
  iunfold isEtcdWatcher at Hew
  ihave #HW := Hew $$ %wctx
    %({ Values := ∅, Deadline := none, Done_gn := γc, PDone := iprop(True) } :
      context.ContextDesc (IProp GF))
    %wkPfx %optsSl
    %([withPrefixM, withRevM (W64 1), withProgressNotifyM, withCreatedNotifyM] :
      List (OpFull → OpFull))
    %(W64 1)
  wp_apply HW $$ [] as %wch %γw ⟨#Hwch, Hcons⟩
  · iframe Hwctx Hopts
    isplitl []
    · ipureintro
      exact ⟨(watchEvents_opts wkPfx (W64 1)).1, (watchEvents_opts wkPfx (W64 1)).2, by decide⟩
    iExactEq Hrd0'; rfl
  (try wp_auto)
  -- `go partitioner(srvs, brs, sched)`: every member's place in the network, every bridge owned
  ihave Hmem : ([∗list] s ∈ [s₁, s₂, s₃], ∃ id : w64, common.srvPeerCtl γn s id) $$ [Hctl₁ Hctl₂ Hctl₃]
  · iapply (BigSepL.bigSepL_cons
      (Φ := fun _ s => iprop(∃ id : w64, common.srvPeerCtl (GF := GF) γn s id))).2
    isplitl [Hctl₁]
    · iexists id₁; iexact Hctl₁
    iapply (BigSepL.bigSepL_cons
      (Φ := fun _ s => iprop(∃ id : w64, common.srvPeerCtl (GF := GF) γn s id))).2
    isplitl [Hctl₂]
    · iexists id₂; iexact Hctl₂
    iapply (BigSepL.bigSepL_cons
      (Φ := fun _ s => iprop(∃ id : w64, common.srvPeerCtl (GF := GF) γn s id))).2
    isplitl [Hctl₃]
    · iexists id₃; iexact Hctl₃
    iapply BigSepL.bigSepL_nil.2
    itrivial
  ihave Hobs : ([∗list] br ∈ [br₁, br₂, br₃], ∃ addr : GoString, bridge.ownBridge br addr false)
    $$ [Hob₁ Hob₂ Hob₃]
  · iapply (BigSepL.bigSepL_cons
      (Φ := fun _ br => iprop(∃ addr : GoString, bridge.ownBridge (GF := GF) br addr false))).2
    isplitl [Hob₁]
    · iexists clientAddr₁; iexact Hob₁
    iapply (BigSepL.bigSepL_cons
      (Φ := fun _ br => iprop(∃ addr : GoString, bridge.ownBridge (GF := GF) br addr false))).2
    isplitl [Hob₂]
    · iexists clientAddr₂; iexact Hob₂
    iapply (BigSepL.bigSepL_cons
      (Φ := fun _ br => iprop(∃ addr : GoString, bridge.ownBridge (GF := GF) br addr false))).2
    isplitl [Hob₃]
    · iexists clientAddr₃; iexact Hob₃
    iapply BigSepL.bigSepL_nil.2
    itrivial
  wp_apply wp_fork $$ [Hobs Hmem]
  · wp_apply (wp_partitioner inferInstance γn _ _ sched [s₁, s₂, s₃] [br₁, br₂, br₃] steps) $$ [Hobs Hmem]
    all_goals (try (iframe #))
    all_goals (try iframe)
    ipureintro; exact isPanic_intoVal ()
  (try wp_auto)
  -- the writers' members, at their bridges: etcd's KV there, their empty logs, the KV's state
  let ms : List (client.SrvAt GF) :=
    [⟨bridgeAddr₁, E₁, ρ₁.rd, cid₁, mid₁⟩, ⟨bridgeAddr₂, E₂, ρ₂.rd, cid₂, mid₂⟩,
      ⟨bridgeAddr₃, E₃, ρ₃.rd, cid₃, mid₃⟩]
  have hms : ms.map client.SrvAt.addr = [bridgeAddr₁, bridgeAddr₂, bridgeAddr₃] := rfl
  imod mvcc.idxCert_nil (GF := GF) E₁.γ.idx with #HF₁
  imod mvcc.idxCert_nil (GF := GF) E₂.γ.idx with #HF₂
  imod mvcc.idxCert_nil (GF := GF) E₃.γ.idx with #HF₃
  ihave #Hmps : ([∗list] x ∈ ms, memberPut γ.kv x) $$ []
  · iapply BigSepL.bigSepL_cons.2
    isplitr
    · iunfold memberPut
      isplitr
      · iunfold client.kvRegsAt
        isplitr
        · iapply isGrpcRpc_forwards $$ [Hfw₁ HPut₁]; iframe #
        isplitr
        · iapply isGrpcRpc_forwards $$ [Hfw₁ HRange₁]; iframe #
        isplitr
        · iapply isGrpcRpc_forwards $$ [Hfw₁ HDel₁]; iframe #
        iapply isGrpcRpc_forwards $$ [Hfw₁ HTxn₁]; iframe #
      iframe #
      ipureintro; rw [hγk]
    iapply BigSepL.bigSepL_cons.2
    isplitr
    · iunfold memberPut
      isplitr
      · iunfold client.kvRegsAt
        isplitr
        · iapply isGrpcRpc_forwards $$ [Hfw₂ HPut₂]; iframe #
        isplitr
        · iapply isGrpcRpc_forwards $$ [Hfw₂ HRange₂]; iframe #
        isplitr
        · iapply isGrpcRpc_forwards $$ [Hfw₂ HDel₂]; iframe #
        iapply isGrpcRpc_forwards $$ [Hfw₂ HTxn₂]; iframe #
      iframe #
      ipureintro; rw [hγk]; exact hst₂
    iapply BigSepL.bigSepL_cons.2
    isplitr
    · iunfold memberPut
      isplitr
      · iunfold client.kvRegsAt
        isplitr
        · iapply isGrpcRpc_forwards $$ [Hfw₃ HPut₃]; iframe #
        isplitr
        · iapply isGrpcRpc_forwards $$ [Hfw₃ HRange₃]; iframe #
        isplitr
        · iapply isGrpcRpc_forwards $$ [Hfw₃ HDel₃]; iframe #
        iapply isGrpcRpc_forwards $$ [Hfw₃ HTxn₃]; iframe #
      iframe #
      ipureintro; rw [hγk]; exact hst₃
    iapply BigSepL.bigSepL_nil.2
    itrivial
  -- (D29) the bridges' addresses are refusal-free: every client's writes are sent at most once
  ihave %Hb₁ : ⌜noRefusalAt bridgeAddr₁⌝ $$ []
  · iunfold forwards at Hfw₁; icases Hfw₁ with ⟨-, %Hf, -⟩; ipureintro; exact Hf Hnr₁
  ihave %Hb₂ : ⌜noRefusalAt bridgeAddr₂⌝ $$ []
  · iunfold forwards at Hfw₂; icases Hfw₂ with ⟨-, %Hf, -⟩; ipureintro; exact Hf Hnr₂
  ihave %Hb₃ : ⌜noRefusalAt bridgeAddr₃⌝ $$ []
  · iunfold forwards at Hfw₃; icases Hfw₃ with ⟨-, %Hf, -⟩; ipureintro; exact Hf Hnr₃
  have hnr : ∀ a ∈ [bridgeAddr₁, bridgeAddr₂, bridgeAddr₃], noRefusalAt a := by
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, _root_.or_false] at ha
    rcases ha with rfl | rfl | rfl
    · exact Hb₁
    · exact Hb₂
    · exact Hb₃
  ihave #Hcls : ([∗list] cl ∈ [cl₁, cl₂, cl₃], isNewClient cl (ms.map client.SrvAt.addr)
      (watchEnv R₁ R₂ R₃ ρ₁.rd wkPfx) ∗ client.clientWriteOnce cl (ms.map client.SrvAt.addr)) $$ []
  · rw [hms]
    iapply BigSepL.bigSepL_cons.2
    isplitr
    · iframe Hnc₁; iunfold client.clientWriteOnce; ipureintro; exact hnr
    iapply BigSepL.bigSepL_cons.2
    isplitr
    · iframe Hnc₂; iunfold client.clientWriteOnce; ipureintro; exact hnr
    iapply BigSepL.bigSepL_cons.2
    isplitr
    · iframe Hnc₃; iunfold client.clientWriteOnce; ipureintro; exact hnr
    iapply BigSepL.bigSepL_nil.2
    itrivial
  -- the log of the successful puts under its mutex (`wsInvH`)
  icases typedPointsto_split _ _ _ $$ «$r0» with Hr0
  try simp only [TypedPointsto.typedPointstoDef]
  icases Hr0 with ⟨mu, ok, -⟩
  imod sync.init_Mutex (wsInvH «$r0_ptr» γ) ⊤
      (structFieldRef github_com.mit_pdos.etcd_grove.examples.common.Writes go!"Mu" «$r0_ptr»)
    $$ mu [ok] with #Hmu
  · inext
    iunfold wsInvH
    iexists slice.nil, []
    iframe ok
    isplitr
    · iapply ownSlice_nil
    isplitr
    · iapply ownSliceCap_nil
    iintro !>
    iapply BigSepL.bigSepL_nil.2; itrivial
  ipersist w
  ipersist clis
  ipersist tried
  ipersist nops
  -- the writers' wait group
  imod sync.init_WaitGroup (sync.join.wgjN.@"wg") wg_ptr $$ wg with ⟨%γwg, Hwg⟩
  imod sync.join.init wg_ptr γwg $$ Hwg with Hwg
  ihave IH : (∃ (k : w64) (na : w32),
      "i" ∷ i_ptr ↦ k ∗ "Hwg" ∷ sync.join.ownAdder wg_ptr na iprop(True) ∗
      "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ sint.Z nw ∧ sint.Z na = sint.Z k⌝ : IProp GF)
    $$ [i Hwg]
  · iexists W64 0, W32 0
    iframe
    ipureintro
    exact ⟨by decide, H0, by decide⟩
  wp_for IH
  wp_if_destruct
  · -- a writer: `lo := i * nops`, `wg.Add(1)`, `go func() { writer(...); wg.Done() }()`
    have Hlt : sint.Z k < sint.Z nw := by simpa using Hif
    have hlo : sint.Z (k * nops) = sint.Z k * sint.Z nops := by
      have h1 : 0 ≤ sint.Z k * sint.Z nops := Int.mul_nonneg Hk.1 Hops
      have h2 : sint.Z k * sint.Z nops ≤ sint.Z nw * sint.Z nops :=
        Int.mul_le_mul_of_nonneg_right (by omega) Hops
      word
    have hhi : sint.Z (k * nops + nops) = sint.Z k * sint.Z nops + sint.Z nops := by
      have h2 : (sint.Z k + 1) * sint.Z nops ≤ sint.Z nw * sint.Z nops :=
        Int.mul_le_mul_of_nonneg_right (by omega) Hops
      have h1 : 0 ≤ sint.Z k * sint.Z nops := Int.mul_nonneg Hk.1 Hops
      rw [Int.add_mul, Int.one_mul] at h2
      word
    (try wp_auto)
    wp_apply (sync.join.WaitGroup.wp_Add_of sync.WaitGroup.wp_Add iprop(True) wg_ptr iprop(True) na)
      $$ [Hwg] as ⟨Hwg, Hdone⟩
    · iframe; ipureintro; word
    ipersist lo
    wp_apply wp_fork $$ [Hdone]
    · (try wp_auto)
      wp_apply (wp_writer clis [cl₁, cl₂, cl₃] ms (watchEnv R₁ R₂ R₃ ρ₁.rd wkPfx) γ «$r0_ptr»
          tsl trs (k * nops) (k * nops + nops) (trs.map pairOf) hAs hγW rfl (by simp) (by rw [hlo]; exact Int.mul_nonneg Hk.1 Hops) (by rw [hlo, hhi]; omega)
          (by
            rw [hhi, Htrs.1]
            have h2 : (sint.Z k + 1) * sint.Z nops ≤ sint.Z nw * sint.Z nops :=
              Int.mul_le_mul_of_nonneg_right (by omega) Hops
            rw [Int.add_mul, Int.one_mul] at h2
            have h0 : (0 : Int) ≤ sint.Z (nw * nops) := by
              rw [hmul]; exact Int.mul_nonneg H0 Hops
            have e : ((sint.nat (nw * nops) : Nat) : Int) = sint.Z (nw * nops) := by word
            rw [e, hmul]
            omega) hsz) $$ []
      · iframe #
      (try wp_auto)
      wp_apply (sync.join.WaitGroup.wp_Done_of sync.WaitGroup.wp_Done iprop(True) wg_ptr)
        $$ [Hdone]
      · iframe
      itrivial
    wp_for_post
    iframe
    iexists (k + W64 1), (na + W32 1)
    iframe
    isplitl [Hwg]
    · iapply sync.join.ownAdder_wand $$ [] Hwg
      iintro -; itrivial
    ipureintro
    refine ⟨by word, by word, by word⟩
  -- the writers are done: `wg.Wait()`
  wp_apply (sync.join.WaitGroup.wp_Wait_of sync.WaitGroup.wp_Wait _ na wg_ptr) $$ [$Hwg] as -
  (try wp_auto)
  -- the successful puts, taken out of the log under the lock
  wp_apply (sync.Mutex.wp_Lock (structFieldRef
      github_com.mit_pdos.etcd_grove.examples.common.Writes go!"Mu" «$r0_ptr»)
      (wsInvH «$r0_ptr» γ)) $$ [] as ⟨Hown, Hws0⟩
  · iframe #
  iunfold wsInvH at Hws0
  icases Hws0 with ⟨%osl', %oks, Hok, Hos, Hocap, #Hoks⟩
  (try wp_auto)
  wp_apply (sync.Mutex.wp_Unlock (structFieldRef
      github_com.mit_pdos.etcd_grove.examples.common.Writes go!"Mu" «$r0_ptr»)
      (wsInvH «$r0_ptr» γ)) $$ [Hown Hok]
  · iframe #
    iframe Hown
    inext
    iunfold wsInvH
    iexists slice.nil, []
    iframe Hok
    isplitr
    · iapply ownSlice_nil
    isplitr
    · iapply ownSliceCap_nil
    iintro !>
    iapply BigSepL.bigSepL_nil.2; itrivial
  (try wp_auto)
  -- `collect(wch, maxRev(oks))`, then `cancel()`
  wp_apply (wp_MaxRev osl' oks (DFrac.own 1)) $$ [Hos] as %m ⟨Hos, %Hm⟩
  · iframe
  ihave Hcons : etcdWatchConsumer γw 0 (W64 0) $$ [Hcons]
  · rw [← h10]; iexact Hcons
  ihave #Hrc := common.isRespChan_of_etcdWatchChan (EM := client.etcdModelOfKV γ) wch γw wkPfx
    $$ Hwch
  wp_apply (common.wp_Collect_plan wp_Collect (watchRespOk (EM := client.etcdModelOfKV γ) wkPfx) (revAtK γ)
      (client.kmInv γ) (trs.map pairOf) wch γw m (fun _ _ _ _ => inferInstance)
      (fun c c' v r => common.watchRespOk_closeErr' (EM := client.etcdModelOfKV γ) wkPfx c c' v r)
      (fun n c c' v r hne hcur => by
        iintro #Hi Hok
        iapply (resp_km γ (trs.map pairOf) hγW hpk n c c' v r hne hcur) $$ Hi Hok))
    $$ [Hcons] as %esl %ok2 Hcol
  · iframe; iframe #
  (try wp_auto)
  wp_apply Hcancel $$ [] as -
  · itrivial
  (try wp_auto)
  cases ok2
  · -- the watch ended before it reported every successful put
    (try wp_auto)
    iapply HΦ; ipureintro; right; right; rfl
  ihave ⟨%evs, Hes, Hcok⟩ := Hcol $$ %rfl
  ihave %HCk := checkOkK_of γ trs m evs oks Hm.2 $$ [Hcok]
  · iframe Hcok
    iexact Hoks
  imod ownSlice_persist _ _ _ $$ Hes with #Hes
  imod ownSlice_persist _ _ _ $$ Hos with #Hos
  (try wp_auto)
  wp_apply (wp_Check go!"linkv3p" go!"put" esl tsl osl' evs trs oks HCk) $$ []
  · iframe #
  (try wp_auto)
  iapply HΦ; ipureintro; left; rfl

end proof

end linkv3p
end EtcdGrove
end Perennial
