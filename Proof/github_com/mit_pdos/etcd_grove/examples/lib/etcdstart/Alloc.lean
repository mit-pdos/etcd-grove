/-
**The ghost state a one-member example's `Main` allocates before its member** (2026-10-22, D33).
Lean-first (no Rocq counterpart). What putget's `putget_alloc` and watchkv's `watchkv_alloc` were,
once, at a peer-URL directory `dir`, with the raft network's allocation (each `Main`'s
`netNames_alloc`) inside.

`alloc1`: for the one-member cluster `{id}` and its bootstrap log (the node API's `BootLog` at the
contexts `ctxs`, each entry a conf change of id `0` the server takes, `bootCCOk`; the id's 16 low
bits not `0`), from `proto.Marshal`'s contract at the bootstrap log (`bootMarshal`, which
`StartNode` takes; 2026-10-27, the server port: until then `bootstrap`'s contract gave it),
everything the member's `NewServer` takes of the ghost state (`memberBoot`): the member's names
chosen before the call (`newServerNames_alloc`: the store's index names, its certificate map, the
revisions' map), with the stand-in apply environment `env₀` carrying them and the claimers' facts
at the member's prefix the server's (`srvFloorFact`); its storage registry, empty (until then
`newServer` allocated it); the cluster's resources over the node API (`srvClusterBoot_alloc`), the
member's names and share (`srvMemberBoot_alloc`); the raft network with the member's slot and the directory
`dir` (`netNames_alloc`); and the client's `etcdKV` at the bootstrap log's model.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Defs
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.NewServerAlloc

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

/-- **What a one-member `Main` takes of the ghost state, for its member** (see the file header). -/
theorem alloc1 (hne : mvcc.api.names_nonempty.law) (id : w64) (ctxs : List (List w8)) (boot : List LogEntry)
    (Hlow : uint.Z id % 2 ^ 16 ≠ 0) (HB : BootLog [id] ctxs boot)
    (Hcc : bootCCOk [id] (LogEntry.toEntries boot 0))
    (Hurl : bootURLsOk (LogEntry.toEntries boot 0))
    (dir : w64 → List GoString) (Hone : ∀ f, dir f ≠ [] → f = id)
    (Hrb : receiptBound GF ≤ 2 ^ 64 - 2) (Hrb2 : receiptBound GF + boot.length ≤ 2 ^ 61)
    (cmp : Bool) (cret : Nat) (lm : lease.Mode) (m : lease.Mode)
    (hlg : lease.runCfg (GF := GF) lm m) :
    ⊢ bootMarshal (GF := GF) [id] ctxs (LogEntry.toEntries boot 0) ={⊤}=∗
      ∃ (γ : SrvRaft) (ρ : ReqNames) (E₀ : apply.AEnv GF)
        (Φs : w64 → w64 → List w8 → GName → IProp GF) (γn : NetNames GF),
      ⌜γ.vs = [id] ∧ γ.rule = srvRule (W64 0) (LogEntry.toEntries boot 0) ∧ γ.boot = LogEntry.toEntries boot 0 ∧
        γn.N = srvNet γ ∧ γn.dir = dir ∧ ρ.rd.kv.log0 = [[], []] ∧ ρ.rd.kv.cmp = cmp ∧
        ρ.rd.kv.cret = cret ∧ ρ.rd.kv.lm = lm⌝ ∗
      memberBoot γ ctxs ρ E₀ Φs id cmp m ∗ netHttpOk γn id ∗
      (if decide (lm ≠ .none) then iprop(True) else
        etcdKV ρ.rd.kv (kvModelSt ρ.rd.kv (bootEntries (LogEntry.toEntries boot 0)))) := by
  iintro #Hmarsh
  imod newServerNames_alloc (GF := GF) with ⟨%γs, %cok, %rev, Hidx, Hcok, Hrev⟩
  -- (R9, the `lean` merge) the stand-in's store name, any (`envAgree` does not read it)
  have γm : mvcc.api.MvccName := Classical.choice hne.1
  -- the member's storage registry, its `bootstrap`'s to join
  imod ghost_map_alloc_empty (GF := GF) (K := Loc) (V := MemStorNamesRec) with ⟨%reg, Hreg⟩
  have Hid0 : id ≠ W64 0 := by
    intro h; apply Hlow; rw [h]; decide
  let Φs : w64 → w64 → List w8 → GName → IProp GF := fun _ => srvFloorFacts γs.slog
  imod (srvClusterBoot_alloc (GF := GF) [id] ctxs boot (fun _ => γs.slog) reg Hrb Hrb2 HB (by simp)
      (by simp) (by simpa using Hid0.symm) Hcc Hurl (by simp) (by simpa using Hlow) cmp cret lm (idPfxOf (W16 (uint.Z id)))) $$ Hmarsh
    with ⟨%γ, %issued, %cnt, %wn, %fs, %γk, %Hγ, #Hsrl, #Hkv, Hetcd, #Hcl, #H0, #Hpm, #Hrc, Hms,
      Hwns⟩
  obtain ⟨hvs, hrule, hboot, hreg, hc0, hch, hlog, hiss, -, hwn, hfs, hkc, hkr, hklg, hgp⟩ := Hγ
  icases BigSepL.bigSepL_cons.1 $$ Hms with ⟨⟨Hp, #Hkf, Hnb, Hsd⟩, -⟩
  icases BigSepL.bigSepL_cons.1 $$ Hwns with ⟨Hwn, -⟩
  imod (srvMemberBoot_alloc (GF := GF) γ cnt γk id cok (fun _ => hgp)) $$ Hkv Hp [Hwn]
    with ⟨%ρ, %Hρ, #Hkvρ, Hsh, Hnk, Hwt⟩
  · rw [hwn]; iexact Hwn
  obtain ⟨hraft, hst, hc0', hch', hlog', hcok, hiss', hcnt, hpfx, hkc', -, hkr', hklg', hwn', hfs', hinc'⟩ := Hρ
  -- (R2c) the member's first key, its store's index registered, at its names
  ihave #Hkf' : idKeyFactAt ρ.ids.fs ρ.ids.key γs.slog $$ []
  · simp only [IdNames.key]; rw [hpfx, hinc', hfs', hfs]; iexact Hkf
  ihave #Hcl' : idClusterInv ρ.ids.issued ρ.ids.cnt ρ.ids.wn ρ.ids.fs srvFloorFacts $$ []
  · rw [hiss', hcnt, hwn', hfs', hiss, hwn, hfs]; iexact Hcl
  -- the raft network; (2026-10-24, rafthttp stage 6d) one member: no other member's hosts to
  -- register (until then the member's slot)
  imod (netNames_alloc (srvNet γ) dir (∅ : GMap w64 Unit) ⊤) with ⟨%γn, %Hγn, -, #HregN⟩
  ihave #Hnet := netHttpOk_single γn id
    (fun f hf => Hone f (by rw [Hγn.2] at hf; exact hf)) $$ HregN
  imodintro
  iexists γ, ρ, env₀ γm γs rev (srvApi.kvNx ρ.rd false) cmp, Φs, γn
  iframe Hnet
  isplitr
  · ipureintro
    exact ⟨hvs, hrule, hboot, Hγn.1, Hγn.2, by rw [hlog', hlog], by rw [hkc', hkc],
      by rw [hkr', hkr], by rw [hklg', hklg]⟩
  iunfold memberBoot
  simp only [env₀]
  rw [hiss', hcnt, hraft, hiss, hvs, hreg]
  rw [← srvPropMint_congr _ γk.ids ρ.ids (by rw [hiss', hiss])]
  rw [← hboot, etcdKV_congr ρ.rd.kv γk hst,
    show kvModelSt ρ.rd.kv (bootEntries γ.boot) = kvModelSt γk (bootEntries γ.boot) by
      unfold kvModelSt kvLeases kvModel; rw [hc0', hch', hlog']]
  rw [← hklg]
  rw [hcok]
  iframe Hnb Hsrl Hcl' Hkf' Hpm Hrc Hsh Hidx Hcok Hrev Hnk Hkvρ Hwt Hetcd Hsd Hreg
  isplitr
  · ipureintro
    exact ⟨rfl, by rw [hc0', hc0], by rw [hch', hch], by rw [hlog', hlog],
      hpfx, rfl, trivial, by rw [hkc', hkc], trivial, by rw [hklg', hklg]; exact hlg⟩
  iunfold idNoZero
  rw [hiss', hiss]
  iexact H0

/-- **`alloc1` at KV names that grant no lease** (its post before the lease-grant plan's 2.3: the
clients' half of the KV state returned). -/
theorem alloc1_false (hne : mvcc.api.names_nonempty.law) (id : w64) (ctxs : List (List w8)) (boot : List LogEntry)
    (Hlow : uint.Z id % 2 ^ 16 ≠ 0) (HB : BootLog [id] ctxs boot)
    (Hcc : bootCCOk [id] (LogEntry.toEntries boot 0))
    (Hurl : bootURLsOk (LogEntry.toEntries boot 0))
    (dir : w64 → List GoString) (Hone : ∀ f, dir f ≠ [] → f = id)
    (Hrb : receiptBound GF ≤ 2 ^ 64 - 2) (Hrb2 : receiptBound GF + boot.length ≤ 2 ^ 61)
    (cmp : Bool := false) (cret : Nat := 0) :
    ⊢ bootMarshal (GF := GF) [id] ctxs (LogEntry.toEntries boot 0) ={⊤}=∗
      ∃ (γ : SrvRaft) (ρ : ReqNames) (E₀ : apply.AEnv GF)
        (Φs : w64 → w64 → List w8 → GName → IProp GF) (γn : NetNames GF),
      ⌜γ.vs = [id] ∧ γ.rule = srvRule (W64 0) (LogEntry.toEntries boot 0) ∧ γ.boot = LogEntry.toEntries boot 0 ∧
        γn.N = srvNet γ ∧ γn.dir = dir ∧ ρ.rd.kv.log0 = [[], []] ∧ ρ.rd.kv.cmp = cmp ∧
        ρ.rd.kv.cret = cret⌝ ∗
      memberBoot γ ctxs ρ E₀ Φs id cmp ∗ netHttpOk γn id ∗
      etcdKV ρ.rd.kv (kvModelSt ρ.rd.kv (bootEntries (LogEntry.toEntries boot 0))) := by
  have h := alloc1 (GF := GF) hne id ctxs boot Hlow HB Hcc Hurl dir Hone Hrb Hrb2 cmp cret .none
    .none lease.runCfg_none
  simp only [ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte] at h
  iintro #Hmarsh
  imod h $$ Hmarsh with ⟨%γ, %ρ, %E₀, %Φs, %γn, %Hal, Hmb, Hnet, Hetcd⟩
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, -⟩ := Hal
  imodintro
  iexists γ, ρ, E₀, Φs, γn
  iframe Hmb Hnet Hetcd
  ipureintro
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩

end alloc

end etcdstart
end EtcdGrove
end Perennial
