/-
**The deployment bridge over the kit's two extensions** (notes/dsv-swiftpaxos.md, "Design
findings"): dsv-epaxos's `robust_of_distProtoLisRBT` (`epaxosnet/Bridge.lean`, itself
`Net/Statement/DistBridge.lean`'s `robust_of_distProtoRB` with listeners unset too and each
machine's thread bound), generalized from `[netExt]` to the kit's extension list `netShaExts`
(TCP and SHA-256 with `sha256NoCollisionFilter`, `Base.lean`). The differences:

* the ghost-state slots: `Base.lean`'s `netShaGpreS`, `netDistGF`'s slots for `netShaExts` (both
  extensions' ghost state in the universal slot 0, as `remoteGpreS` puts the network's);
* the extensions' global start: the net extension's is the first of the two (`netSha_globalStart`,
  `sep_elim_left`, as `Net`'s `net_globalStart`); the hash has none (`globalStart _ _ := True`);
* the extensions' initial global state (`goose_dist_adequacy_below`'s `Hinitg`): the net extension's from
  `DistDeploy` (no connection), the hash's (nothing hashed) from `Robust`'s `extsInitGlobal g`
  (the hash's `initgP` is its semantics' `initGlobal`).

Proved from Net's and Perennial's lemmas only. To move to `Net/Statement/DistBridge.lean` with
EPaxos's and QuePaxa's bridges (over any extension list that has the net extension first), once
Net offers it.
-/
module

public import Net.Statement.DistBridge
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Base

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Robustness Net Dsv

namespace github_com.imdea_software.swiftpaxos

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp netShaExts_has
  netShaExts_hasSha256 GooseGlobalGS.gooseInvGS

section bridgeSha
variable [GoGlobalContext] {GF : BundledGFunctors} [hPre : GooseGpreS GF]

/-- The global start resources of `netShaExts`: the net extension's (the first of the two). -/
theorem netSha_globalStart [G : GooseGlobalGS .hasLC GF] (g : ExtsGlobalState netShaExts.exts) :
    extsGlobalStart (GF := GF) g ⊢ netStart (extGlobalGS netExt) (extGlobal netExt g) :=
  sep_elim_left

/-- `DistBootWpGT` (dsv-epaxos's): `DistBootWpG` with the machine's thread bound at most `T`. -/
def DistBootWpGT [lctx : GoLocalContext] [G : GooseGlobalGS .hasLC GF] (T : Nat) (e : Expr)
    (P : IProp GF) : Prop :=
  ∀ hG : HeapGS .hasLC GF, hG.goose_globalGS = G →
    hG.goose_localGS.goose_go_local_context = lctx → threadBound GF ≤ T →
    P ⊢ ownGoState (hG := hG.goose_localGS.goose_go_stateGS) ∅ -∗
      WP e @ Stuckness.NotStuck; ⊤ {{ v, ⌜v = #()⌝ }}

theorem nodeWp_of_distBootGT [lctx : GoLocalContext] [G : GooseGlobalGS .hasLC GF] (T T' : Nat)
    (hT : T ≤ T') (e : Expr) (σ : state) (P : IProp GF) (hf : Fresh lctx σ)
    (H : DistBootWpGT T' e P) :
    P ⊢ nodeWp T e σ (fun v => v = #()) := by
  unfold nodeWp
  iintro HP %L
  unfold nodeWpBody
  iintro %hTb %hL Hls Hgs -
  rw [hf.2.1]
  imodintro
  iapply H ⟨G, L⟩ rfl (hL.trans hf.1) (by rw [hTb]; exact hT) $$ HP Hgs

/-- dsv-epaxos's `robust_of_distBootLisRBT` over `netShaExts`: from the addresses `addrs` and the
listeners `las` unset (pairwise disjoint, disjoint from `addrs`) to each machine's share, with
the receipt bound `receiptBound GF ≤ bound` and each machine's thread bound `threads`, `Robust`'s
(Perennial's `goose_dist_adequacy_below`: the thread bound along the execution at hand). -/
theorem robust_of_distBootLisRBT_sha [lctx : GoLocalContext] (addrs las : List GoString)
    (nodes : List (Expr × state)) (g : GlobalState) (threads bound : Nat)
    (hlas : las.Pairwise (fun l1 l2 => ∀ a, lisAccepts l1 a → ¬ lisAccepts l2 a))
    (hdisj : ∀ a ∈ addrs, ∀ la ∈ las, ¬ lisAccepts la a)
    (Hstart : ∀ [GooseGlobalGS .hasLC GF], receiptBound GF ≤ bound →
      ⊢ ([∗list] a ∈ addrs, addrUnset a) -∗ ([∗list] la ∈ las, lisUnset la) ={⊤}=∗
        ∃ Ps : Nat → IProp GF,
          ⌜∀ (i : Nat) (m : Expr × state), nodes[i]? = some m →
            DistBootWpGT threads m.1 (Ps i)⌝ ∗
          [∗list] i ↦ _m ∈ nodes, Ps i) :
    DistDeploy addrs nodes g → Robust [] nodes g threads bound := by
  rintro ⟨Hnd, Hok, Hconns, -⟩ hfresh hig _ n κs c hsteps hn i tp σ hi e he
  simp only [List.map_nil, List.nil_append] at hfresh hsteps
  have H := goose_dist_adequacy_below (GF := GF) (n + 1) threads nodes g (fun _ v => v = #())
    (fun _ p h => intoVal_ne_PanicV () p h.symm) ⟨Hconns, hig.2.1, trivial⟩
    (fun _ _ => ⟨trivial, trivial, trivial⟩)
    ?_ n κs c hsteps (Nat.lt_succ_self n) (fun m hm => (hfresh m hm).2.2) i tp σ hi
  · exact ⟨H.2.1 e he, H.2.2 e he⟩
  · intro G HN
    iintro Hg
    ihave Hnet := netSha_globalStart g.globalWorld $$ Hg
    ihave ⟨Hs, Hl⟩ := addrs_lis_start (Gg := G) (extGlobal netExt g.globalWorld) addrs las Hnd Hok
      hlas hdisj $$ Hnet
    imod Hstart (by omega) $$ Hs Hl with ⟨%Ps, %HP, HPs⟩
    imodintro
    iapply BigSepL.bigSepL_mono ?_ $$ HPs
    intro j m hm
    exact nodeWp_of_distBootGT threads threads (Nat.le_refl _) m.1 m.2 (Ps j)
      (hfresh m (List.mem_of_getElem? hm)) (HP j m hm)

/-- **The bridge over `netShaExts`, wildcard listeners and the thread bound** (dsv-epaxos's
`robust_of_distProtoLisRBT` over the kit's two extensions): `robust_of_distBootLisRBT_sha` with
the net protocol library's registry made first (`netProto_alloc`). -/
theorem robust_of_distProtoLisRBT_sha [lctx : GoLocalContext] (addrs las : List GoString)
    (nodes : List (Expr × state)) (g : GlobalState) (threads bound : Nat)
    (hlas : las.Pairwise (fun l1 l2 => ∀ a, lisAccepts l1 a → ¬ lisAccepts l2 a))
    (hdisj : ∀ a ∈ addrs, ∀ la ∈ las, ¬ lisAccepts la a)
    (Hstart : ∀ [GooseGlobalGS .hasLC GF] [NetProtoGS], receiptBound GF ≤ bound →
      ⊢ regCtx -∗ ([∗list] a ∈ addrs, addrUnset a) -∗ ([∗list] la ∈ las, lisUnset la) ={⊤}=∗
        ∃ Ps : Nat → IProp GF,
          ⌜∀ (i : Nat) (m : Expr × state), nodes[i]? = some m →
            DistBootWpGT threads m.1 (Ps i)⌝ ∗
          [∗list] i ↦ _m ∈ nodes, Ps i) :
    DistDeploy addrs nodes g → Robust [] nodes g threads bound := by
  refine robust_of_distBootLisRBT_sha (GF := GF) addrs las nodes g threads bound hlas hdisj ?_
  intro G hb
  iintro Hs Hl
  imod netProto_alloc ⊤ with ⟨%π, #Hreg⟩
  iapply @Hstart G π hb $$ Hreg Hs Hl

/-- `DistBootWpGT` whose program also gets the machine's main thread's token (`nodeWpBody`'s
`threadTok`), for a program whose main thread runs a spec taking it (net/http's `Serve`;
dsv-epaxos's `DistBootWpGTT`). -/
def DistBootWpGTT [lctx : GoLocalContext] [G : GooseGlobalGS .hasLC GF] (T : Nat) (e : Expr)
    (P : IProp GF) : Prop :=
  ∀ hG : HeapGS .hasLC GF, hG.goose_globalGS = G →
    hG.goose_localGS.goose_go_local_context = lctx → threadBound GF ≤ T →
    P ⊢ ownGoState (hG := hG.goose_localGS.goose_go_stateGS) ∅ -∗ threadTok -∗
      WP e @ Stuckness.NotStuck; ⊤ {{ v, ⌜v = #()⌝ }}

theorem nodeWp_of_distBootGTT [lctx : GoLocalContext] [G : GooseGlobalGS .hasLC GF] (T T' : Nat)
    (hT : T ≤ T') (e : Expr) (σ : state) (P : IProp GF) (hf : Fresh lctx σ)
    (H : DistBootWpGTT T' e P) :
    P ⊢ nodeWp T e σ (fun v => v = #()) := by
  unfold nodeWp
  iintro HP %L
  unfold nodeWpBody
  iintro %hTb %hL Hls Hgs Htok
  rw [hf.2.1]
  imodintro
  iapply H ⟨G, L⟩ rfl (hL.trans hf.1) (by rw [hTb]; exact hT) $$ HP Hgs Htok

/-- `robust_of_distBootLisRBT_sha` whose machines' programs also get their main thread's token. -/
theorem robust_of_distBootLisRBTT_sha [lctx : GoLocalContext] (addrs las : List GoString)
    (nodes : List (Expr × state)) (g : GlobalState) (threads bound : Nat)
    (hlas : las.Pairwise (fun l1 l2 => ∀ a, lisAccepts l1 a → ¬ lisAccepts l2 a))
    (hdisj : ∀ a ∈ addrs, ∀ la ∈ las, ¬ lisAccepts la a)
    (Hstart : ∀ [GooseGlobalGS .hasLC GF], receiptBound GF ≤ bound →
      ⊢ ([∗list] a ∈ addrs, addrUnset a) -∗ ([∗list] la ∈ las, lisUnset la) ={⊤}=∗
        ∃ Ps : Nat → IProp GF,
          ⌜∀ (i : Nat) (m : Expr × state), nodes[i]? = some m →
            DistBootWpGTT threads m.1 (Ps i)⌝ ∗
          [∗list] i ↦ _m ∈ nodes, Ps i) :
    DistDeploy addrs nodes g → Robust [] nodes g threads bound := by
  rintro ⟨Hnd, Hok, Hconns, -⟩ hfresh hig _ n κs c hsteps hn i tp σ hi e he
  simp only [List.map_nil, List.nil_append] at hfresh hsteps
  have H := goose_dist_adequacy_below (GF := GF) (n + 1) threads nodes g (fun _ v => v = #())
    (fun _ p h => intoVal_ne_PanicV () p h.symm) ⟨Hconns, hig.2.1, trivial⟩
    (fun _ _ => ⟨trivial, trivial, trivial⟩)
    ?_ n κs c hsteps (Nat.lt_succ_self n) (fun m hm => (hfresh m hm).2.2) i tp σ hi
  · exact ⟨H.2.1 e he, H.2.2 e he⟩
  · intro G HN
    iintro Hg
    ihave Hnet := netSha_globalStart g.globalWorld $$ Hg
    ihave ⟨Hs, Hl⟩ := addrs_lis_start (Gg := G) (extGlobal netExt g.globalWorld) addrs las Hnd Hok
      hlas hdisj $$ Hnet
    imod Hstart (by omega) $$ Hs Hl with ⟨%Ps, %HP, HPs⟩
    imodintro
    iapply BigSepL.bigSepL_mono ?_ $$ HPs
    intro j m hm
    exact nodeWp_of_distBootGTT threads threads (Nat.le_refl _) m.1 m.2 (Ps j)
      (hfresh m (List.mem_of_getElem? hm)) (HP j m hm)

/-- **The bridge over `netShaExts`, wildcard listeners, the thread bound and the main threads'
tokens**: `robust_of_distProtoLisRBT_sha` whose machines' programs also get their main thread's
token. -/
theorem robust_of_distProtoLisRBTT_sha [lctx : GoLocalContext] (addrs las : List GoString)
    (nodes : List (Expr × state)) (g : GlobalState) (threads bound : Nat)
    (hlas : las.Pairwise (fun l1 l2 => ∀ a, lisAccepts l1 a → ¬ lisAccepts l2 a))
    (hdisj : ∀ a ∈ addrs, ∀ la ∈ las, ¬ lisAccepts la a)
    (Hstart : ∀ [GooseGlobalGS .hasLC GF] [NetProtoGS], receiptBound GF ≤ bound →
      ⊢ regCtx -∗ ([∗list] a ∈ addrs, addrUnset a) -∗ ([∗list] la ∈ las, lisUnset la) ={⊤}=∗
        ∃ Ps : Nat → IProp GF,
          ⌜∀ (i : Nat) (m : Expr × state), nodes[i]? = some m →
            DistBootWpGTT threads m.1 (Ps i)⌝ ∗
          [∗list] i ↦ _m ∈ nodes, Ps i) :
    DistDeploy addrs nodes g → Robust [] nodes g threads bound := by
  refine robust_of_distBootLisRBTT_sha (GF := GF) addrs las nodes g threads bound hlas hdisj ?_
  intro G hb
  iintro Hs Hl
  imod netProto_alloc ⊤ with ⟨%π, #Hreg⟩
  iapply @Hstart G π hb $$ Hreg Hs Hl

end bridgeSha

end github_com.imdea_software.swiftpaxos
end Perennial
