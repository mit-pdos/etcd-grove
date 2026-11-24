/-
**The deployment bridge over wildcard listeners** (a local copy of `Net/Statement/DistBridge.lean`'s
`robust_of_distBootRB`/`robust_of_distProtoRB`; notes/dsv-epaxos.md, "Design finding (Net/remote):
the master's wildcard listener at the top level"). The master listens on the wildcard `":7501"`,
whose resource `lisUnset ":7501"` only `addrs_lis_start` (`GooseLang/Ext/Net/Proto.lean`) gives;
Net's bridge gives the addresses' (`addrs_start`). `robust_of_distProtoLisRB` is
`robust_of_distProtoRB` with `addrs_lis_start` in place of `addrs_start`: the start obligation also
gets the listeners `las` unset (pairwise disjoint, and disjoint from `addrs`). Proved from Net's
lemmas only; Net could offer it.
-/
module

public import Net.Statement.DistBridge

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Robustness Net

namespace github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet

attribute [local instance] netExts netExtsSemantics netExtsInterp netExts_hasNet
  GooseGlobalGS.gooseInvGS

section bridgeLis
variable [GoGlobalContext] {GF : BundledGFunctors} [hPre : GooseGpreS GF]

/-- `robust_of_distBootRB` with the listeners `las` unset too (`addrs_lis_start`). -/
theorem robust_of_distBootLisRB [lctx : GoLocalContext] (addrs las : List GoString)
    (nodes : List (Expr × state)) (g : GlobalState) (threads bound : Nat)
    (hlas : las.Pairwise (fun l1 l2 => ∀ a, lisAccepts l1 a → ¬ lisAccepts l2 a))
    (hdisj : ∀ a ∈ addrs, ∀ la ∈ las, ¬ lisAccepts la a)
    (Hstart : ∀ [GooseGlobalGS .hasLC GF], receiptBound GF ≤ bound →
      ⊢ ([∗list] a ∈ addrs, addrUnset a) -∗ ([∗list] la ∈ las, lisUnset la) ={⊤}=∗
        ∃ Ps : Nat → IProp GF,
          ⌜∀ (i : Nat) (m : Expr × state), nodes[i]? = some m → DistBootWpG m.1 (Ps i)⌝ ∗
          [∗list] i ↦ _m ∈ nodes, Ps i) :
    DistDeploy addrs nodes g → Robust [] nodes g threads bound := by
  rintro ⟨Hnd, Hok, Hconns, -⟩ hfresh _ _ n κs c hsteps hn i tp σ hi e he
  simp only [List.map_nil, List.nil_append] at hfresh hsteps
  have H := goose_dist_adequacy_below (GF := GF) (n + 1) threads nodes g (fun _ v => v = #())
    (fun _ p h => intoVal_ne_PanicV () p h.symm) ⟨Hconns, trivial⟩ (fun _ _ => ⟨trivial, trivial⟩)
    ?_ n κs c hsteps (Nat.lt_succ_self n) (fun m hm => (hfresh m hm).2.2) i tp σ hi
  · exact ⟨H.2.1 e he, H.2.2 e he⟩
  · intro G HN
    iintro Hg
    ihave Hnet := net_globalStart g.globalWorld $$ Hg
    ihave ⟨Hs, Hl⟩ := addrs_lis_start (Gg := G) (extGlobal netExt g.globalWorld) addrs las Hnd Hok
      hlas hdisj $$ Hnet
    imod Hstart (by omega) $$ Hs Hl with ⟨%Ps, %HP, HPs⟩
    imodintro
    iapply BigSepL.bigSepL_mono ?_ $$ HPs
    intro j m hm
    exact nodeWp_of_distBootG threads m.1 m.2 (Ps j) (hfresh m (List.mem_of_getElem? hm))
      (HP j m hm)

/-- **The bridge over wildcard listeners**: `robust_of_distProtoRB` with the listeners `las`
unset too (`addrs_lis_start`; `las` pairwise disjoint and disjoint from `addrs`). -/
theorem robust_of_distProtoLisRB [lctx : GoLocalContext] (addrs las : List GoString)
    (nodes : List (Expr × state)) (g : GlobalState) (threads bound : Nat)
    (hlas : las.Pairwise (fun l1 l2 => ∀ a, lisAccepts l1 a → ¬ lisAccepts l2 a))
    (hdisj : ∀ a ∈ addrs, ∀ la ∈ las, ¬ lisAccepts la a)
    (Hstart : ∀ [GooseGlobalGS .hasLC GF] [NetProtoGS], receiptBound GF ≤ bound →
      ⊢ regCtx -∗ ([∗list] a ∈ addrs, addrUnset a) -∗ ([∗list] la ∈ las, lisUnset la) ={⊤}=∗
        ∃ Ps : Nat → IProp GF,
          ⌜∀ (i : Nat) (m : Expr × state), nodes[i]? = some m → DistBootWpG m.1 (Ps i)⌝ ∗
          [∗list] i ↦ _m ∈ nodes, Ps i) :
    DistDeploy addrs nodes g → Robust [] nodes g threads bound := by
  refine robust_of_distBootLisRB (GF := GF) addrs las nodes g threads bound hlas hdisj ?_
  intro G hb
  iintro Hs Hl
  imod netProto_alloc ⊤ with ⟨%π, #Hreg⟩
  iapply @Hstart G π hb $$ Hreg Hs Hl

/-! ## With the thread bound (net/rpc's server)

Net's net/rpc server (`Server.ServeCodec.spec`, so `RpcHttpHyp`'s `HandleHTTP`/`Serve`) asks
`threadBound GF ≤ 2 ^ 31` (its wait group's counter is an `int32`). Perennial's
`goose_dist_adequacy_below` (perennial#690) takes the thread bound `T` along the execution at hand
(`DistCrashNstepsBelow [] T`, which is what `Robust`'s `threads` bounds) and gives each machine's
obligation (`nodeWpBody`) `threadBound GF = T`; the variants below keep that fact as
`threadBound GF ≤ threads`, independent of the step bound. (Until the pin of perennial#690 these
bridges used `goose_dist_adequacy`, whose thread bound is of every execution of `n` steps, so
`n + 2`, `DistThreadsBelow.of_single`: a kit serving net/rpc was covered for fewer than
`2 ^ 31 - 1` steps only.) -/

/-- `DistBootWpG` with the machine's thread bound at most `T`. -/
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

/-- `robust_of_distBootLisRB` with each machine's thread bound at most `threads`, `Robust`'s. -/
theorem robust_of_distBootLisRBT [lctx : GoLocalContext] (addrs las : List GoString)
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
  rintro ⟨Hnd, Hok, Hconns, -⟩ hfresh _ _ n κs c hsteps hn i tp σ hi e he
  simp only [List.map_nil, List.nil_append] at hfresh hsteps
  have H := goose_dist_adequacy_below (GF := GF) (n + 1) threads nodes g (fun _ v => v = #())
    (fun _ p h => intoVal_ne_PanicV () p h.symm) ⟨Hconns, trivial⟩ (fun _ _ => ⟨trivial, trivial⟩)
    ?_ n κs c hsteps (Nat.lt_succ_self n) (fun m hm => (hfresh m hm).2.2) i tp σ hi
  · exact ⟨H.2.1 e he, H.2.2 e he⟩
  · intro G HN
    iintro Hg
    ihave Hnet := net_globalStart g.globalWorld $$ Hg
    ihave ⟨Hs, Hl⟩ := addrs_lis_start (Gg := G) (extGlobal netExt g.globalWorld) addrs las Hnd Hok
      hlas hdisj $$ Hnet
    imod Hstart (by omega) $$ Hs Hl with ⟨%Ps, %HP, HPs⟩
    imodintro
    iapply BigSepL.bigSepL_mono ?_ $$ HPs
    intro j m hm
    exact nodeWp_of_distBootGT threads threads (Nat.le_refl _) m.1 m.2 (Ps j)
      (hfresh m (List.mem_of_getElem? hm)) (HP j m hm)

/-- **The bridge over wildcard listeners, with the thread bound**: `robust_of_distProtoLisRB`
whose machines' obligations also get `threadBound GF ≤ threads`, `Robust`'s. -/
theorem robust_of_distProtoLisRBT [lctx : GoLocalContext] (addrs las : List GoString)
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
  refine robust_of_distBootLisRBT (GF := GF) addrs las nodes g threads bound hlas hdisj ?_
  intro G hb
  iintro Hs Hl
  imod netProto_alloc ⊤ with ⟨%π, #Hreg⟩
  iapply @Hstart G π hb $$ Hreg Hs Hl

end bridgeLis

end github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet
end Perennial
