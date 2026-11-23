/-
**The deployment bridge over wildcard listeners**: dsv-epaxos's `examples/epaxosnet/Bridge.lean`
(origin/dsv-epaxos 6d2224f420), copied verbatim into this kit's namespace (a local copy of
`Net/Statement/DistBridge.lean`'s `robust_of_distBootRB`/`robust_of_distProtoRB`; Upamanyu (#24)
asked that it move to `Net/Statement/DistBridge.lean`, beside quepaxa's). The gryff kit's servers
listen at seven wildcards (`":7501"`, `":7502".."7504"`, `":8502".."8504"`), whose resources
`lisUnset` only `addrs_lis_start` (`GooseLang/Ext/Net/Proto.lean`) gives; Net's bridge gives the
listed addresses' (`addrs_start`). `robust_of_distProtoLisRB(T)` is `robust_of_distProtoRB` with
`addrs_lis_start` in place of `addrs_start`: the start obligation also gets the listeners `las`
unset (pairwise disjoint, and disjoint from `addrs`); the `T` variants keep each machine's thread
bound (`threadBound GF ≤ bound + 1`, which Net's net/rpc server needs). Proved from Net's lemmas
only.
-/
module

public import Net.Statement.DistBridge

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Robustness Net

namespace gryff.examples.gryffnet

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
  have H := goose_dist_adequacy (GF := GF) (n + 1) (n + 2) nodes g (fun _ v => v = #())
    (fun _ p h => intoVal_ne_PanicV () p h.symm) ⟨Hconns, trivial⟩ (fun _ _ => ⟨trivial, trivial⟩)
    ?_ n κs c (distNsteps_of_crash_nil hsteps.nsteps) (Nat.lt_succ_self n)
    (fun m hm => (hfresh m hm).2.2) (DistThreadsBelow.of_single ?_) i tp σ hi
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
    exact nodeWp_of_distBootG (n + 2) m.1 m.2 (Ps j) (hfresh m (List.mem_of_getElem? hm))
      (HP j m hm)
  · intro j tp' σ' hj
    simp only [distInit, List.getElem?_map] at hj
    obtain ⟨x, hx, hx'⟩ := Option.map_eq_some_iff.mp hj
    simp only [Prod.mk.injEq] at hx'
    obtain ⟨-, rfl⟩ := hx'
    exact (hfresh x (List.mem_of_getElem? hx)).2.2

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
`threadBound GF ≤ 2 ^ 31` (its wait group's counter is an `int32`). `goose_dist_adequacy`'s node
obligation (`nodeWpBody`) has `threadBound GF = n + 2` for an execution of `n < bound` steps, which
`nodeWp_of_distBootG` drops; the variants below keep it as `threadBound GF ≤ bound + 1`. (The
statement's `threads`, the live threads of the execution, would be the better bound; Perennial's
`goose_dist_adequacy` takes its thread bound as `DistThreadsBelow`, of every execution, not of the
one at hand, so it is not used here.) -/

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

/-- `robust_of_distBootLisRB` with each machine's thread bound at most `bound + 1`. -/
theorem robust_of_distBootLisRBT [lctx : GoLocalContext] (addrs las : List GoString)
    (nodes : List (Expr × state)) (g : GlobalState) (threads bound : Nat)
    (hlas : las.Pairwise (fun l1 l2 => ∀ a, lisAccepts l1 a → ¬ lisAccepts l2 a))
    (hdisj : ∀ a ∈ addrs, ∀ la ∈ las, ¬ lisAccepts la a)
    (Hstart : ∀ [GooseGlobalGS .hasLC GF], receiptBound GF ≤ bound →
      ⊢ ([∗list] a ∈ addrs, addrUnset a) -∗ ([∗list] la ∈ las, lisUnset la) ={⊤}=∗
        ∃ Ps : Nat → IProp GF,
          ⌜∀ (i : Nat) (m : Expr × state), nodes[i]? = some m →
            DistBootWpGT (bound + 1) m.1 (Ps i)⌝ ∗
          [∗list] i ↦ _m ∈ nodes, Ps i) :
    DistDeploy addrs nodes g → Robust [] nodes g threads bound := by
  rintro ⟨Hnd, Hok, Hconns, -⟩ hfresh _ _ n κs c hsteps hn i tp σ hi e he
  simp only [List.map_nil, List.nil_append] at hfresh hsteps
  have H := goose_dist_adequacy (GF := GF) (n + 1) (n + 2) nodes g (fun _ v => v = #())
    (fun _ p h => intoVal_ne_PanicV () p h.symm) ⟨Hconns, trivial⟩ (fun _ _ => ⟨trivial, trivial⟩)
    ?_ n κs c (distNsteps_of_crash_nil hsteps.nsteps) (Nat.lt_succ_self n)
    (fun m hm => (hfresh m hm).2.2) (DistThreadsBelow.of_single ?_) i tp σ hi
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
    exact nodeWp_of_distBootGT (n + 2) (bound + 1) (by omega) m.1 m.2 (Ps j)
      (hfresh m (List.mem_of_getElem? hm)) (HP j m hm)
  · intro j tp' σ' hj
    simp only [distInit, List.getElem?_map] at hj
    obtain ⟨x, hx, hx'⟩ := Option.map_eq_some_iff.mp hj
    simp only [Prod.mk.injEq] at hx'
    obtain ⟨-, rfl⟩ := hx'
    exact (hfresh x (List.mem_of_getElem? hx)).2.2

/-- **The bridge over wildcard listeners, with the thread bound**: `robust_of_distProtoLisRB`
whose machines' obligations also get `threadBound GF ≤ bound + 1`. -/
theorem robust_of_distProtoLisRBT [lctx : GoLocalContext] (addrs las : List GoString)
    (nodes : List (Expr × state)) (g : GlobalState) (threads bound : Nat)
    (hlas : las.Pairwise (fun l1 l2 => ∀ a, lisAccepts l1 a → ¬ lisAccepts l2 a))
    (hdisj : ∀ a ∈ addrs, ∀ la ∈ las, ¬ lisAccepts la a)
    (Hstart : ∀ [GooseGlobalGS .hasLC GF] [NetProtoGS], receiptBound GF ≤ bound →
      ⊢ regCtx -∗ ([∗list] a ∈ addrs, addrUnset a) -∗ ([∗list] la ∈ las, lisUnset la) ={⊤}=∗
        ∃ Ps : Nat → IProp GF,
          ⌜∀ (i : Nat) (m : Expr × state), nodes[i]? = some m →
            DistBootWpGT (bound + 1) m.1 (Ps i)⌝ ∗
          [∗list] i ↦ _m ∈ nodes, Ps i) :
    DistDeploy addrs nodes g → Robust [] nodes g threads bound := by
  refine robust_of_distBootLisRBT (GF := GF) addrs las nodes g threads bound hlas hdisj ?_
  intro G hb
  iintro Hs Hl
  imod netProto_alloc ⊤ with ⟨%π, #Hreg⟩
  iapply @Hstart G π hb $$ Hreg Hs Hl

end bridgeLis

end gryff.examples.gryffnet
end Perennial
