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

end bridgeLis

end github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet
end Perennial
