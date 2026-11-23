/-
**The deployment bridge with wildcard listeners** (kit-local; notes/dsv-quepaxa.md, "the start"):
`Net/Statement/DistBridge.lean`'s `robust_of_distBootRB`/`robust_of_distProtoRB`, whose start
obligation gets, beside the listed addresses unset (`addrUnset`), every address each listener of
a list `las` takes unset (`lisUnset`, from `GooseLang/Ext/Net/Proto.lean`'s `addrs_lis_start`),
when no two of the listeners take an address in common and none takes a listed address.

QuePaxa's proxies and recorders listen at wildcards (`0.0.0.0:76xx`, D21): their protocols are set
by `lis_set_proto` from `lisUnset`, which `Net/`'s bridge does not give (it gives the listed
addresses' `addrUnset` only, `addrs_start`). This file proves the variant from `Net/`'s public
lemmas (`goose_dist_adequacy`, `net_globalStart`, `addrs_lis_start`, `netProto_alloc`,
`nodeWp_of_distBootG`), the proof of `robust_of_distBootRB` with `addrs_lis_start` in place of
`addrs_start`. **Design finding**: `Net/` should offer it (`robust_of_distProtoLisRB`); with
`las = []` it is `robust_of_distProtoRB` (`lisUnset` of no listener is `emp`).

It imports no proof module (defs tier).
-/
module

public import Net.Statement.DistBridge

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

namespace raxos.examples.quepaxanet

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Robustness Net

attribute [local instance] netExts netExtsSemantics netExtsInterp netExts_hasNet
attribute [local instance] GooseGlobalGS.gooseInvGS

section bridgeLis
variable [GoGlobalContext] {GF : BundledGFunctors} [hPre : GooseGpreS GF]

/-- `robust_of_distBootRB` with listeners: the obligation gets the listed addresses unset and,
for each listener of `las`, the addresses it takes unset (`lisUnset`), if no two listeners take
an address in common (`hlas`) and none takes a listed address (`hdisj`). -/
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

/-- **`robust_of_distProtoRB` with listeners**: the library's ghost state made first
(`netProto_alloc`); the obligation gets the registry, the listed addresses unset and the
listeners' addresses unset, and sets their protocols itself (`addrs_set_proto`,
`lis_set_proto`). -/
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

end raxos.examples.quepaxanet
end Perennial
