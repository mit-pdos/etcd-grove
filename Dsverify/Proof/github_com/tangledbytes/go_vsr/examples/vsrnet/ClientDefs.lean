/-
A client machine's system (`kit.go`'s `Sys`, notes/dsv-vr.md): what `mkClient` makes and every
`Op` takes and gives back, `sysRes γ c sys n` (client `c`'s go-vsr client, id `c + 1`, its `*TCP`,
the flags, the ghost layer's invariants and request counter `n`), and a reply's bound.

Ported from dsverify-lab `examples/vr/proof/VsrProof/Top/{Defs,ClGhost}.lean`, simplified: remote's
`Serve` calls `op` one call at a time, threading the system's resource `tok sys` from one call to the
next (`svcOp`), so the client's resources need no invariant and token swap (the lab's `clInv`,
`cl_acquire`, `cl_release`: its harness's `isSys` was persistent); `sysRes` holds them, and the
whole request counter `nextReq γ (c + 1) n`.

* `reply_short`: a valid reply's result is shorter than 2^16 bytes (the store's values are
  registered puts' values, `InputBounded`), so the output `Op` returns is a `KOut`
  (`ghost_reply_short`).
-/
module

public import Dsverify.Proof.github_com.tangledbytes.go_vsr.examples.vsrnet.OrchProofDefs
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Spec.client
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Spec.network

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net
open VsrModel VsrGhost

namespace github_com.tangledbytes.go_vsr.examples.vsrnet

/-! ## A valid reply is short -/

section pure
variable [GooseExts]

theorem storeOf_snoc' (l : List Entry) (e : Entry) :
    storeOf (l ++ [e]) = (handle (storeOf l) e.op).1 := by
  simp [storeOf, List.foldl_append]

theorem handle_ok' (m : VsrModel.Store) {i : KvInput GoString GoString} (hi : InputOk i) :
    handle m (encOp i) = svcStep m i := by
  apply handle_encOp
  cases i with
  | get k => exact hi.1
  | put k v => exact ⟨hi.1.1, hi.2.2.1⟩

/-- A registered entry's input is well formed and bounded. -/
theorem reg_ok {s : VsrModel.Sys} (h : Inv s) {e : Entry} {l : List Entry} (hl : Registered s l)
    (he : e ∈ l) : ∃ i, e.op = encOp i ∧ InputOk i ∧ InputBounded i := by
  obtain ⟨i, hi, hop⟩ := hl e he
  obtain ⟨-, -, -, -, -, -, -, -, -, -, h11, -⟩ := h
  obtain ⟨hok, -, -, -, -, hb⟩ := h11 _ _ _ hi
  exact ⟨i, hop, hok, hb⟩

/-- The store after registered entries has short values. -/
theorem foldl_bnd {s : VsrModel.Sys} (h : Inv s) :
    ∀ (l : List Entry) (m : VsrModel.Store), Registered s l → StBnd m →
      StBnd (l.foldl (fun m e => (handle m e.op).1) m) := by
  intro l
  induction l with
  | nil => intro m _ hm; exact hm
  | cons e l ih =>
    intro m hl hm
    rw [List.foldl_cons]
    apply ih _ (fun x hx => hl x (List.mem_cons_of_mem _ hx))
    obtain ⟨i, hop, hok, hb⟩ := reg_ok h hl (List.mem_cons_self)
    rw [hop, handle_ok' _ hok]
    cases i with
    | get k => exact hm
    | put k v =>
      intro k' w hw
      simp only [svcStep] at hw
      split at hw
      · cases hw; exact hb.2
      · exact hm _ _ hw

theorem storeOf_bnd {s : VsrModel.Sys} (h : Inv s) (l : List Entry) (hl : Registered s l) :
    StBnd (storeOf l) :=
  foldl_bnd h l _ hl (fun _ _ hv => by simp at hv)

/-- **A valid reply's result is short.** -/
theorem reply_short {s : VsrModel.Sys} (h : Inv s) {id cid v : Nat} {res : GoString}
    (hm : MsgValid s (.reply id cid v res)) : res.length < 2 ^ 16 := by
  obtain ⟨j, e, hj, -, -, hres⟩ := hm
  have hreg : Registered s s.lin := by
    obtain ⟨-, -, -, -, -, -, -, -, -, h10, -, -⟩ := h; exact h10
  subst hres
  unfold outOf
  rw [hj]
  dsimp only
  obtain ⟨i, hop, hok, hb⟩ := reg_ok h hreg (List.mem_of_getElem? hj)
  rw [hop, handle_ok' _ hok]
  cases i with
  | put k w => exact hb.2
  | get k =>
    simp only [svcStep]
    have hst := storeOf_bnd h (s.lin.take j) (fun x hx => hreg x (List.mem_of_mem_take hx))
    cases hk : storeOf (s.lin.take j) k with
    | none => simp
    | some w => exact hst k w hk

end pure

section ghost
attribute [local instance] GooseGlobalGS.gooseInvGS
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [G : GooseGlobalGS .hasLC GF]

/-- A reply the system made is short (`reply_short`). -/
theorem ghost_reply_short (γ : Names) (E : CoPset) (hE : ↑sysN ⊆ E) (id cid v : Nat)
    (res : GoString) :
    sysInv (GF := GF) γ -∗ fact γ (.msg (.reply id cid v res)) ={E}=∗ ⌜res.length < 2 ^ 16⌝ := by
  have H : ∀ s, VsrModel.Inv s → (∀ f ∈ [Fact.msg (.reply id cid v res)], Holds s f) →
      res.length < 2 ^ 16 :=
    fun s h hfs => reply_short (id := id) (cid := cid) (v := v) h (hfs _ (List.mem_singleton_self _))
  iintro #Hs #Hf
  iapply ghost_pure γ E hE [.msg (.reply id cid v res)] (res.length < 2 ^ 16) H $$ Hs
  iapply BigSepL.bigSepL_cons.2
  isplitl []
  · iexact Hf
  · iapply BigSepL.bigSepL_nil.2; iempintro

end ghost

/-! ## The system's resource -/

/-- Client machine `c`'s go-vsr address (its `*TCP`'s: machine `1 + c`'s, `Addrs()[1 + c]`). -/
abbrev meC (c : Nat) : GoString := VsrWire.addrs.getD (1 + c) go!""

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [package_sem' : github_com.tangledbytes.go_vsr.examples.vsrnet.Assumptions]
variable [π : NetProtoGS]
variable [encoding.json.DecoderRep GF]

/-- **Client machine `c`'s system** `sys`, its request counter at `n` (exclusive; `Op` takes it and
gives it back): the boxed `*Sys` `x`, its `*TCP` (at `meC c`) and go-vsr client (id `c + 1`, in
state `cst`), the flags, the counter `nextReq γ (c + 1) n`, the ghost layer's invariants and the
number of replicas' fact (what registering a request needs), the client's invariant: unless it gave
up, nothing pending and its request number one below the counter. -/
def sysRes (γ : Names) (c : Nat) (sys : GoInterface) (n : Nat) : IProp GF :=
  iprop(∃ (x tcp vc : Loc) (st gu : Bool) (cst : pkg.client.St) (N : Nat),
    ⌜sys = interface.mkOk (go.GoType.PointerType Sys.ty) #x⌝ ∗
    x ↦ Sys.mk tcp vc (W64 (c : Int)) st gu ∗
    pkg.network.isTCP tcp γ (meC c) ∗ pkg.client.isClient vc γ (c + 1) cst ∗
    nextReq (G := hG.goose_globalGS) γ (c + 1) n ∗ sysInv (G := hG.goose_globalGS) γ ∗
    regInv (G := hG.goose_globalGS) γ ∗ fact (G := hG.goose_globalGS) γ (.size N) ∗
    ⌜1 ≤ n ∧ (gu = false → cst.pend = none ∧ cst.n + 1 = n)⌝)

end defs

end github_com.tangledbytes.go_vsr.examples.vsrnet
end Perennial
