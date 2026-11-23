/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swiftnet/Start.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
`StartOk` (Spec/swiftnet/Interface.lean): the run's start (stage 2). From the network's start
resources of every address but the client nodes' request ports (the harness's): the
configuration's and the membership's mono lists (their writers' authorities to the orchestrator
and the master), the abstract state's ghost variable (half to the orchestrator, half to
`sp.alloc`), the rpc world of `services` (`net.rpc.rpcWorld_alloc`), the SwiftPaxos names,
invariant, shares and prediction tokens (`sp.alloc`); the plain addresses' protocols
(`addrs_set_proto` with `protoP`/`protoQ`) and the rpc addresses' (`net.rpc.rpcAddr_set`); every
node gets its addresses' tokens and `common γ`.
-/
module

public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.examples.swiftnet.Interface

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

/-- The client nodes' addresses with tokens in their shares (node address, configuration port),
node by node. -/
def startClAddrs : List GoString :=
  (List.range 6).flatMap (fun c => [clientNodeAddrs.getD c go!"", clientConfAddrs.getD c go!""])

/-- The server nodes' addresses, node by node. -/
def startSvAddrs : List GoString := (List.range 6).flatMap (fun i => nodeAddrs.getD (7 + i) [])

theorem start_filter_perm [GoGlobalContext] :
    (allAddrs.filter (fun a => a ∉ kit.reqAddrs)).Perm (plainAddrs ++ rpcAddrs) := by
  show (allAddrs.filter (fun a => a ∉ reqAddrs)).Perm (plainAddrs ++ rpcAddrs)
  decide

theorem start_nodes_perm :
    (plainAddrs ++ rpcAddrs).Perm (orchAddr :: startClAddrs ++ startSvAddrs) := by
  decide

/-- A big separating conjunction indexed by position only, over two lists of the same length. -/
theorem start_bigSepL_idx {A B : Type _} {PROP : Type _} [BI PROP] :
    ∀ (l1 : List A) (l2 : List B) (P : Nat → PROP), l1.length = l2.length →
    ([∗list] k ↦ _x ∈ l1, P k) ⊢ [∗list] k ↦ _y ∈ l2, P k
  | [], [], _, _ => .rfl
  | [], _ :: _, _, h => by simp at h
  | _ :: _, [], _, h => by simp at h
  | _ :: l1, _ :: l2, P, h => by
    have ih := start_bigSepL_idx l1 l2 (fun k => P (k + 1)) (by simpa using h)
    exact (BigSepL.bigSepL_cons (Φ := fun k (_ : A) => P k)).1.trans
      ((sep_mono .rfl ih).trans (BigSepL.bigSepL_cons (Φ := fun k (_ : B) => P k)).2)

/-- A big separating conjunction over `List.range n`, as one indexed by the positions of a list
of length `n`. -/
theorem start_bigSepL_range {B : Type _} {PROP : Type _} [BI PROP] (n : Nat) (l : List B)
    (P : Nat → PROP) (h : l.length = n) :
    ([∗list] x ∈ List.range n, P x) ⊢ [∗list] k ↦ _y ∈ l, P k := by
  refine (BigSepL.bigSepL_mono ?_).trans (start_bigSepL_idx (List.range n) l P (by simp [h]))
  intro k x hx
  obtain ⟨h1, h2⟩ := List.getElem?_eq_some_iff.mp hx
  rw [List.getElem_range] at h2
  subst h2
  exact .rfl

section start
variable [GoGlobalContext] [G : GooseGlobalGS .hasLC netDistGF] [π : NetProtoGS] [Perennial.github_com.imdea_software.swiftpaxos.sp.GobFmt]

instance start_rpcAddr_persistent (W : net.rpc.RpcWorld netDistGF) (a : GoString) :
    Persistent (net.rpc.rpcAddr (GF := netDistGF) W a) := by
  unfold net.rpc.rpcAddr; infer_instance

/-- Set the rpc protocols of a list of addresses (`net.rpc.rpcAddr_set`), keeping the tokens. -/
theorem start_rpcAddrs_set (W : net.rpc.RpcWorld netDistGF) :
    ∀ addrs : List GoString,
    ⊢ inv net.rpc.regN (net.rpc.regInv W) -∗
      ([∗list] a ∈ addrs, addrTok a ∗ addrUnset a) ==∗
      ([∗list] a ∈ addrs, addrTok a) ∗
      [∗list] a ∈ addrs, net.rpc.rpcAddr (GF := netDistGF) W a
  | [] => by
    iintro #_ -
    imodintro
    isplitl <;> iapply BigSepL.bigSepL_nil.2 <;> iempintro
  | a :: addrs => by
    iintro #Hinv Hs
    icases BigSepL.bigSepL_cons.1 $$ Hs with ⟨⟨Ht, Hu⟩, Hs⟩
    imod net.rpc.rpcAddr_set W a $$ Hu Hinv with #Hp
    imod start_rpcAddrs_set W addrs $$ Hinv Hs with ⟨Hts, #Hps⟩
    imodintro
    isplitl [Ht Hts]
    · iapply BigSepL.bigSepL_cons.2; iframe Ht Hts
    · iapply BigSepL.bigSepL_cons.2; iframe Hp Hps

instance start_common_persistent (γ : SwiftNames netDistGF) : Persistent (common γ) := by
  unfold common; infer_instance

/-- A persistent proposition, once per element of a list. -/
theorem start_bigSepL_dup {A : Type _} (P : IProp netDistGF) [Persistent P] (l : List A) :
    P ⊢ [∗list] _x ∈ l, P := by
  induction l with
  | nil => iintro -; iapply BigSepL.bigSepL_nil.2; iempintro
  | cons x l ih =>
    iintro #HP
    iapply BigSepL.bigSepL_cons.2
    iframe HP
    iapply ih $$ HP

/-- The client nodes' tokens, node by node. -/
theorem start_cl_toks :
    ([∗list] a ∈ startClAddrs, addrTok a) ⊢
      [∗list] c ∈ List.range 6, addrTok (clientNodeAddrs.getD c go!"") ∗
        addrTok (clientConfAddrs.getD c go!"") := by
  unfold startClAddrs
  rw [BigSepL.bigSepL_flatMap]
  refine BigSepL.bigSepL_mono_of_forall ?_
  intro k x
  iintro ⟨H1, H2, -⟩
  iframe H1 H2

/-- The servers' halves of `serverShare`'s middle part, node by node. -/
theorem start_sv_parts (γsp : sp.Names) (Hm : IProp netDistGF) :
    Hm ∗ ([∗list] k ∈ List.range 5, sp.replicaStart γsp k) ∗
      ([∗list] k ∈ List.range 5, sp.predTok γsp (sp.PNode.rep k)) ⊢
    [∗list] i ∈ List.range 6, (if i = 0 then Hm
      else sp.replicaStart γsp (i - 1) ∗ sp.predTok γsp (sp.PNode.rep (i - 1))) := by
  iintro ⟨Hm, Hr, Hp⟩
  rw [show List.range 6 = 0 :: (List.range 5).map Nat.succ from rfl]
  iapply (BigSepL.bigSepL_cons (Φ := fun _ (i : Nat) => if i = 0 then Hm
      else iprop(sp.replicaStart γsp (i - 1) ∗ sp.predTok γsp (sp.PNode.rep (i - 1))))).2
  simp only [↓reduceIte]
  iframe Hm
  rw [BigSepL.bigSepL_map]
  ihave Hrp := BigSepL.bigSepL_sep_eqv.2 $$ [Hr Hp]
  · iframe Hr Hp
  iapply BigSepL.bigSepL_mono_of_forall ?_ $$ Hrp
  intro k x
  simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.succ_sub_one]
  exact .rfl

/-- `StartOk`: the run's start (see the file header). -/
theorem start_proof : StartOk := by
  unfold StartOk
  rw [swiftNetCfg_addrs]
  iintro Hs
  imod mono_list_own_alloc (GF := netDistGF) ([] : List Conf) with ⟨%γc, Hc, -⟩
  imod mono_list_own_alloc (GF := netDistGF) ([] : List (List GoString)) with ⟨%γm, Hm, -⟩
  imod ghostVar_alloc (GF := netDistGF) ([] : List (GoString × GoString)) with ⟨%γl, Hl⟩
  icases (ghostVar_split_half γl 1 _).1 $$ Hl with ⟨Hl1, Hl2⟩
  imod sp.alloc γc γm γl $$ Hl2 with ⟨%γsp, #Hinv, Hcl, Hreps, Hpt⟩
  imod net.rpc.rpcWorld_alloc (services γc γm) with ⟨%W, %HW, #Hreg⟩
  let γ : SwiftNames netDistGF := ⟨γc, γm, W, γsp, γl⟩
  ihave Hs := (BigSepL.bigSepL_perm start_filter_perm).1 $$ Hs
  icases BigSepL.bigSepL_append.1 $$ Hs with ⟨Hp, Hr⟩
  imod addrs_set_proto (protoP γ) (protoQ γ) plainAddrs $$ Hp with ⟨Htp, #Hpp⟩
  imod start_rpcAddrs_set W rpcAddrs $$ Hreg Hr with ⟨Htr, #Hpr⟩
  ihave #Hcommon : common γ $$ []
  · unfold common
    iframe Hpp Hpr Hinv
    ipureintro; exact HW
  ihave Hts : [∗list] a ∈ plainAddrs ++ rpcAddrs, addrTok a $$ [Htp Htr]
  · iapply BigSepL.bigSepL_append.2
    iframe Htp Htr
  ihave Hts := (BigSepL.bigSepL_perm start_nodes_perm).1 $$ Hts
  icases BigSepL.bigSepL_append.1 $$ Hts with ⟨Htc, Hts⟩
  icases (BigSepL.bigSepL_cons (Φ := fun _ a => addrTok a)).1 $$ Htc with ⟨H0, Htc⟩
  ihave Htc := start_cl_toks $$ Htc
  unfold startSvAddrs
  rw [BigSepL.bigSepL_flatMap]
  -- the clients' parts
  ihave Hcs := sp.clientsStart_split $$ Hcl
  unfold sp.allPNodes
  icases BigSepL.bigSepL_append.1 $$ Hpt with ⟨Hptc, Hptr⟩
  rw [BigSepL.bigSepL_map, BigSepL.bigSepL_map]
  ihave Hcd := start_bigSepL_dup (common γ) (List.range 6) $$ Hcommon
  ihave Hsd := start_bigSepL_dup (common γ) (List.range 6) $$ Hcommon
  ihave Hsv := start_sv_parts γsp (mem.writer γ) $$ [Hm Hreps Hptr]
  · iframe Hreps Hptr
    unfold mem.writer; iexact Hm
  imodintro
  iexists γ
  isplitl [H0 Hc Hl1]
  · unfold orchShare
    iframe Hcommon
    isplitl [H0]
    · unfold orchAddr; iexact H0
    isplitl [Hc]
    · unfold conf.writer; iexact Hc
    unfold lin.own linOwn
    iexists []
    iframe Hl1
    ipureintro; rfl
  isplitl [Htc Hcs Hptc Hcd]
  · iapply start_bigSepL_range 6 clientNodes (fun c => clientNodeShare γ c) (by rfl)
    ihave H := BigSepL.bigSepL_sep_eqv.2 $$ [Htc Hcs]
    · iframe Htc Hcs
    ihave H := BigSepL.bigSepL_sep_eqv.2 $$ [H Hptc]
    · iframe H Hptc
    ihave H := BigSepL.bigSepL_sep_eqv.2 $$ [H Hcd]
    · iframe H Hcd
    iapply BigSepL.bigSepL_mono_of_forall ?_ $$ H
    intro k x
    unfold clientNodeShare
    iintro ⟨⟨⟨⟨H1, H2⟩, H3⟩, H4⟩, H5⟩
    iframe H1 H2 H3 H4 H5
  · iapply start_bigSepL_range 6 serverNodes (fun i => serverShare γ i) (by rfl)
    ihave H := BigSepL.bigSepL_sep_eqv.2 $$ [Hts Hsv]
    · iframe Hts Hsv
    ihave H := BigSepL.bigSepL_sep_eqv.2 $$ [H Hsd]
    · iframe H Hsd
    iapply BigSepL.bigSepL_mono_of_forall ?_ $$ H
    intro k x
    unfold serverShare
    iintro ⟨⟨H1, H2⟩, H3⟩
    iframe H1 H2 H3

/-- `StartOk` (stage 2's name). -/
theorem start_ok' : StartOk := start_proof

end start

end Perennial.github_com.imdea_software.swiftpaxos
